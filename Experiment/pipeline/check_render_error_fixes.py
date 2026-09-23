#!/usr/bin/env python3
"""Focused regressions for structural refusal and explicit_rw layout."""

from __future__ import annotations

import hashlib
import pathlib
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import replay_module as P  # noqa: E402
import sites as S  # noqa: E402
import tactic_syntax_ast as TSA  # noqa: E402


def trace(name: str, invocation: int = 0, invocations: int = 1,
          close: dict | None = None) -> dict:
    return {
        "schema": "simp-trace-v1",
        "module": "Fixture",
        "occurrence": "1",
        "invocation": invocation,
        "invocations": invocations,
        "locations": [{
            "loc": "goal",
            "pre": "True",
            "post": None,
            "steps": [{"kind": "rw", "pos": [], "name": name}],
            "close": close,
        }],
    }


def rendered(source: str, records: list[dict] | dict,
             include_original_comment: bool = True) -> dict:
    sites = S.find_sites(source)
    assert len(sites) == 1, f"expected one source site, got {len(sites)}"
    syntax = None
    if isinstance(records, list) and len(records) > 1:
        with tempfile.TemporaryDirectory(prefix="render-error-syntax-") as temp:
            path = pathlib.Path(temp) / "Fixture.lean"
            source_bytes = source.encode("utf-8")
            path.write_bytes(source_bytes)
            syntax = TSA.extract_tactic_ancestries(
                module="Mathlib.RenderErrorFixture",
                source_path=path,
                sites=[{
                    "start_char": sites[0].start,
                    "end_char": sites[0].end,
                    "expected_text": sites[0].text,
                }],
                expected_source_sha256=hashlib.sha256(source_bytes).hexdigest(),
                require_pinned_path=False,
            )[0]
    return P.render_site(sites[0], records, source,
                         include_original_comment=include_original_comment,
                         syntax_ancestry=syntax, module_sites=sites)


def main() -> int:
    # Only a Lean parser-authenticated `<;>` ancestry may expand an invocation
    # list. It establishes the source order of generated goals.
    branch_source = "example : True := by\n  by_cases h : True <;> simp\n"
    branch_records = [trace("first", 0, 2), trace("second", 1, 2)]
    branch = rendered(branch_source, branch_records)
    assert branch["status"] == "rendered", branch
    assert branch["structural_leaf_count"] == 2, branch
    assert sum(line.lstrip().startswith("·") for line in branch["lines"]) == 2, branch
    branch_text = "\n".join(branch["lines"])
    assert branch_text.index("first at []") < branch_text.index("second at []"), branch_text
    assert any("-- simp" in line for line in branch["lines"]), branch["lines"]

    # The false flag must suppress source comments in the structural path too.
    uncommented = rendered(branch_source, branch_records,
                           include_original_comment=False)
    assert uncommented["status"] == "rendered", uncommented
    assert not any("Original simp" in line for line in uncommented["lines"]), (
        uncommented["lines"]
    )
    inline_branch = rendered(
        "example : True := by by_cases h : True <;> simp\n",
        branch_records,
        include_original_comment=False,
    )
    assert inline_branch["status"] == "rendered", inline_branch
    assert "by_cases h : True" in "\n".join(inline_branch["lines"]), inline_branch["lines"]
    assert not any("Original simp" in line for line in inline_branch["lines"]), (
        inline_branch["lines"]
    )

    # Nested declarations and multi-line tactic blocks are parsed structurally;
    # text-only operator lookalikes still have no authenticated ancestry.
    nested_proof = rendered(
        "example (b : Bool) : True := by\n"
        "  have h : True := by cases b <;> simp\n  exact h\n",
        branch_records,
    )
    assert nested_proof["status"] == "rendered", nested_proof
    assert all(line.startswith("    ") for line in nested_proof["lines"]), nested_proof["lines"]
    multiline_proof = rendered(
        "example (b : Bool) : True := by\n"
        "  have h : True :=\n"
        "    by\n"
        "      cases b <;>\n"
        "        simp\n"
        "  exact h\n",
        branch_records,
    )
    assert multiline_proof["status"] == "rendered", multiline_proof
    fail_closed = [
        (
            "string lookalike",
            'example : True := by\n  have s : String := "<;> by_cases h : P"\n  simp\n',
        ),
        (
            "comment lookalike",
            "example : True := by\n  /- by_cases h : P <;> -/\n  simp\n",
        ),
    ]
    for name, source in fail_closed:
        result = rendered(source, branch_records)
        assert result["status"] == "structurally_refused", (name, result)

    manual_source = "example : True := by\n" + "  simp\n" * 6
    manual_sites = S.find_sites(manual_source)
    assert len(manual_sites) == 6, manual_sites
    manual = P.render_site(
        manual_sites[5], {"schema": "simp-trace-v1", "modulePath":
                          "Mathlib/Logic/Function/Basic.lean"},
        manual_source, include_original_comment=False,
    )
    assert manual["status"] == "rendered", manual
    assert not any("Original simp" in line for line in manual["lines"]), manual

    # The single-invocation path must also separate the final empty location
    # path's closer from explicit_rw's outer step-list bracket.
    one = rendered(
        "example : True := by\n  simp\n",
        trace("eq_self", close=None),
    )
    assert one["status"] == "rendered", one
    output = "\n".join(one["lines"])
    assert "eq_self at [] ]" in output, output
    assert "eq_self at []]" not in output, output

    # A hypothesis close is rendered as an `at h` rewrite followed by the
    # exact recorded ordinary goal closer, and the source-splice formatter
    # keeps both tactics in the generated proof.
    hyp_close_source = (
        "example (P : Prop) (h : P) (hFalse : P = False) : False := by\n"
        "  simp at h\n"
    )
    hyp_close_trace = {
        "schema": "simp-trace-v1",
        "module": "Fixture",
        "occurrence": "1",
        "invocation": 0,
        "invocations": 1,
        "locations": [{
            "loc": {"hyp": "h"},
            "pre": "P",
            "post": "False",
            "steps": [{"kind": "rw", "pos": [], "name": "hFalse", "dir": "fwd"}],
            "close": {"by": "absurd:h"},
        }],
    }
    hyp_close = rendered(hyp_close_source, hyp_close_trace)
    assert hyp_close["status"] == "rendered", hyp_close
    assert hyp_close["lines"][-1] == (
        "  explicit_rw [hFalse at [] ] at h; explicit_rw [] then close [h.elim]"
    ), hyp_close["lines"]

    # A semicolon continuation is outside the extracted `<;>` branch range.
    unsupported = rendered(
        "example : True := by\n  cases x <;> simp; rfl\n",
        branch_records,
    )
    assert unsupported["status"] == "structurally_refused", unsupported

    # Ordinals, not input container order, determine the ordered mapping.
    reversed_records = rendered(
        branch_source,
        [trace("second", 1, 2), trace("first", 0, 2)],
    )
    ordered_text = "\n".join(reversed_records["lines"])
    assert ordered_text.index("first at []") < ordered_text.index("second at []"), (
        ordered_text
    )

    # The finalized trace must authenticate a complete, unique ordinal range.
    malformed = rendered(
        branch_source,
        [trace("first", 0, 2), trace("second", 0, 2)],
    )
    assert malformed["status"] == "structurally_refused", malformed
    malformed_total = rendered(
        branch_source,
        trace("only", 0, True),
    )
    assert malformed_total["status"] == "render_failed:bad_invocations", malformed_total

    # A sibling source target cannot be swallowed by the splice. An enclosing
    # alternative is likewise outside the parsed branch-spine grammar.
    nested_source = "example : True := by\n  simp <;> simp\n"
    nested_sites = S.find_sites(nested_source)
    assert len(nested_sites) == 2, nested_sites
    nested = P.render_site(
        nested_sites[1], [trace("first", 0, 2), trace("second", 1, 2)],
        nested_source,
    )
    assert nested["status"] == "structurally_refused", nested
    alternative = rendered(
        "example : True := by\n  first | cases x <;> simp\n",
        branch_records,
    )
    assert alternative["status"] == "structurally_refused", alternative

    print(f"passed {len(fail_closed) + 12} focused renderer regressions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
