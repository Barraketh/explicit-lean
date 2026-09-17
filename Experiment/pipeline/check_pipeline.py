#!/usr/bin/env python3
"""Check the replay pipeline: renderer unit tests, then one real module.

    python3 -B Experiment/pipeline/check_pipeline.py

Two parts:

* **Renderer unit tests** over `test/Pipeline/renderer_cases.json`, hand-written
  fixtures covering every step kind and every field the spec defines, plus the
  malformed shapes the renderer must refuse by name. The fixtures are written
  from `tracking/SIMP-TRACE-SPEC.md`, not from recorder output: where the
  recorder deviates, the spec is what the renderer implements and the deviation
  is reported rather than absorbed.
* **One end-to-end run** of the harness on `Mathlib/Logic/Nontrivial/Defs.lean`,
  asserting the report's structure — not its replay counts, which are the
  measurement the harness exists to produce and would make this check a
  tautology.

Site detection is also checked against the six modules' known site counts, since
a drift there would silently misattribute every trace in a module.

Exit 0 when everything passes, 1 otherwise.
"""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))

import render as R  # noqa: E402
import replay_module as P  # noqa: E402
import sites as S  # noqa: E402

CASES = ROOT / "test" / "Pipeline" / "renderer_cases.json"

# Site counts per module, cross-checked against T1's own `check_transcription.py`
# output. Detection drift would misalign every trace in the affected module.
EXPECTED_SITES = {
    "Logic/IsEmpty/Basic.lean": 17,
    "Logic/Nontrivial/Defs.lean": 1,
    "Logic/Function/Defs.lean": 2,
    "Logic/ExistsUnique.lean": 8,
    "Logic/Function/Basic.lean": 23,
    "Logic/Basic.lean": 31,
}

DEFAULT_T1 = pathlib.Path(
    "/Users/ptsier/projects/explicit-lean-worktrees/T1-trace-capture"
)
DEFAULT_T2 = pathlib.Path(
    "/Users/ptsier/projects/explicit-lean-worktrees/T2-explicit-rw"
)


class Failures:
    def __init__(self) -> None:
        self.items: list[str] = []
        self.passed = 0

    def check(self, name: str, condition: bool, detail: str = "") -> None:
        if condition:
            self.passed += 1
        else:
            self.items.append(f"{name}: {detail}")

    def equal(self, name: str, got: object, want: object) -> None:
        self.check(name, got == want, f"got {got!r}, want {want!r}")


def render_tests(f: Failures) -> None:
    cases = json.loads(CASES.read_text(encoding="utf-8"))

    for case in cases["steps"]:
        try:
            f.equal("step/" + case["name"], R.render_step(case["step"]), case["expect"])
        except R.RenderError as exc:
            f.check("step/" + case["name"], False, f"raised {exc}")

    for case in cases["step_errors"]:
        try:
            got = R.render_step(case["step"])
            f.check("step_error/" + case["name"], False,
                    f"rendered {got!r} instead of refusing")
        except R.RenderError as exc:
            f.equal("step_error/" + case["name"] + "/reason", exc.reason, case["error"])
            f.equal("step_error/" + case["name"] + "/side", exc.side, case["side"])

    for case in cases["closes"]:
        try:
            f.equal("close/" + case["name"], R.render_close(case["close"]),
                    case["expect"])
        except R.RenderError as exc:
            f.check("close/" + case["name"], False, f"raised {exc}")

    for case in cases["close_errors"]:
        try:
            got = R.render_close(case["close"])
            f.check("close_error/" + case["name"], False,
                    f"rendered {got!r} instead of refusing")
        except R.RenderError as exc:
            f.equal("close_error/" + case["name"], exc.reason, case["error"])

    for case in cases["traces"]:
        try:
            bodies, _ = R.render_trace(case["trace"])
            f.equal("trace/" + case["name"], bodies, case["expect"])
        except R.RenderError as exc:
            f.check("trace/" + case["name"], False, f"raised {exc}")

    for case in cases["trace_errors"]:
        try:
            R.render_trace(case["trace"])
            f.check("trace_error/" + case["name"], False, "did not refuse")
        except R.RenderError as exc:
            f.equal("trace_error/" + case["name"], exc.reason, case["error"])

    for case in cases["unresolved"]:
        f.equal("unresolved/" + case["name"],
                R.unresolved_reason(case["trace"]), case["expect"])

    for case in cases["inaccessible"]:
        indices: list[int] = []
        for loc in case["trace"]["locations"]:
            R.collect_inaccessible(loc.get("steps") or [], indices)
        f.equal("inaccessible/" + case["name"], sorted(indices), case["expect"])

    # Every spec step kind must have a positive fixture, or a kind could be
    # added to the spec and silently never exercised.
    covered = {c["step"]["kind"] for c in cases["steps"]}
    for kind in R.KNOWN_KINDS:
        if kind == "intro_ctx":
            continue  # covered by a negative case: it is unimplemented by design
        f.check(f"coverage/{kind}", kind in covered,
                "no positive fixture for this spec step kind")


def layout_tests(f: Failures) -> None:
    """Rendering must preserve indentation and stay inside the line budget."""
    steps = [f"lemma_with_a_long_name_{i} at [0, 1, {i}]" for i in range(8)]
    lines = S.wrap_step_list("explicit_rw [", steps, "]", "  ", "    ")
    f.check("layout/breaks_long_list", len(lines) > 1,
            "an 8-step list at 100 columns was not broken")
    f.check("layout/first_line_indent", lines[0].startswith("  explicit_rw ["),
            f"first line is {lines[0]!r}")
    f.check("layout/continuations_indent_deeper",
            all(line.startswith("    ") for line in lines[1:]),
            "a continuation line does not indent deeper than the tactic block")
    f.check("layout/within_budget", not S.overlong(lines),
            f"lines over {S.MAX_LINE} chars: {S.overlong(lines)}")

    short = S.wrap_step_list("explicit_rw [", ["foo at []"], "]", "  ", "    ")
    f.equal("layout/short_stays_one_line", short, ["  explicit_rw [foo at []]"])

    # An unbreakable single step is reported, not silently wrapped.
    huge = ["x" * 140 + " at []"]
    lines = S.wrap_step_list("explicit_rw [", huge, "]", "  ", "    ")
    f.check("layout/unbreakable_reported", bool(S.overlong(lines)),
            "an unbreakable overlong step was not reported")

    # Determinism: the same trace renders to the same text every time.
    trace = json.loads(CASES.read_text(encoding="utf-8"))["traces"][0]["trace"]
    f.equal("layout/deterministic",
            R.render_trace(trace)[0], R.render_trace(trace)[0])


def splice_tests(f: Failures) -> None:
    source = "import A\nimport B\n\ntheorem t : True := by\n  simp only [foo]\n"
    found = S.find_sites(source)
    f.equal("splice/one_site", len(found), 1)
    f.equal("splice/site_text", found[0].text, "simp only [foo]")
    f.equal("splice/column", found[0].column, 2)
    f.check("splice/alone_on_line", found[0].alone_on_line, "site not alone on line")

    out = S.splice(source, {0: ["  -- Original simp:", "  -- simp only [foo]",
                               "  explicit_rw [foo at []]"]}, found)
    f.check("splice/indentation_preserved",
            "\n  -- Original simp:\n  -- simp only [foo]\n  explicit_rw [foo at []]\n"
            in out, f"spliced text is {out!r}")

    withimport = S.add_import(out)
    f.check("splice/import_after_imports",
            "import B\nimport ExplicitLean.ExplicitRw\n" in withimport,
            f"import block is {withimport.splitlines()[:4]}")

    # A mid-line site must refuse a multi-line replacement rather than emit
    # source that does not parse.
    mid = "import A\n\ntheorem t : True := by\n  ext a; simp only [foo]\n"
    midsites = S.find_sites(mid)
    f.equal("splice/midline_detected", midsites[0].alone_on_line, False)
    try:
        S.splice(mid, {0: ["a", "b"]}, midsites)
        f.check("splice/midline_refuses_multiline", False, "did not refuse")
    except ValueError:
        f.passed += 1

    # Public-import spelling is followed, as Mathlib's module system uses it.
    pub = "module\n\npublic import Mathlib.Order.Defs\n\ntheorem t : True := trivial\n"
    f.check("splice/public_import_spelling",
            "public import ExplicitLean.ExplicitRw" in S.add_import(pub),
            "the new import did not follow the `public import` spelling")


def diagnostic_tests(f: Failures) -> None:
    """Diagnostic parsing, and the attribution that reads it.

    A real `lake env lean` transcript: two errors at the same position, the
    first with a multi-line body. The header pattern must not match inside that
    body — `[^:]` matches a newline, so an unanchored file group finds a
    spurious header several lines down and truncates the body it was supposed
    to capture, which is what made every such failure attribute to `harness`.
    """
    text = (
        "/tmp/M.lean:553:21: error: explicit_rw: step 1: Application type mismatch: "
        "The argument\n  h\nhas type\n  A\nbut is expected to have type\n  ¬?m.11\n"
        "in the application\n  eq_false h\n"
        "/tmp/M.lean:553:21: error: explicit_rw: step 2: position [0, 1] rewrites "
        "the domain of a dependent `∀`.\n"
    )
    matches = list(P.DIAG_RE.finditer(text))
    f.equal("diag/two_errors", len(matches), 2)
    if len(matches) == 2:
        f.equal("diag/second_header_line", matches[1].group("line"), "553")
        body = text[matches[0].start("msg") : matches[1].start()]
        f.check("diag/body_spans_to_next_header", "eq_false h" in body,
                f"body was cut to {body!r}")

    f.equal("diag/warnings_are_not_errors",
            [m.group("sev") for m in P.DIAG_RE.finditer(
                "/tmp/M.lean:1:1: warning: unused\n")],
            ["warning"])

    # Attribution reads the body, and each family lands on the right side.
    for message, side in (
        ("explicit_rw: step 2: lemma `foo` does not match the subterm at position [1].",
         "t1"),
        ("explicit_rw: step 1: `unfold Ne` was applied where the head constant is `Iff`.",
         "t1"),
        ("unknown free variable '_uniq.42'", "t1"),
        ("Unknown identifier 'a✝'", "t1"),
        ("explicit_rw: step 1: `intro_ctx` is not implemented", "t2"),
        ("unexpected token '=='; expected ')'", "t1"),
        ("explicit_rw: step 2: lemma `eq_true foo` does not match the subterm at "
         "position [1]. Expected ∀ (f : ?m.3), P f but the subterm is P g", "t1"),
        ("explicit_rw: step 1: Application type mismatch: The argument h has type A "
         "but is expected to have type ¬?m.11 in the application eq_false h", "t1"),
    ):
        got, why = P.attribute({}, message)
        f.equal("attribute/" + message[:34], got, side)
        f.check("attribute/justified/" + message[:24], bool(why), "no justification")

    # The two `prop` families must be told apart, since they are different T1
    # defects with different fixes.
    quantified = P.attribute({}, (
        "lemma `eq_true foo` does not match the subterm at position [1]. "
        "Expected ∀ (f : ?m.3), P f but the subterm is P g"))[1]
    mismatched = P.attribute({}, (
        "Application type mismatch: The argument h has type A but is expected to "
        "have type ¬?m.11 in the application eq_false h"))[1]
    f.check("attribute/prop_families_differ", quantified != mismatched,
            "the two prop defects share one justification")
    f.check("attribute/quantified_names_args", "args" in quantified,
            f"justification does not name the missing field: {quantified!r}")


def invocation_tests(f: Failures) -> None:
    """A site whose call runs once per branch cannot take one tactic.

    The recorder writes one JSON per invocation, so a call under `<;>` or inside
    an alternation leaves several traces sharing one `occurrence`. Identical
    ones are a repeated compile and collapse to one; differing ones are real
    branches, and replacing the call with any single branch's steps would be
    wrong in the others.
    """
    site = S.Site(index=0, start=0, end=10, text="simp [*]", line=1, column=2,
                  alone_on_line=True, trailing="")
    trace = {
        "schema": "simp-trace-v1", "module": "M", "occurrence": "1",
        "locations": [{"loc": "goal", "pre": "a", "post": None,
                       "steps": [{"kind": "rw", "pos": [], "name": "foo",
                                  "dir": "fwd"}],
                       "close": {"by": "rfl"}}],
    }
    single = P.render_site(site, dict(trace))
    f.equal("invocations/single_renders", single["status"], "rendered")

    several = P.render_site(site, {**trace, "_invocations": 3})
    f.equal("invocations/several_refuse", several["status"],
            "render_failed:multiple_invocations")
    f.check("invocations/refusal_counts_them", "3" in several["detail"],
            f"detail does not name the count: {several['detail']!r}")
    f.check("invocations/original_kept",
            any(site.text in line for line in several["lines"]),
            "the original call was not kept")
    f.check("invocations/marker_emitted",
            any("explicit_rw: unresolved" in line for line in several["lines"]),
            "no marker comment was emitted")


def site_count_tests(f: Failures, t1: pathlib.Path) -> None:
    mathlib = t1 / ".lake" / "packages" / "mathlib" / "Mathlib"
    if not mathlib.is_dir():
        f.check("sites/mathlib_present", False, f"not found: {mathlib}")
        return
    for rel, expected in EXPECTED_SITES.items():
        path = mathlib / rel
        if not path.is_file():
            f.check(f"sites/{rel}", False, "source missing")
            continue
        f.equal(f"sites/{rel}", len(S.find_sites(path.read_text(encoding="utf-8"))),
                expected)


def end_to_end_test(f: Failures, t1: pathlib.Path, t2: pathlib.Path) -> None:
    """Run the harness on one small module and assert the report's structure."""
    with tempfile.TemporaryDirectory(prefix="pipeline-check-") as tmp:
        out = pathlib.Path(tmp)
        code = P.main([
            "--module", "Mathlib/Logic/Nontrivial/Defs.lean",
            "--t1", str(t1), "--t2", str(t2), "--out", str(out),
        ])
        f.equal("e2e/exit", code, 0)

        report_path = out / "report.json"
        summary_path = out / "summary.md"
        f.check("e2e/report_exists", report_path.is_file(), "report.json missing")
        f.check("e2e/summary_exists", summary_path.is_file(), "summary.md missing")
        if not report_path.is_file():
            return
        report = json.loads(report_path.read_text(encoding="utf-8"))

        for key in ("generated", "t1_commit", "t2_commit", "t1_branch", "t2_branch",
                    "modules", "seconds", "t1_dirty_after", "t2_dirty_after"):
            f.check(f"e2e/report_has_{key}", key in report, "missing key")
        f.check("e2e/t1_commit_is_a_hash", len(report.get("t1_commit", "")) >= 7,
                f"got {report.get('t1_commit')!r}")
        f.check("e2e/t2_commit_is_a_hash", len(report.get("t2_commit", "")) >= 7,
                f"got {report.get('t2_commit')!r}")
        f.equal("e2e/one_module", len(report["modules"]), 1)

        mod = report["modules"][0]
        for key in ("module", "sites", "compile_mode", "records", "seconds",
                    "trace_count", "transcription"):
            f.check(f"e2e/module_has_{key}", key in mod, "missing key")
        f.equal("e2e/module_sites", mod["sites"], 1)
        f.check("e2e/compile_mode",
                mod["compile_mode"] in ("whole_module", "per_site"),
                f"got {mod['compile_mode']!r}")
        f.equal("e2e/one_record", len(mod["records"]), 1)

        rec = mod["records"][0]
        for key in ("site", "line", "column", "original", "status"):
            f.check(f"e2e/record_has_{key}", key in rec, "missing key")
        f.check("e2e/status_is_in_the_enumeration",
                P.bucket(rec["status"]) in P.STATUS_ORDER,
                f"status {rec['status']!r} is outside the enumeration")
        if rec["status"] != "replayed":
            f.check("e2e/failure_is_attributed",
                    rec.get("attribution") in ("t1", "t2", "harness"),
                    f"attribution {rec.get('attribution')!r}")
            f.check("e2e/failure_has_a_justification",
                    bool(rec.get("detail") or rec.get("error")),
                    "no detail or error text")
        f.check("e2e/original_preserved",
                rec["original"].startswith(("simp", "dsimp")),
                f"original is {rec['original']!r}")

        # The translated module was written and carries the new import.
        translated = out / "Mathlib" / "Logic" / "Nontrivial" / "Defs.lean"
        f.check("e2e/translated_written", translated.is_file(), "not written")
        if translated.is_file():
            text = translated.read_text(encoding="utf-8")
            f.check("e2e/import_added", "import ExplicitLean.ExplicitRw" in text,
                    "the ExplicitRw import is missing")
            f.check("e2e/original_kept_as_comment",
                    "-- Original simp:" in text or rec["status"] != "replayed",
                    "a replayed site did not keep its original call as a comment")

        # The driven worktrees stayed clean of anything this harness did.
        f.equal("e2e/t1_unchanged", report["t1_dirty_after"], report["t1_dirty"])
        f.equal("e2e/t2_unchanged", report["t2_dirty_after"], report["t2_dirty"])

        summary = summary_path.read_text(encoding="utf-8")
        f.check("e2e/summary_has_totals", "**total**" in summary,
                "summary has no totals row")
        f.check("e2e/summary_names_commits",
                report["t1_commit"][:7] in summary and report["t2_commit"][:7] in summary,
                "summary does not name both commits")


def main() -> int:
    t1 = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_T1
    t2 = pathlib.Path(sys.argv[2]) if len(sys.argv) > 2 else DEFAULT_T2

    f = Failures()
    render_tests(f)
    layout_tests(f)
    splice_tests(f)
    diagnostic_tests(f)
    invocation_tests(f)
    site_count_tests(f, t1)
    end_to_end_test(f, t1, t2)

    if f.items:
        print(f"\nFAIL: {len(f.items)} of {f.passed + len(f.items)} checks",
              file=sys.stderr)
        for item in f.items:
            print(f"  {item}", file=sys.stderr)
        return 1
    print(f"OK: {f.passed} checks")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
