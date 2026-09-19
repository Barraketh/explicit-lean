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
import simp_engine_inventory as I  # noqa: E402
import broader_overlay as B  # noqa: E402

CASES = ROOT / "test" / "Pipeline" / "renderer_cases.json"

# Site counts per module, cross-checked against T1's own `check_transcription.py`
# output. Detection drift would misalign every trace in the affected module.
EXPECTED_SITES = {
    "Data/Option/Basic.lean": 7,
    "Logic/IsEmpty/Basic.lean": 17,
    "Logic/Nontrivial/Defs.lean": 1,
    "Logic/Function/Defs.lean": 2,
    "Logic/ExistsUnique.lean": 8,
    "Logic/Function/Basic.lean": 25,
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

    # Attributes do not hide executable tactics on the same line, while the
    # term-level Meta API remains excluded.
    attributed = "@[simp] lemma t : True := by simp\n"
    f.equal("sites/attribute_with_tactic", len(S.find_sites(attributed)), 1)
    multiline_attribute = "@[simp,\n  foo]\nlemma t : True := by simp\n"
    f.equal("sites/multiline_attribute_with_tactic", len(S.find_sites(multiline_attribute)), 1)
    api = "example : True := withTraceNode `x <| simp True\n"
    f.equal("sites/meta_api_excluded", len(S.find_sites(api)), 0)

    # A top-level term ascription belongs outside the replacement range.
    ascribed = "example : Nat := (by simp : Nat)\n"
    ascribed_sites = S.find_sites(ascribed)
    f.equal("sites/ascription_count", len(ascribed_sites), 1)
    if ascribed_sites:
        f.equal("sites/ascription_call", ascribed_sites[0].text, "simp")
        f.check("sites/ascription_preserved", ascribed[ascribed_sites[0].end :].startswith(" : Nat"),
                "the type ascription was swallowed")

    # A retained mid-line call gets a standalone marker above its enclosing
    # line; splice must accept that two-line replacement.
    marked = "example : True := by\n  first | rfl <;> simp [foo]\n"
    marked_sites = S.find_sites(marked)
    if marked_sites:
        replacement = P.render_site(marked_sites[0], {
            "schema": "simp-trace-v1", "module": "M", "occurrence": "1",
            "invocations": 2, "locations": [],
        })
        out = S.splice(marked, {0: replacement["lines"]}, marked_sites)
        f.check("splice/midline_marker_standalone",
                "-- explicit_rw: unresolved" in out and "<;> simp [foo]" in out,
                f"marker or original missing: {out!r}")
    else:
        f.check("splice/midline_marker_site", False, "mid-line fixture was not detected")

    # The pipeline's guard is independent of renderer behaviour: forged
    # replacement text must not be eligible for replay.
    forged = {"status": "rendered", "lines": ["explicit_rw [foo at []]; simp"]}
    f.check("lint/replacement_block", bool(P.lint_replacement(forged)),
            "forbidden simp-family token was not found in replacement")

    # All edits, including zero-width markers, use original coordinates. Two
    # retained mid-line calls on one source line must each keep a recognizable
    # marker, and a replayed neighbor must not be shifted or mangled.
    same_line = "  exact foo <;> simp [foo] <;> simp [bar]\n"
    same_sites = S.find_sites(same_line)
    retained = [
        ["  -- explicit_rw: unresolved: branch one", "  simp [foo]"],
        ["  -- explicit_rw: unresolved: branch two", "  simp [bar]"],
    ]
    same_out = S.splice(same_line, {0: retained[0], 1: retained[1]}, same_sites)
    f.equal("splice/same_line_two_markers",
            same_out.count("-- explicit_rw: unresolved:"), 2)
    f.check("splice/same_line_originals_intact",
            "exact foo <;> simp [foo] <;> simp [bar]" in same_out,
            f"same-line retained calls were corrupted: {same_out!r}")

    mixed = "  exact foo <;> simp [foo] <;> simp [bar]\n"
    mixed_sites = S.find_sites(mixed)
    mixed_out = S.splice(mixed, {
        0: ["explicit_rw [foo at []]"],
        1: ["  -- explicit_rw: unresolved: retained", "  simp [bar]"],
    }, mixed_sites)
    f.check("splice/same_line_mixed_site",
            "explicit_rw [foo at []]" in mixed_out
            and "-- explicit_rw: unresolved: retained" in mixed_out
            and "simp [bar]" in mixed_out,
            f"mixed same-line edits were corrupted: {mixed_out!r}")

    unicode = "  λx => exact foo <;> simp [foo] <;> simp [bar]\n"
    unicode_sites = S.find_sites(unicode)
    unicode_out = S.splice(unicode, {0: retained[0], 1: retained[1]}, unicode_sites)
    f.check("splice/unicode_before_sites",
            "λx => exact foo <;> simp [foo] <;> simp [bar]" in unicode_out
            and unicode_out.count("-- explicit_rw: unresolved:") == 2,
            f"Unicode offset handling failed: {unicode_out!r}")


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
    """Structural expansion fixtures for the four observed branch families."""
    def source(prefix: str, call: str = "simp [h]", suffix: str = "") -> str:
        return "import A\nexample : True := by\n  " + prefix + " <;> " + call + suffix + "\n"

    def traces(count: int, names: list[str] | None = None) -> list[dict]:
        names = names or ["foo"] * count
        return [{
            "schema": "simp-trace-v1", "module": "M", "occurrence": "1",
            "invocation": i, "invocations": count,
            "locations": [{"loc": "goal", "pre": "a", "post": None,
                           "steps": [{"kind": "rw", "pos": [], "name": names[i]}],
                           "close": {"by": "rfl"}}],
        } for i in range(count)]

    def expanded(name: str, prefix: str, count: int, suffix: str = "",
                 names: list[str] | None = None) -> dict:
        text = source(prefix, suffix=suffix)
        site = S.find_sites(text)[0]
        return P.render_site(site, traces(count, names), text)

    one = expanded("A", "by_cases h : True", 2, names=["true_step", "false_step"])
    f.equal("invocations/group_A_replayed", one["status"], "rendered")
    f.equal("invocations/group_A_leaf_count", one["structural_leaf_count"], 2)
    f.check("invocations/group_A_order", "true_step" in one["lines"][3]
            and "false_step" in one["lines"][4], "ordinal order was not preserved")
    f.check("invocations/comment_adjacent", one["lines"][2].startswith("  by_cases")
            and one["lines"][1] == "  -- simp [h]", "original comment is not adjacent")

    b = expanded("B", "rcases h with rfl | hne", 2)
    f.equal("invocations/group_B_leaf_count", b["structural_leaf_count"], 2)
    f.check("invocations/group_B_bullets", sum(line.lstrip().startswith("·")
            for line in b["lines"]) == 2, "rcases did not produce two leaves")

    c = expanded("C", "obtain rfl | ha := eq_or_ne x y <;> obtain rfl | ha' := eq_or_ne a b", 4)
    f.equal("invocations/group_C_leaf_count", c["structural_leaf_count"], 4)
    f.check("invocations/group_C_nested", sum("obtain rfl | ha'" in line for line in c["lines"]) == 2,
            "nested obtain spine was not expanded")

    d = expanded("D", "by_cases hp : P <;> by_cases hq : Q", 4,
                 names=["p_q", "p_nq", "np_q", "np_nq"])
    f.equal("invocations/group_D_leaf_count", d["structural_leaf_count"], 4)
    f.check("invocations/group_D_order", all(name in "\n".join(d["lines"])
            for name in ("p_q", "p_nq", "np_q", "np_nq")), "nested by_cases traces missing")

    non_tail = expanded("non_tail", "by_cases h : a == b", 2,
                        suffix=" <;> simpa [I.eq_iff] using h")
    f.equal("invocations/non_tail_continuation_rewritten", non_tail["status"], "rendered")
    f.equal("invocations/non_tail_original_comments",
            sum("-- Original continuation: simpa [I.eq_iff] using h" in line
                for line in non_tail["lines"]), 2)
    f.check("invocations/non_tail_has_ordinary_closes",
            any("exact congrArg f (beq_iff_eq.mp h)" in line for line in non_tail["lines"])
            and any("exact fun hab => h (beq_iff_eq.mpr ((I.eq_iff).mp hab))" in line
                     for line in non_tail["lines"]),
            "branch-specific ordinary continuation was not emitted")
    f.check("invocations/non_tail_no_generated_simp_family",
            not P.lint_replacement(non_tail),
            "non-tail continuation still contains a generated simp-family call")

    refused_suffix = expanded("unsupported_suffix", "by_cases h : True", 2,
                              suffix=" <;> simpa using h")
    f.equal("invocations/unsupported_simp_suffix_refused",
            refused_suffix["status"], "structurally_refused")

    identical = expanded("identical", "by_cases h : True", 2, names=["same", "same"])
    f.equal("invocations/identical_step_lists_keep_leaves", identical["structural_leaf_count"], 2)
    f.equal("invocations/identical_step_lists_occurrences", "\n".join(identical["lines"]).count("same at []"), 2)

    base = source("by_cases h : True")
    site = S.find_sites(base)[0]
    for name, records in (("missing", traces(2)[:1]),
                          ("duplicate", traces(2)[:1] + [dict(traces(2)[0])]),
                          ("gapped", [dict(traces(2)[0], invocation=0),
                                      dict(traces(2)[1], invocation=2)])):
        refused = P.render_site(site, records, base)
        f.equal("invocations/malformed_" + name, refused["status"], "structurally_refused")
        f.check("invocations/malformed_" + name + "/original",
                any(site.text in line for line in refused["lines"]), "original call was not retained")

    # A legacy aggregate does not carry the complete records and is refused.
    legacy = P.render_site(site, {"schema": "simp-trace-v1", "invocations": 2,
                                  "locations": []}, base)
    f.equal("invocations/legacy_aggregate_refused", legacy["status"], "structurally_refused")


def mapping_tests(f: Failures) -> None:
    source = "import A\n\nexample : True := by\n  simp [foo]\n"
    site_list = S.find_sites(source)
    rec = P.render_site(site_list[0], {
        "schema": "simp-trace-v1", "module": "M", "occurrence": "1",
        "locations": [{"loc": "goal", "pre": "True", "post": None,
                       "steps": [{"kind": "rw", "pos": [], "name": "foo"}],
                       "close": {"by": "rfl"}}],
    })
    start, end = P.replacement_line_range(source, site_list, [rec], 0)
    probe = pathlib.Path("/tmp/probe.lean")
    diagnostics = [
        {"file": "/tmp/header.lean", "line": 1, "column": 1, "message": "header", "body": "header"},
        {"file": "/tmp/probe.lean", "line": start, "column": 1, "message": "site", "body": "site"},
    ]
    f.equal("diag/in_block_selected",
            P.diagnostic_for_probe(diagnostics, probe, start, end)["message"], "site")
    f.check("diag/out_of_block_is_inconclusive",
            P.diagnostic_for_probe([diagnostics[0]], probe, start, end) is None,
            "an unrelated diagnostic was selected")


def manual_override_tests(f: Failures) -> None:
    """The cone's source overlays enter the real replay splice path."""
    mathlib = ROOT / ".lake" / "packages" / "mathlib"
    expected = {
        "Mathlib/Logic/Function/Basic.lean": {
            "bcd40e80cbe2ffe1": 1,
        },
    }
    for module, expected_ids in expected.items():
        source = (mathlib / module).read_text(encoding="utf-8")
        site_list = S.find_sites(source)
        selected = P.manual_overrides_for_sites(module, source, site_list)
        f.equal("manual/sites/" + module, len(selected), len(expected_ids))
        observed_ids = {entry["occurrence"] for entry in selected.values()}
        f.equal("manual/identities/" + module, observed_ids, set(expected_ids))
        records = [
            P.render_manual_override(site, selected[site.index], source)
            for site in site_list if site.index in selected
        ]
        translated = P.build_module(source, site_list, records)
        for record in records:
            occurrence = record["manual_override"]
            f.equal("manual/status/" + occurrence, record["status"], "rendered")
            f.check("manual/comment/" + occurrence,
                    "-- Original simp:" in translated
                    and record["original"] in translated,
                    "original simp call was not retained as an adjacent comment")
            f.check("manual/lint/" + occurrence,
                    not P.lint_replacement(record),
                    "manual replacement contains a forbidden simp-family token")
        f.check("manual/import/" + module,
                "import ExplicitLean.ExplicitRw" in translated,
                "manual replay did not use the normal ExplicitRw import path")


def broader_overlay_tests(f: Failures) -> None:
    """The broader-family overlay is authenticated and fail-closed."""
    mathlib = ROOT / ".lake" / "packages" / "mathlib"
    source_path = mathlib / "Mathlib" / "Logic" / "Basic.lean"
    if not source_path.is_file():
        f.check("broader/source_present", False, f"not found: {source_path}")
        return
    source = source_path.read_bytes()
    metadata, entries = B.load_database()
    selected = [entry for entry in entries if entry["module"] == "Mathlib/Logic/Basic.lean"]
    f.equal("broader/entry_count", len(selected), 14)
    f.equal("broader/top_level_has_no_shared_source_hash", "moduleSourceSha256" in metadata, False)
    f.check("broader/entry_hashes_are_source_hashes",
            all(entry["moduleSourceSha256"] == B._sha256(source) for entry in selected),
            "an entry does not carry the exact Logic.Basic source hash")
    f.check("broader/deterministic_ids",
            all(entry["occurrence"] == I.occurrence_id(
                entry["module"], entry["startByte"], entry["endByte"]
            ) for entry in selected),
            "an accepted occurrence uses a free-form label")
    source_text = source.decode("utf-8")
    rendered, used = B.apply_to_rendered(
        "Mathlib/Logic/Basic.lean", source, source_text,
        [(len(source_text[:site.start].encode("utf-8")),
          len(source_text[:site.end].encode("utf-8")))
         for site in S.find_sites(source_text)],
    )
    f.equal("broader/all_entries_used", used, [entry["occurrence"] for entry in selected])
    f.equal("broader/comments", rendered.count("-- Original broader simp-family call/declaration:"), 14)
    f.check("broader/metadata_entries_unresolved",
            "@[grind =] theorem xor_def" in source_text
            and "grind_pattern Exists.choose_spec => P.choose" in source_text
            and all("xor_def" not in entry["source"] and "grind_pattern" not in entry["source"]
                    for entry in selected),
            "metadata-only declarations were silently accepted by the overlay")
    f.check("broader/replacements_linted",
            not any(P.lint_replacement({"lines": [entry["replacement"]]})
                    for entry in selected),
            "overlay replacement contains a forbidden executable token")
    try:
        B.apply_to_rendered("Mathlib/Logic/Basic.lean", source, source.decode("utf-8"),
                            [(selected[0]["startByte"], selected[0]["endByte"])])
        f.check("broader/protected_overlap", False, "overlap was accepted")
    except RuntimeError:
        f.passed += 1
    missing = source.decode("utf-8").replace(selected[0]["source"], "shifted", 1)
    try:
        B.apply_to_rendered("Mathlib/Logic/Basic.lean", source, missing)
        f.check("broader/missing_entry", False, "missing rendered entry was accepted")
    except RuntimeError:
        f.passed += 1
    duplicate = source.decode("utf-8") + "\n" + selected[0]["source"]
    try:
        B.apply_to_rendered("Mathlib/Logic/Basic.lean", source, duplicate)
        f.check("broader/duplicate_entry", False, "duplicate rendered entry was accepted")
    except RuntimeError:
        f.passed += 1

    # Synthetic entries authenticate each module independently.  In particular,
    # a second module must not inherit the first module's source digest.
    with tempfile.TemporaryDirectory(prefix="broader-overlay-fixture-") as tmp:
        db_path = pathlib.Path(tmp) / "overlay.json"
        a_module = "Mathlib/SyntheticA.lean"
        b_module = "Mathlib/SyntheticB.lean"
        a_source = b"  first\n    grind foo\n      continuation\n"
        b_source = "-- λ before\n\tgrind bar\n".encode("utf-8")
        a_start = a_source.index(b"grind foo")
        b_start = b_source.index(b"grind bar")
        fixture_entries = [
            {
                "module": a_module, "moduleSourceSha256": B._sha256(a_source),
                "occurrence": I.occurrence_id(
                    a_module, a_start, a_start + len(b"grind foo\n      continuation")
                ),
                "startByte": a_start,
                "endByte": a_start + len(b"grind foo\n      continuation"),
                "source": "grind foo\n      continuation",
                "replacement": "rfl\n  exact True.intro",
            },
            {
                "module": b_module, "moduleSourceSha256": B._sha256(b_source),
                "occurrence": I.occurrence_id(
                    b_module, b_start, b_start + len(b"grind bar")
                ),
                "startByte": b_start, "endByte": b_start + len(b"grind bar"),
                "source": "grind bar", "replacement": "rfl",
            },
        ]
        fixture = {
            "kind": B.KIND, "schema": B.SCHEMA,
            "mathlibCommit": B.EXPECTED_MATHLIB_COMMIT,
            "lean": {"version": B.EXPECTED_LEAN_VERSION, "commit": B.EXPECTED_LEAN_COMMIT},
            "overrides": fixture_entries,
        }
        db_path.write_text(json.dumps(fixture), encoding="utf-8")
        _, loaded = B.load_database(db_path)
        f.equal("broader/two_module_fixture", len(loaded), 2)
        a_out, _ = B.apply_to_rendered(a_module, a_source, a_source.decode(), path=db_path)
        b_out, _ = B.apply_to_rendered(b_module, b_source, b_source.decode(), path=db_path)
        f.check("broader/independent_hashes", a_out.endswith("    rfl\n      exact True.intro\n") and b_out.endswith("\trfl\n"),
                f"indented fixture layout was not preserved: {a_out!r} / {b_out!r}")
        expected_a = (
            "  first\n    -- Original broader simp-family call/declaration:\n"
            "    -- grind foo\n    --       continuation\n    rfl\n"
            "      exact True.intro\n"
        )
        expected_b = (
            "-- λ before\n\t-- Original broader simp-family call/declaration:\n"
            "\t-- grind bar\n\trfl\n"
        )
        f.equal("broader/comment_line_fidelity_a", a_out, expected_a)
        f.equal("broader/comment_line_fidelity_b", b_out, expected_b)

        def rejected_fixture(name: str, mutate: object) -> None:
            value = json.loads(db_path.read_text(encoding="utf-8"))
            mutate(value)
            bad = pathlib.Path(tmp) / (name + ".json")
            bad.write_text(json.dumps(value), encoding="utf-8")
            try:
                B.load_database(bad)
            except RuntimeError:
                f.passed += 1
            else:
                f.check("broader/reject/" + name, False, "forged fixture was accepted")

        rejected_fixture("wrong_mathlib_identity", lambda value: value.__setitem__(
            "mathlibCommit", "a" * 40))
        rejected_fixture("wrong_lean_version", lambda value: value["lean"].__setitem__(
            "version", "4.32.1"))
        rejected_fixture("wrong_lean_commit", lambda value: value["lean"].__setitem__(
            "commit", "b" * 40))
        rejected_fixture("mismatched_occurrence_id", lambda value: value["overrides"][0].__setitem__(
            "occurrence", "free-form-t57-label"))

        wrong_hash = json.loads(db_path.read_text(encoding="utf-8"))
        wrong_hash["overrides"][1]["moduleSourceSha256"] = "c" * 64
        wrong_hash_path = pathlib.Path(tmp) / "wrong-entry-hash.json"
        wrong_hash_path.write_text(json.dumps(wrong_hash), encoding="utf-8")
        try:
            B.apply_to_rendered(b_module, b_source, b_source.decode(), path=wrong_hash_path)
        except RuntimeError as error:
            f.check("broader/reject/entry_source_hash", "source hash changed" in str(error), str(error))
        else:
            f.check("broader/reject/entry_source_hash", False, "a forged entry source hash was accepted")

        split = json.loads(db_path.read_text(encoding="utf-8"))
        split_entry = split["overrides"][1]
        split_start = b_source.index("λ".encode("utf-8")) + 1
        split_entry["startByte"] = split_start
        split_entry["endByte"] = split_start + 2
        split_entry["occurrence"] = I.occurrence_id(
            b_module, split_entry["startByte"], split_entry["endByte"])
        split_path = pathlib.Path(tmp) / "split.json"
        split_path.write_text(json.dumps(split), encoding="utf-8")
        split_source = b_source
        try:
            B.apply_to_rendered(b_module, split_source, split_source.decode(), path=split_path)
        except RuntimeError as error:
            f.check("broader/reject/utf8_split", "splits UTF-8" in str(error), str(error))
        else:
            f.check("broader/reject/utf8_split", False, "a range split a code point")


def derivation_tests(f: Failures) -> None:
    """T19's term-free theorem derivation contract and refusal fixtures."""
    def step(op: str = "direct_eq", *, source: str | None = "simp-argument",
             source_arg: int | None = 0, pos: list[int] | None = None,
             redex: list[int] | None = None, extra: int = 0,
             binders: list[dict] | None = None, discharge: list[dict] | None = None,
             side: list[dict] | None = None, name: str = "lemma",
             args: list[str] | None = None, direction: str = "fwd",
             prop: str | None = None, include_derivation: bool = True) -> dict:
        pos = [] if pos is None else pos
        d = {"origin": "decl:lemma", "preprocess": [op], "redex": pos if redex is None else redex,
             "extraArgs": extra, "binders": binders or [], "discharge": discharge or []}
        if source is not None:
            d["source"] = source
        if source_arg is not None:
            d["argId"] = source_arg
        result = {"kind": "rw", "pos": pos, "name": name, "dir": direction,
                  "side": side or [], "args": args or []}
        if prop is not None:
            result["prop"] = prop
        if include_derivation:
            result["derivation"] = d
        return result

    source = "foo, if_neg (fun h => h), H.eq, H.1, H.2"
    source_args = [
        {"argId": 0, "startChar": 0, "endChar": 3, "direction": "fwd"},
        {"argId": 1, "startChar": 5, "endChar": 24, "direction": "fwd"},
        {"argId": 2, "startChar": 26, "endChar": 30, "direction": "fwd"},
        {"argId": 3, "startChar": 32, "endChar": 35, "direction": "fwd"},
        {"argId": 4, "startChar": 37, "endChar": 40, "direction": "fwd"},
    ]
    cases = [
        ("direct_eq", step(), "foo at []"),
        ("iff_propext", step("iff_propext"), "foo at []"),
        ("prop_true", step("prop_to_true", prop="true"), "prop_true foo at []"),
        ("prop_false", step("not_to_false", prop="false"), "prop_false foo at []"),
        ("conjunction_left", step("conjunction_left", source_arg=3), "H.1 at []"),
        ("conjunction_right", step("conjunction_right", source_arg=4), "H.2 at []"),
        ("reverse", dict(step("direct_eq", direction="fwd"),
                          derivation={**step("direct_eq")["derivation"],
                                      "preprocess": ["reverse", "direct_eq"]}), "← foo at []"),
        ("extra_args_no_payload", step(source=None, source_arg=None, extra=1,
                                        args=["forged_payload"]), "lemma at []"),
        ("extra_args_option_or_else", step(source=None, source_arg=None, extra=2,
                                            pos=[0, 1, 0, 1, 0, 0],
                                            name="Option.orElse_eq_orElse"),
         "Option.orElse_eq_orElse at [0, 1, 0, 1, 0, 0]"),
        ("extra_args_function_prefix", step(source=None, source_arg=None, extra=1,
                                             pos=[0, 1, 0], name="Function.update_of_ne"),
         "Function.update_of_ne at [0, 1, 0]"),
    ]
    for name, value, expected in cases:
        try:
            f.equal("derivation/" + name,
                    R.render_step(value, source_text=source, source_args=source_args,
                                  operational=True), expected)
        except R.RenderError as exc:
            f.check("derivation/" + name, False, f"raised {exc}")

    # Source syntax is taken verbatim, including a lambda proof; no stored args
    # or proof expression can replace it. The one source-level named-argument
    # form is preserved and lowered by ExplicitRw itself.
    source_lambda = step(source_arg=1)
    f.equal("derivation/source_lambda_exact",
            R.render_step(source_lambda, source_text=source, source_args=source_args,
                          operational=True),
            "if_neg (fun h => h) at []")
    named_source = "heq_comm (a := a), heq_iff_exists_eq_cast"
    named_term, named_direction = R.source_argument(named_source, [
        {"argId": 0, "startChar": 0, "endChar": 17, "direction": "fwd"},
    ], 0)
    f.equal("derivation/source_named_argument_exact",
            (named_term, named_direction), ("heq_comm (a := a)", "fwd"))
    named = step(source_arg=0)
    f.equal("derivation/source_named_argument_rendered",
            R.render_step(named, source_text=named_source,
                          source_args=[
                              {"argId": 0, "startChar": 0, "endChar": 17,
                               "direction": "fwd"}],
                          operational=True),
            "heq_comm (a := a) at []")
    reversed_source = step("direct_eq", direction="fwd")
    try:
        R.render_step(reversed_source, source_text="← foo", source_args=[
            {"argId": 0, "startChar": 0, "endChar": 5, "direction": "rev"}],
            operational=True)
        f.check("derivation/reverse_direction_mismatch", False,
                "reversed source syntax was accepted with a forward trace direction")
    except R.RenderError as exc:
        f.equal("derivation/reverse_direction_mismatch", exc.reason,
                "direction_mismatch")
    matching_reverse = step("direct_eq", direction="rev")
    f.equal("derivation/reverse_source_matching_direction",
            R.render_step(matching_reverse, source_text="← foo", source_args=[
                {"argId": 0, "startChar": 0, "endChar": 5, "direction": "rev"}],
                operational=True),
            "← foo at []")
    unparseable = step(source_arg=0)
    try:
        R.render_step(unparseable, source_text="foo := bar", source_args=[
            {"argId": 0, "startChar": 0, "endChar": 10, "direction": "fwd"}],
            operational=True)
        f.check("derivation/unparseable_source", False, "named argument was accepted")
    except R.RenderError as exc:
        f.equal("derivation/unparseable_source/reason", exc.reason,
                "unparseable_source_argument")

    local = step(source="local-evidence", source_arg=None, name="H.1",
                 args=[], binders=[])
    local["local"] = {"userName": "H", "inaccessible": False, "ctxIndex": 2}
    f.equal("derivation/local_projection", R.render_step(local, operational=True),
            "local_ref 2 .1 at []")

    discharge = [{"id": 0, "classification": "discharge"}]
    nested = step(binders=discharge, discharge=[{"binder": 0, "provenance": "configured-or-default"}],
                  side=[{"pre": "p", "post": None,
                          "steps": [step(source=None, source_arg=None, name="side")],
                          "close": {"by": "rfl"}}])
    f.equal("derivation/nested_discharge",
            R.render_step(nested, source_text=source, source_args=source_args,
                          operational=True),
            "foo at [] with [explicit_rw [side at []] then rfl]")

    refusals = [
        ("missing", step(include_derivation=False), "missing_derivation"),
        ("redex", step(redex=[1]), "redex_mismatch"),
        ("duplicate_binder", step(binders=[{"id": 0, "classification": "matched"},
                                               {"id": 0, "classification": "instance"}]), "duplicate_binder"),
        ("binder_range", step(binders=[{"id": 1, "classification": "matched"}]), "binder_out_of_range"),
        ("binder_class", step(binders=[{"id": 0, "classification": "other"}]), "bad_binder_classification"),
        ("unknown_op", step("unknown"), "unknown_preprocess"),
        ("source_ordinal", step(source_arg=8), "source_arg_identity"),
        ("side_pairing", step(binders=[{"id": 0, "classification": "discharge"}],
                               discharge=[{"binder": 0, "provenance": "x"}], side=[]), "side_mismatch"),
    ]
    for name, value, reason in refusals:
        try:
            R.render_step(value, source_text=source, source_args=source_args,
                          operational=True)
            f.check("derivation/refusal_" + name, False, "did not refuse")
        except R.RenderError as exc:
            f.equal("derivation/refusal_" + name, exc.reason, reason)

    # Every refusal retains the original call through the pipeline site path.
    source = "import A\nexample : True := by\n  simp [foo]\n"
    site = S.find_sites(source)[0]
    refused = P.render_site(site, {"schema": "simp-trace-v2", "locations": [
        {"loc": "goal", "steps": [{**step(redex=[1])}], "close": None}
    ]}, source)
    f.equal("derivation/refusal_retains_original", refused["status"],
            "render_failed:redex_mismatch")
    f.check("derivation/refusal_original_present",
            any(site.text in line for line in refused["lines"]),
            "original call was not retained")


def summary_tests(f: Failures) -> None:
    """Summary rows expose every status and reconcile to site totals."""
    report = {
        "generated": "fixture", "t1_branch": "t1", "t1_commit": "abcdef0",
        "t1_dirty": False, "t2_branch": "t2", "t2_commit": "1234567",
        "t2_dirty": False,
        "modules": [
            {"module": "Mathlib/A.lean", "sites": 4, "seconds": 0,
             "compile_mode": "per_site", "records": [
                 {"site": 0, "line": 1, "status": "replayed"},
                 {"site": 1, "line": 2, "status": "compile_failed"},
                 {"site": 2, "line": 3, "status": "structurally_refused"},
                 {"site": 3, "line": 4, "status": "unresolved:fixture"},
             ]},
            {"module": "Mathlib/B.lean", "sites": 2, "seconds": 0,
             "compile_mode": "whole_module", "records": [
                 {"site": 0, "line": 1, "status": "render_failed:fixture"},
                 {"site": 1, "line": 2, "status": "probe_inconclusive"},
             ]},
        ],
    }
    summary = P.summarize(report)
    f.check("summary/structural_column", "structurally_refused" in summary,
            "structurally refused status has no explicit column")
    total = next((line for line in summary.splitlines() if line.startswith("| **total**")), "")
    cells = [cell.strip() for cell in total.split("|")[1:-1]]
    # module, sites, then one cell per status bucket, followed by mode/seconds.
    f.equal("summary/total_site_count", cells[1] if len(cells) > 1 else None, "**6**")
    counts = [int(cell.strip("*") or "0") for cell in cells[2:2 + len(P.STATUS_ORDER)]]
    f.equal("summary/total_reconciles", sum(counts), 6)
    f.equal("summary/structural_count", counts[P.STATUS_ORDER.index("structurally_refused")], 1)


def identity_tests(f: Failures) -> None:
    """The v2 source-site bijection fails closed before rendering."""
    source = (
        "-- Unicode before the authenticated sites: λ\n"
        "@[simp] lemma attr_one : True := by simp [p]\n"
        "@[simp] lemma attr_two : True := by simp [p]\n"
        "example : True := by simp [p]; simp [q]\n"
        "example : True := by simp; simp\n"
    )
    module = "Mathlib/Test/Identity.lean"
    sites = S.find_sites(source)
    manifest = P.build_manifest(module, source, sites)

    def record(site: dict, invocation: int = 0, invocations: int = 1) -> dict:
        return {
            "schema": "simp-trace-v2", "modulePath": module,
            "site": {key: site[key] for key in
                     ("siteOrdinal", "startChar", "endChar", "callText")},
            "occurrence": str(site["siteOrdinal"]),
            "invocation": invocation, "invocations": invocations,
            "locations": [],
        }

    records = [record(site) for site in manifest["sites"]]
    f.check("identity/unicode_char_ranges",
            manifest["sites"][0]["startChar"] > 0,
            "fixture did not exercise a nonzero Unicode character offset")
    accepted, _ = P.validate_identity(module, source, sites, records)
    f.equal("identity/valid_fixture", accepted["identity"], "accepted")
    f.equal("identity/fixture_site_count", accepted["expectedSites"], 6)

    def rejected(name: str, forged: list[dict], category: str | None = None) -> None:
        result, _ = P.validate_identity(module, source, sites, forged)
        f.equal("identity/" + name, result["identity"], "rejected")
        f.equal("identity/" + name + "/no_render", result["renderAttempted"], False)
        if category is not None:
            f.check("identity/" + name + "/category", bool(result.get(category)),
                    f"category {category} was empty: {result!r}")

    rejected("missing_site", records[:-1], "missingSites")
    extra = list(records) + [record(manifest["sites"][0])]
    rejected("duplicate_invocation", extra, "duplicateSiteInvocations")
    altered = record(manifest["sites"][0], invocation=2, invocations=2)
    rejected("out_of_range_invocation", records[:-1] + [altered],
             "incompleteInvocationOrdinals")
    wrong_call = list(records)
    wrong_call[0] = record(dict(manifest["sites"][0], callText="simp [forged]"))
    rejected("wrong_call", wrong_call, "identityMismatches")
    wrong_range = list(records)
    wrong_range[0] = record(dict(manifest["sites"][0], startChar=0))
    rejected("wrong_range", wrong_range, "identityMismatches")
    extra = list(records) + [dict(records[0], modulePath="Mathlib/Other.lean")]
    rejected("extra_trace", extra, "extraTraces")
    malformed = list(records)
    malformed[0] = dict(malformed[0], locations="not-an-array")
    rejected("malformed_locations", malformed, "invalidRecords")
    two_invocations = list(records[:-1]) + [record(manifest["sites"][-1], 0, 2),
                                             record(manifest["sites"][-1], 1, 2)]
    result, _ = P.validate_identity(module, source, sites, two_invocations)
    f.equal("identity/identical_invocation_payloads", result["identity"], "accepted")
    rejected("v1_rejected", [{**records[0], "schema": "simp-trace-v1"}], "invalidRecords")


def lifecycle_tests(f: Failures) -> None:
    """Run-local staging and finalization fixtures, without touching T1/T2."""
    trace_source = 'example : True := by simp =>trace "test/SimpTrace/meas_out/Test_01.json"\n'
    source = "example : True := by simp\n"
    sites = S.find_sites(source)
    module = "Mathlib/Test/Lifecycle.lean"
    with tempfile.TemporaryDirectory(prefix="lifecycle-check-") as tmp:
        out = pathlib.Path(tmp)
        first = P.make_trace_run(out, "TestTraced")
        second = P.make_trace_run(out, "TestTraced")
        f.check("lifecycle/run_dirs_do_not_collide", first[0] != second[0],
                "repeated runs reused one run directory")
        for run in (first, second):
            f.check("lifecycle/run_subdirs_exist", all(path.is_dir() for path in run[1:]),
                    f"missing stage/raw/final under {run[0]}")
        rewritten = P.rewrite_trace_paths(trace_source, first[2])
        f.check("lifecycle/trace_path_redirected",
                str(first[2] / "Test_01.json") in rewritten,
                "generated trace path was not redirected into raw")
        f.check("lifecycle/trace_path_preserves_ordinal",
                "Test_01.json" in rewritten,
                "trace basename/site ordinal was changed")

        site = sites[0]
        final_record = {
            "schema": "simp-trace-v2", "modulePath": module,
            "site": {"siteOrdinal": site.index, "startChar": site.start,
                     "endChar": site.end, "callText": site.text},
            "occurrence": "1", "invocation": 0, "invocations": 1,
            "locations": [],
        }
        raw_file = first[2] / "Test_01.json"
        final_file = first[3] / "Test_01.json"
        raw_file.write_text(json.dumps({"schema": "simp-trace-v1"}), encoding="utf-8")
        final_file.write_text(json.dumps(final_record), encoding="utf-8")
        f.equal("lifecycle/raw_stays_v1", json.loads(raw_file.read_text())["schema"],
                "simp-trace-v1")
        f.equal("lifecycle/final_is_v2", json.loads(final_file.read_text())["schema"],
                "simp-trace-v2")
        accepted, _ = P.validate_identity(module, source, sites,
                                           [json.loads(final_file.read_text())])
        f.equal("lifecycle/final_validates", accepted["identity"], "accepted")
        missing, _ = P.validate_identity(module, source, sites, [])
        f.equal("lifecycle/missing_final_rejected", missing["identity"], "rejected")
        f.equal("lifecycle/missing_final_no_render", missing["renderAttempted"], False)

        # Exercise the complete T4 lifecycle with a fixed-path T1 CLI mock.
        t1 = out / "t1"
        mathlib = out / "mathlib" / "Mathlib"
        (t1 / "test" / "SimpTrace").mkdir(parents=True)
        mathlib.mkdir(parents=True)
        original = mathlib / "Test" / "Lifecycle.lean"
        original.parent.mkdir()
        original.write_text(source, encoding="utf-8")
        traced = t1 / "test" / "SimpTrace" / "TestTraced.lean"
        traced.write_text(
            'example : True := by simp_trace =>trace "test/SimpTrace/meas_out/TestTraced_01.json"\n',
            encoding="utf-8")
        (t1 / "test" / "SimpTrace" / "TestTraced.manifest.json").write_text(
            "{}", encoding="utf-8")
        (t1 / "test" / "SimpTrace" / "check_transcription.py").write_text("", encoding="utf-8")
        (t1 / "test" / "SimpTrace" / "finalize_traces.py").write_text("", encoding="utf-8")
        calls: list[tuple[list[str], dict[str, str] | None]] = []
        original_run = P.run

        def fake_run(cmd: list[str], cwd: pathlib.Path, timeout: int = P.COMPILE_TIMEOUT,
                     env: dict[str, str] | None = None) -> tuple[int, str, str, float]:
            del timeout
            calls.append((cmd, env))
            if "check_transcription.py" in " ".join(cmd):
                return 0, "", "", 0.01
            if cmd and cmd[0] == "lake":
                staged_text = pathlib.Path(cmd[-1]).read_text(encoding="utf-8")
                f.check("lifecycle/mock_compile_uses_raw_path",
                        str(first[2]) not in staged_text and "raw/TestTraced_01.json" in staged_text,
                        "staged trace clause was not redirected")
                raw_path = pathlib.Path(env["SIMP_TRACE_OUT_ROOT"]) / "raw" / "TestTraced_01.json"
                raw_path.write_text(json.dumps({"schema": "simp-trace-v1"}), encoding="utf-8")
                return 0, "", "", 0.01
            if "--out-dir" in cmd:
                out_path = pathlib.Path(cmd[cmd.index("--out-dir") + 1])
                final_path = out_path / "TestTraced_01.json"
                final_path.write_text(json.dumps({
                    "schema": "simp-trace-v2", "modulePath": module,
                    "site": {"siteOrdinal": 0, "startChar": sites[0].start,
                              "endChar": sites[0].end, "callText": sites[0].text},
                    "occurrence": "1", "invocation": 0, "invocations": 1,
                    "locations": [],
                }), encoding="utf-8")
                f.check("lifecycle/finalizer_cli_shape",
                        all(flag in cmd for flag in
                            ("--traced-source", "--manifest", "--source", "--raw-dir", "--out-dir")),
                        "explicit-path finalizer CLI was not used")
                return 0, "", "", 0.01
            return 1, "", "unexpected mock command", 0.01

        P.run = fake_run
        try:
            _, transcription = P.transcribe(
                t1, mathlib, module, "TestTraced", out / "mock-run", False, [])
        finally:
            P.run = original_run
        f.equal("lifecycle/mock_final_is_v2",
                transcription["trace_records"][0]["schema"], "simp-trace-v2")
        mock_root = pathlib.Path(transcription["run_root"])
        f.equal("lifecycle/mock_raw_stays_v1",
                json.loads((mock_root / "raw" / "TestTraced_01.json").read_text())["schema"],
                "simp-trace-v1")
        f.check("lifecycle/compile_sets_out_root",
                any(env and env.get("SIMP_TRACE_OUT_ROOT") == str(mock_root)
                    for cmd, env in calls if cmd and cmd[0] == "lake"),
                "compile did not receive the T4 run root")


def publication_tests(f: Failures) -> None:
    """A failed current run cannot leave a stale module publication."""
    module = "Mathlib/Logic/Nontrivial/Defs.lean"
    source = "example : True := by simp\n"
    with tempfile.TemporaryDirectory(prefix="publication-check-") as tmp:
        root = pathlib.Path(tmp)
        mathlib = root / "mathlib" / "Mathlib"
        source_path = mathlib / "Logic" / "Nontrivial" / "Defs.lean"
        source_path.parent.mkdir(parents=True)
        source_path.write_text(source, encoding="utf-8")
        out = root / "published"
        target = out / module
        target.parent.mkdir(parents=True)
        target.write_text("old translated output\n", encoding="utf-8")
        marker = target.with_suffix(target.suffix + ".success")
        marker.write_text("old success\n", encoding="utf-8")
        old_transcribe = P.transcribe

        def fail_transcribe(*args: object, **kwargs: object) -> tuple[pathlib.Path, dict]:
            del args, kwargs
            return root / "stage.lean", {
                "trace_records": [{"schema": "simp-trace-v1"}],
                "run_root": str(root / "run"),
            }

        P.transcribe = fail_transcribe
        try:
            result = P.replay_module(module, root / "t1", root / "t2", out, mathlib)
        finally:
            P.transcribe = old_transcribe
        f.equal("publication/identity_failed", result["compile_mode"], "identity_failed")
        f.equal("publication/not_published", result["published"], False)
        f.check("publication/old_output_removed", not target.exists(),
                "stale translated output survived identity failure")
        f.check("publication/old_marker_removed", not marker.exists(),
                "stale success marker survived identity failure")
        f.check("publication/no_replay", not any(rec["status"] == "replayed"
                                                  for rec in result["records"]),
                "identity failure reported a replayed site")


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
        shared = t1 / "test" / "SimpTrace" / "meas_out"
        shared_before = {
            path.relative_to(shared): path.read_bytes()
            for path in shared.glob("*") if path.is_file()
        }
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
                mod["compile_mode"] in ("whole_module", "per_site", "identity_failed"),
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

        # A clean v2 producer output authenticates and permits rendering.
        translated_candidates = list(out.glob(
            "trace-runs/**/translated/Mathlib/Logic/Nontrivial/Defs.lean"))
        translated = translated_candidates[0] if translated_candidates else (
            out / "Mathlib" / "Logic" / "Nontrivial" / "Defs.lean")
        f.equal("e2e/identity_accepted_v2", mod.get("identity", {}).get("identity"), "accepted")
        f.equal("e2e/identity_render_attempted",
                mod.get("identity", {}).get("renderAttempted"), True)
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
        shared_after = {
            path.relative_to(shared): path.read_bytes()
            for path in shared.glob("*") if path.is_file()
        }
        f.equal("e2e/shared_t1_outputs_unchanged", shared_after, shared_before)

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
    mapping_tests(f)
    manual_override_tests(f)
    broader_overlay_tests(f)
    derivation_tests(f)
    summary_tests(f)
    identity_tests(f)
    lifecycle_tests(f)
    publication_tests(f)
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
