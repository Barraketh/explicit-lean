#!/usr/bin/env python3
"""Self-contained checks for :mod:`simp_family_lint` and its loader wiring.

Run with ``python3 -B Experiment/check_simp_family_lint.py`` (or from within
``Experiment/``).  The suite covers positives for every forbidden token,
negatives for lookalike identifiers and attribute syntax, comment and string
handling, the fixed override database, and the loader's rejection of a
violating entry.

The fast suite takes well under a second.  ``--sweep`` additionally runs the
whole-corpus assertion over every pinned Mathlib file (~8.3k files, a couple of
minutes), which is the regression test for the round-2 attribute defects.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import simp_family_lint as lint  # noqa: E402
import simp_manual_overrides as manual  # noqa: E402


DATABASE = HERE / "simp_manual_overrides.json"
MATHLIB = HERE.parents[0] / ".lake" / "packages" / "mathlib" / "Mathlib"

#: Set by ``--sweep`` on the command line.  The corpus sweep is slow, so it is
#: opt-in and the default suite stays fast.
RUN_SWEEP = False


class PositiveChecks(unittest.TestCase):
    """Every forbidden spelling is reported."""

    POSITIVES = (
        "simp",
        "simp?",
        "simp!",
        "simp_all",
        "simpa",
        "simp_rw",
        "simp_arith",
        "dsimp",
        "dsimp?",
        "dsimp only",
        "simp only",
        "field_simp",
        "norm_num",
        "push_cast",
        "norm_cast",
        "simp_wf",
        "simp_intro",
    )

    def test_every_listed_token_is_flagged(self) -> None:
        for token in self.POSITIVES:
            with self.subTest(token=token):
                self.assertTrue(
                    lint.has_simp_family(token),
                    f"{token!r} should be flagged",
                )

    def test_tokens_with_arguments_are_flagged(self) -> None:
        for snippet in (
            "simp only [foo, bar]",
            "dsimp only [tau, Equiv.coe_trans]",
            "simpa using h",
            "simp_rw [map_zero]",
            "field_simp [hx]",
            "norm_num [Nat.succ_eq_add_one]",
            "simp_all only [h]",
        ):
            with self.subTest(snippet=snippet):
                self.assertTrue(lint.has_simp_family(snippet))

    def test_tactic_inside_a_proof_body_is_flagged(self) -> None:
        source = "theorem t : True := by\n  intro\n  simp [foo]\n"
        results = lint.findings(source)
        self.assertEqual([item.token for item in results], ["simp"])
        self.assertEqual(results[0].line, 3)
        self.assertEqual(results[0].column, 3)

    def test_conv_block_occurrences_are_flagged(self) -> None:
        for snippet in (
            "conv => simp",
            "conv at h => dsimp only [f]",
            "conv in (_ + _) =>\n  simp only [add_comm]",
            "conv_lhs => simp",
        ):
            with self.subTest(snippet=snippet):
                self.assertTrue(lint.has_simp_family(snippet))

    def test_multiple_findings_are_all_reported(self) -> None:
        source = "by\n  simp\n  rw [h]\n  dsimp only [f]\n  norm_cast\n"
        self.assertEqual(
            [item.token for item in lint.findings(source)],
            ["simp", "dsimp", "norm_cast"],
        )


class NegativeChecks(unittest.TestCase):
    """Allowed tactics and lookalike identifiers are never reported."""

    def test_ordinary_tactics_are_clean(self) -> None:
        for snippet in (
            "rw [map_zero]",
            "exact zero_add _",
            "unfold tau",
            "change (algebraMap R A) 0 + _ = _",
            "show (algebraMap R A) 0 + _ = _",
            "rfl",
            "refine ⟨?_, fun x ↦ ?_⟩",
            "ring",
            "omega",
            "decide",
            "apply Subtype.ext",
        ):
            with self.subTest(snippet=snippet):
                self.assertFalse(lint.has_simp_family(snippet))

    def test_identifiers_containing_a_token_are_not_flagged(self) -> None:
        for snippet in (
            "simple",
            "simplex",
            "Simp.Result",
            "Lean.Meta.Simp.Config",
            "rw [simp_lemma_name]",
            "exact simpa_like_name",
            "dsimped",
            "let simp_count := 0",
            "norm_number",
            "push_castle",
        ):
            with self.subTest(snippet=snippet):
                self.assertFalse(
                    lint.has_simp_family(snippet),
                    f"{snippet!r} should not be flagged",
                )

    def test_simps_attribute_is_not_a_tactic(self) -> None:
        for snippet in (
            "@[simps]",
            "@[simps!]",
            "@[simps! apply_coe]\nnoncomputable def f := 1",
            "@[simps apply]\ndef g := 2",
            "@[to_additive, simps]\ndef h := 3",
        ):
            with self.subTest(snippet=snippet):
                self.assertFalse(
                    lint.has_simp_family(snippet),
                    f"{snippet!r} should not be flagged",
                )

    def test_simp_attribute_is_not_a_tactic_call(self) -> None:
        self.assertFalse(lint.has_simp_family("@[simp]\ntheorem t : True := trivial"))
        self.assertFalse(lint.has_simp_family("@[simp, norm_cast]\ntheorem t := trivial"))

    def test_bracket_attribute_forms_are_not_tactic_calls(self) -> None:
        for snippet in (
            "@[simp]",
            "@[simp, norm_cast]",
            "@[local simp]",
            "@[scoped simp]",
            "@[simps]",
            "@[simps!]",
            "@[-simp]",
            "@[simp] theorem t : True := trivial",
            "@[to_additive, simp] theorem t : True := trivial",
            "@[simps apply_coe, simp] def f := 1",
        ):
            with self.subTest(snippet=snippet):
                self.assertFalse(
                    lint.has_simp_family(snippet),
                    f"{snippet!r} is attribute syntax, not a tactic call",
                )

    def test_attribute_command_forms_are_not_tactic_calls(self) -> None:
        # `attribute [...simp...]` occurs in hundreds of pinned Mathlib files;
        # generated files must keep those declarations verbatim.
        for snippet in (
            "attribute [simp] Foo.bar",
            "attribute [simp] upperPolar_extent lowerPolar_intent",
            "attribute [local simp] foo",
            "attribute [scoped simp] foo",
            "attribute [-simp] foo",
            "attribute [simp, norm_cast] foo bar",
            "  attribute [simp] a b c",
            "attribute [dsimp] foo",
            "attribute [push_cast] foo",
        ):
            with self.subTest(snippet=snippet):
                self.assertFalse(
                    lint.has_simp_family(snippet),
                    f"{snippet!r} is an attribute command, not a tactic call",
                )

    def test_attr_assignment_form_is_not_a_tactic_call(self) -> None:
        for snippet in (
            "@[to_additive (attr := simp)] theorem t : a = a := rfl",
            "@[to_additive (attr := simp, norm_cast)] def f := 1",
            "@[simps (attr := simp)] def g := 2",
        ):
            with self.subTest(snippet=snippet):
                self.assertFalse(
                    lint.has_simp_family(snippet),
                    f"{snippet!r} is attribute configuration, not a tactic call",
                )

    def test_attribute_as_an_ordinary_word_does_not_shield_a_tactic(self) -> None:
        # Only a command-position `attribute` opens an attribute list; the word
        # appearing mid-expression must not suppress a real finding.
        self.assertTrue(lint.has_simp_family("exact foo attribute [simp]"))

    def test_attribute_line_does_not_shield_a_later_tactic(self) -> None:
        source = "attribute [simp] foo\n\nexample : True := by\n  simp\n"
        results = lint.findings(source)
        self.assertEqual([item.token for item in results], ["simp"])
        self.assertEqual(results[0].line, 4)


class CommentChecks(unittest.TestCase):
    """Comments, including the retained originals, are ignored."""

    def test_line_comment_is_ignored(self) -> None:
        self.assertFalse(lint.has_simp_family("rw [h] -- simp only [foo]"))

    def test_retained_original_simp_comment_is_ignored(self) -> None:
        source = (
            "show (algebraMap R A) 0 + _ = _\n"
            "  -- Original simp:\n"
            "  -- simp [starAlgHom]\n"
            "  rw [map_zero]\n"
            "  exact zero_add _\n"
        )
        self.assertEqual(lint.findings(source), [])

    def test_block_comment_is_ignored(self) -> None:
        self.assertFalse(lint.has_simp_family("/- simp only [a] -/\nrw [b]"))

    def test_nested_block_comment_is_ignored(self) -> None:
        self.assertFalse(
            lint.has_simp_family("/- outer /- simp -/ still comment -/\nrfl")
        )

    def test_doc_comment_is_ignored(self) -> None:
        self.assertFalse(
            lint.has_simp_family("/-- Proved by `simp` historically. -/\ndef f := 1")
        )

    def test_code_after_a_block_comment_is_still_scanned(self) -> None:
        results = lint.findings("/- simp -/ simp only [a]")
        self.assertEqual([item.token for item in results], ["simp"])

    def test_code_after_a_line_comment_is_still_scanned(self) -> None:
        results = lint.findings("-- simp\nsimp only [a]\n")
        self.assertEqual([item.token for item in results], ["simp"])
        self.assertEqual(results[0].line, 2)


class StringChecks(unittest.TestCase):
    """String and character literals are ignored."""

    def test_string_literal_is_ignored(self) -> None:
        self.assertFalse(lint.has_simp_family('exact msg "simp only [a]"'))

    def test_escaped_quote_inside_string_is_handled(self) -> None:
        self.assertFalse(lint.has_simp_family('let s := "a \\" simp [b]"'))

    def test_interpolated_string_is_ignored(self) -> None:
        self.assertFalse(lint.has_simp_family('throwError s!"cannot simp {e}"'))

    def test_code_after_a_string_is_still_scanned(self) -> None:
        results = lint.findings('exact msg "simp" <;> simp')
        self.assertEqual([item.token for item in results], ["simp"])

    def test_identifier_prime_is_not_a_character_literal(self) -> None:
        # `h'` must not open a character literal and swallow the `simp` after.
        results = lint.findings("have h' := t\n  simp\n")
        self.assertEqual([item.token for item in results], ["simp"])


class ApiChecks(unittest.TestCase):
    """Structured results and the error helper behave as documented."""

    def test_findings_report_offsets_and_text(self) -> None:
        source = "by\n  dsimp only [f]\n"
        (item,) = lint.findings(source)
        self.assertEqual(item.token, "dsimp")
        self.assertEqual(item.line, 2)
        self.assertEqual(item.column, 3)
        self.assertEqual(source[item.offset : item.offset + 5], "dsimp")
        self.assertEqual(item.text, "dsimp only [f]")

    def test_assert_clean_passes_on_clean_source(self) -> None:
        lint.assert_clean("rw [map_zero]\nexact zero_add _")

    def test_assert_clean_names_the_label_and_token(self) -> None:
        with self.assertRaises(RuntimeError) as caught:
            lint.assert_clean("dsimp only [f]", "entry abc")
        message = str(caught.exception)
        self.assertIn("entry abc", message)
        self.assertIn("dsimp", message)

    def test_non_string_input_is_rejected(self) -> None:
        with self.assertRaises(TypeError):
            lint.findings(None)  # type: ignore[arg-type]

    def test_cli_exit_status(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            clean = Path(directory) / "clean.lean"
            clean.write_text("theorem t : True := by rfl\n", encoding="utf-8")
            dirty = Path(directory) / "dirty.lean"
            dirty.write_text("theorem t : True := by simp\n", encoding="utf-8")
            self.assertEqual(lint.main([str(clean), "--quiet"]), 0)
            self.assertEqual(lint.main([str(dirty), "--quiet"]), 1)


class AttributeSpellingChecks(unittest.TestCase):
    """The 11 real Mathlib attribute spellings reported in review round 2.

    Round 1 decided attribute context with a backward character scan that
    aborted on any unexpected character, so an attribute list containing
    ``(``, ``=``, ``>``, ``<-`` or a string flagged the token after it, and any
    modifier in front of the ``attribute`` keyword defeated the command check.
    Detection is now structural (match brackets backwards), and each spelling
    below is pinned so the class of defect cannot come back one spelling at a
    time.
    """

    #: Defect 1: `@[...]` lists whose contents broke the character scan.
    BRACKET_SPELLINGS = (
        "@[simp <-, push_cast] theorem t : a = a := rfl",
        "@[simp ←, push_cast] theorem t : a = a := rfl",
        "@[push <-, simp] theorem t : a = a := rfl",
        "@[push ←, simp] theorem t : a = a := rfl",
        "@[grind =>, simp] lemma t : a = a := rfl",
        "@[simp, grind =, norm_cast] theorem t : a = a := rfl",
        "@[aesop (rule_sets := [finiteness]) safe apply, simp] theorem t : a = a := rfl",
        '@[deprecated "use X" (since := "2026-02-21"), norm_cast] theorem t : a = a := rfl',
        "@[to_dual self (reorder := f g, hf hg), simp] theorem t : a = a := rfl",
    )

    #: Defect 2: prefixes in front of the `attribute` command keyword.
    COMMAND_SPELLINGS = (
        "local attribute [simp] foo",
        "scoped attribute [simp] foo",
        "scoped[Pointwise] attribute [simp] Set.image_smul",
        "scoped[AddConstMapClass] attribute [simp] map_add_const",
        "open Foo in attribute [simp] foo",
        "open Foo Bar in attribute [simp] foo",
        "variable {x : Nat} in attribute [simp] foo",
        "private attribute [simp] foo",
        "protected attribute [simp] foo",
    )

    def test_bracket_attribute_spellings_are_clean(self) -> None:
        for snippet in self.BRACKET_SPELLINGS:
            with self.subTest(snippet=snippet):
                self.assertEqual(
                    lint.findings(snippet),
                    [],
                    f"{snippet!r} is attribute syntax, not a tactic call",
                )

    def test_command_attribute_spellings_are_clean(self) -> None:
        for snippet in self.COMMAND_SPELLINGS:
            with self.subTest(snippet=snippet):
                self.assertEqual(
                    lint.findings(snippet),
                    [],
                    f"{snippet!r} is an attribute command, not a tactic call",
                )

    def test_nested_argument_groups_are_resolved_outwards(self) -> None:
        # A token inside a nested group of an attribute list is still an
        # attribute, however deep the nesting goes.
        for snippet in (
            "@[aesop (rule_sets := [simp]) safe apply] theorem t : a = a := rfl",
            "@[foo (bar := (baz := simp))] theorem t : a = a := rfl",
            "@[to_additive (attr := simp, norm_cast)] def f := 1",
        ):
            with self.subTest(snippet=snippet):
                self.assertEqual(lint.findings(snippet), [])

    def test_attribute_list_split_across_lines_is_clean(self) -> None:
        self.assertEqual(lint.findings("attribute [\n  simp] foo"), [])
        self.assertEqual(lint.findings("@[\n  simp,\n  norm_cast]\ndef f := 1"), [])

    def test_prefixes_do_not_shield_a_real_tactic(self) -> None:
        # The command-position guard must survive the widening: a keyword in
        # the middle of an expression still does not make a tactic an
        # attribute, and neither does an attribute line above one.
        for snippet in (
            "exact foo attribute [simp]",
            "local attribute [simp] foo\nexample : True := by\n  simp",
            "scoped[NS] attribute [simp] foo\nexample : True := by\n  simp",
            "open Foo in attribute [simp] foo\nexample : True := by\n  simp",
        ):
            with self.subTest(snippet=snippet):
                self.assertTrue(
                    lint.has_simp_family(snippet),
                    f"{snippet!r} contains a real simp tactic",
                )

    def test_attribute_on_a_declaration_proved_by_simp(self) -> None:
        # Only the tactic is a finding, never the attribute in front of it.
        results = lint.findings("@[simp] lemma l : a = a := by simp")
        self.assertEqual([(i.token, i.column) for i in results], [("simp", 31)])
        results = lint.findings("@[simp] theorem t : a = a := by simp only [x]")
        self.assertEqual([(i.token, i.column) for i in results], [("simp", 33)])


class WholeFileChecks(unittest.TestCase):
    """Whole-file runs, including the reviewer's round-1 reproduction."""

    #: Pinned Mathlib module whose line 277 is `attribute [simp] ...`.  Round 1
    #: flagged that line; it must never be reported again.
    REPRODUCTION = (
        HERE.parents[0]
        / ".lake"
        / "packages"
        / "mathlib"
        / "Mathlib"
        / "Order"
        / "Concept.lean"
    )

    def test_reproduction_file_reports_no_attribute_finding(self) -> None:
        if not self.REPRODUCTION.exists():
            self.skipTest("pinned Mathlib checkout is not available")
        text = self.REPRODUCTION.read_text(encoding="utf-8")
        results = lint.findings(text)
        # The file genuinely contains simp *tactic* calls, so a zero-findings
        # assertion would be wrong.  What round 1 requires is that no finding
        # comes from the `attribute [simp]` declaration on line 277.
        attribute_lines = [
            number
            for number, line in enumerate(text.splitlines(), start=1)
            if line.lstrip().startswith("attribute [")
        ]
        self.assertEqual(attribute_lines, [277])
        self.assertNotIn(
            277,
            [item.line for item in results],
            "the `attribute [simp]` declaration must not be flagged",
        )
        for item in results:
            with self.subTest(line=item.line):
                self.assertFalse(
                    text.splitlines()[item.line - 1].lstrip().startswith("attribute ["),
                    "no finding may come from an attribute declaration",
                )

    def test_handwritten_file_reports_exactly_the_one_real_call(self) -> None:
        source = """\
/-- Doc comment mentioning simp only [foo]. -/
@[simp]
theorem a : True := trivial

@[simp, norm_cast]
theorem b : True := trivial

@[local simp]
theorem c : True := trivial

@[simps]
def d := 1

@[to_additive (attr := simp)]
theorem e : True := trivial

attribute [simp] a b
attribute [local simp] c
attribute [scoped simp] c
attribute [-simp] a

-- A retained original: simp [foo]
/- block comment with dsimp only [bar] -/
def message : String := "simp only [baz]"

example : True := by
  simp
"""
        results = lint.findings(source)
        self.assertEqual(
            [(item.token, item.line) for item in results],
            [("simp", 27)],
            f"expected exactly one finding, got {lint.format_findings(results)}",
        )

    def test_handwritten_file_via_the_cli(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Attributes.lean"
            path.write_text(
                "attribute [simp] foo\n@[simp, norm_cast]\ntheorem t : True := trivial\n",
                encoding="utf-8",
            )
            self.assertEqual(lint.main([str(path), "--quiet"]), 0)


class CorpusSweepChecks(unittest.TestCase):
    """Whole-corpus assertion over every pinned Mathlib file.

    Review round 2 found the 18 attribute-derived false positives by sweeping
    the corpus, so the corpus is the regression test.  It is slow (~8.3k files,
    a couple of minutes), so it only runs under ``--sweep``; the fast suite
    stays well under a second.
    """

    def setUp(self) -> None:
        if not RUN_SWEEP:
            self.skipTest("corpus sweep is opt-in; pass --sweep to run it")
        if not MATHLIB.is_dir():
            self.skipTest("pinned Mathlib checkout is not available")

    def test_no_finding_lies_inside_an_attribute_list(self) -> None:
        """Zero attribute-derived findings across the whole pinned corpus.

        A finding is attribute-derived when its token sits inside an attribute
        list, decided by the same structural check the lint uses.  Round 2
        counted 18 such findings; there must now be none.
        """

        offenders: list[str] = []
        files = 0
        total = 0
        for path in sorted(MATHLIB.rglob("*.lean")):
            try:
                text = path.read_text(encoding="utf-8")
            except OSError:
                continue
            files += 1
            results = lint.findings(text)
            if not results:
                continue
            total += len(results)
            masked = lint._mask(text)
            lines = text.splitlines()
            for item in results:
                if lint._in_attribute_list(masked, item.offset):
                    offenders.append(
                        f"{path.relative_to(MATHLIB)}:{item.line}: "
                        f"{lines[item.line - 1].strip()[:72]}"
                    )
        self.assertGreater(files, 8000, "corpus looks unexpectedly small")
        self.assertGreater(total, 0, "corpus should contain real simp calls")
        self.assertEqual(
            offenders,
            [],
            f"{len(offenders)} attribute-derived finding(s):\n"
            + "\n".join(offenders[:40]),
        )

    def test_known_round_two_occurrences_are_clean(self) -> None:
        """The exact 18 occurrences review round 2 listed are not flagged.

        Pinned by file and text so that a future regression names the case,
        not just a count.  Files that have moved upstream are skipped rather
        than failing, since the corpus is pinned but not owned by this task.
        """

        expected = {
            "Algebra/AddConstMap/Basic.lean": 1,
            "Algebra/Group/Pointwise/Set/Scalar.lean": 1,
            "Algebra/Homology/HomologicalComplex.lean": 1,
            "Algebra/Order/Kleene.lean": 1,
            "Analysis/Normed/Group/Defs.lean": 1,
            "Data/ENNReal/Inv.lean": 2,
            "Data/Finset/Range.lean": 1,
            "Data/Finset/SDiff.lean": 1,
            "GroupTheory/SpecificGroups/KleinFour.lean": 2,
            "Tactic/Zify.lean": 1,
            "Topology/Instances/Rat.lean": 2,
            "Topology/IsLocalHomeomorph.lean": 2,
            "Topology/MetricSpace/Pseudo/Defs.lean": 1,
            "Topology/Order/OrderClosed.lean": 1,
        }
        self.assertEqual(sum(expected.values()), 18)
        checked = 0
        for relative, count in sorted(expected.items()):
            path = MATHLIB / relative
            if not path.is_file():
                continue
            text = path.read_text(encoding="utf-8")
            masked = lint._mask(text)
            attribute_findings = [
                item
                for item in lint.findings(text)
                if lint._in_attribute_list(masked, item.offset)
            ]
            with self.subTest(module=relative):
                self.assertEqual(
                    attribute_findings,
                    [],
                    f"{relative} still reports attribute syntax "
                    f"(round 2 counted {count} here)",
                )
            checked += 1
        self.assertGreater(checked, 0, "none of the pinned modules were found")


class DatabaseChecks(unittest.TestCase):
    """The shipped override database is clean and the loader enforces the rule."""

    def setUp(self) -> None:
        self.database = json.loads(DATABASE.read_text(encoding="utf-8"))

    def test_every_replacement_is_clean(self) -> None:
        overrides = self.database["overrides"]
        self.assertEqual(len(overrides), 26)
        for entry in overrides:
            with self.subTest(occurrence=entry["occurrence"]):
                self.assertEqual(
                    lint.findings(str(entry["replacement"])),
                    [],
                    f"override {entry['occurrence']} uses a simp-family tactic",
                )

    def test_fixed_database_loads(self) -> None:
        _environment, entries = manual.load_database(DATABASE)
        self.assertEqual(len(entries), 26)

    def test_loader_rejects_a_violating_replacement(self) -> None:
        for bad in ("dsimp [starAlgHom]", "dsimp only [tau]", "push_cast\n  rfl"):
            with self.subTest(replacement=bad):
                broken = json.loads(json.dumps(self.database))
                target = broken["overrides"][5]
                self.assertEqual(target["occurrence"], "1734864b48394331")
                target["replacement"] = bad
                with tempfile.TemporaryDirectory() as directory:
                    path = Path(directory) / "broken.json"
                    path.write_text(json.dumps(broken), encoding="utf-8")
                    with self.assertRaises(RuntimeError) as caught:
                        manual.load_database(path)
                    message = str(caught.exception)
                    self.assertIn("1734864b48394331", message)
                    self.assertIn("simp-family", message)

    def test_loader_still_accepts_the_shipped_replacements(self) -> None:
        # A round trip through a temporary copy proves the rejection above is
        # caused by the injected token, not by the copy itself.
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "copy.json"
            path.write_text(json.dumps(self.database), encoding="utf-8")
            _environment, entries = manual.load_database(path)
            self.assertEqual(len(entries), 26)


if __name__ == "__main__":
    if "--sweep" in sys.argv:
        sys.argv.remove("--sweep")
        RUN_SWEEP = True
    unittest.main(verbosity=2)
