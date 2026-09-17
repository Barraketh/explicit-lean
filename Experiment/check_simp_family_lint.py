#!/usr/bin/env python3
"""Self-contained checks for :mod:`simp_family_lint` and its loader wiring.

Run with ``python3 -B Experiment/check_simp_family_lint.py`` (or from within
``Experiment/``).  The suite covers positives for every forbidden token,
negatives for lookalike identifiers and the ``@[simps]`` attribute, comment and
string handling, the fixed override database, and the loader's rejection of a
violating entry.
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


class DatabaseChecks(unittest.TestCase):
    """The shipped override database is clean and the loader enforces the rule."""

    def setUp(self) -> None:
        self.database = json.loads(DATABASE.read_text(encoding="utf-8"))

    def test_every_replacement_is_clean(self) -> None:
        overrides = self.database["overrides"]
        self.assertEqual(len(overrides), 21)
        for entry in overrides:
            with self.subTest(occurrence=entry["occurrence"]):
                self.assertEqual(
                    lint.findings(str(entry["replacement"])),
                    [],
                    f"override {entry['occurrence']} uses a simp-family tactic",
                )

    def test_fixed_database_loads(self) -> None:
        _environment, entries = manual.load_database(DATABASE)
        self.assertEqual(len(entries), 21)

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
            self.assertEqual(len(entries), 21)


if __name__ == "__main__":
    unittest.main(verbosity=2)
