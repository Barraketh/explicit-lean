#!/usr/bin/env python3
"""Focused source identity and tactic-ancestry tests for the Lean AST extractor."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from pipeline import tactic_syntax_ast as ast
from pipeline import sites as S


FIXTURE = '''import Mathlib

def decoyString : String := "<;> simp"
-- comment decoy: <;> simp
/- block decoy: <;> simp -/

theorem oneLine : True := by ext <;> simp

theorem multiline : True := by
  apply And.intro
  <;> simp

theorem nested : True := by
  by_cases h : True <;> (by_cases h₂ : True <;> simp)

theorem corpusExt : True := by ext <;> simp
theorem corpusApply : True := by apply And.intro <;> simp
theorem corpusSplit : True := by split_ifs <;> simp [ite_true] <;> tauto
'''


class TacticSyntaxAstChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temp = tempfile.TemporaryDirectory(prefix="tactic-syntax-ast-")
        cls.path = Path(cls.temp.name) / "Fixture.lean"
        cls.path.write_text(FIXTURE, encoding="utf-8")
        cls.digest = hashlib.sha256(FIXTURE.encode("utf-8")).hexdigest()
        cls.sites = S.find_sites(FIXTURE)
        decoy_sites = []
        for needle, occurrence in (("simp", 0), ("simp", 1), ("simp", 2),
                                  ("<;>", 0), ("<;>", 1)):
            starts = [index for index in range(len(FIXTURE))
                      if FIXTURE.startswith(needle, index)]
            start = starts[occurrence]
            decoy_sites.append({
                "start_char": start, "end_char": start + len(needle),
                "expected_text": needle,
            })
        results = ast.extract_tactic_ancestries(
            module="Mathlib.TacticSyntaxFixture",
            source_path=cls.path,
            sites=[
                *[{"start_char": site.start, "end_char": site.end,
                   "expected_text": site.text} for site in cls.sites],
                *decoy_sites,
            ],
            expected_source_sha256=cls.digest,
            require_pinned_path=False,
            raise_on_refusal=False,
        )
        cls.valid_results = results[:len(cls.sites)]
        cls.decoy_results = results[len(cls.sites):]

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temp.cleanup()

    def extract(self, needle: str, occurrence: int = 0) -> dict:
        self.assertEqual(needle, "simp")
        return self.valid_results[occurrence]

    def test_one_line_and_source_decoys(self) -> None:
        result = self.extract("simp", occurrence=0)
        self.assertEqual(result["targetText"], "simp")
        self.assertEqual(result["targetStartChar"], self.sites[0].start)
        self.assertEqual(result["targetEndChar"], self.sites[0].end)
        self.assertEqual(result["target"]["startChar"], self.sites[0].start)
        self.assertEqual(result["target"]["endChar"], self.sites[0].end)
        self.assertTrue(any("tactic_<;>_" in node["kind"] for node in result["ancestry"]))
        # Text in strings and both comment forms does not become tactic syntax.
        self.assertTrue(all(item["status"] == "refused" for item in self.decoy_results))

    def test_every_parser_target_has_unique_authenticated_range(self) -> None:
        for site, result in zip(self.sites, self.valid_results):
            self.assertEqual(result["status"], "ok")
            self.assertEqual((result["target"]["startChar"], result["target"]["endChar"]),
                             (site.start, site.end))
            self.assertEqual(result["targetText"], site.text)
            self.assertEqual(result["ancestry"][-1]["kind"], "Lean.Parser.Tactic.simp")

    def test_pinned_mathlib_module_in_its_parser_environment(self) -> None:
        path = ast.ROOT / ".lake" / "packages" / "mathlib" / "Mathlib" / "Logic" / "Basic.lean"
        source_bytes = path.read_bytes()
        source = source_bytes.decode("utf-8")
        module_sites = S.find_sites(source)
        selected = [module_sites[0], module_sites[2]]  # `simp` and `simp only`
        results = ast.extract_tactic_ancestries(
            module="Mathlib.Logic.Basic", source_path=path,
            sites=[{"start_char": site.start, "end_char": site.end,
                    "expected_text": site.text} for site in selected],
            expected_source_sha256=hashlib.sha256(source_bytes).hexdigest(),
        )
        self.assertEqual([result["status"] for result in results], ["ok", "ok"])
        self.assertEqual([result["targetText"] for result in results],
                         [site.text for site in selected])

    def test_multiline_and_nested_sequence_ancestry(self) -> None:
        multiline = self.extract("simp", occurrence=1)
        seq_nodes = [node for node in multiline["ancestry"]
                     if "tactic_<;>_" in node["kind"]]
        self.assertTrue(seq_nodes)
        self.assertTrue(seq_nodes[-1]["branchChildren"])
        nested = self.extract("simp", occurrence=2)
        self.assertGreaterEqual(
            sum("tactic_<;>_" in node["kind"] for node in nested["ancestry"]), 2
        )

    def test_corpus_shapes_and_left_right_continuations(self) -> None:
        for occurrence in (3, 4, 5):
            result = self.extract("simp", occurrence=occurrence)
            seq_nodes = [node for node in result["ancestry"]
                         if "tactic_<;>_" in node["kind"]]
            self.assertTrue(seq_nodes, result)
            children = [child for node in seq_nodes for child in node["branchChildren"]]
            self.assertTrue(any(child["role"] == "left" for child in children))
            self.assertTrue(any(child["role"] == "right" for child in children), seq_nodes)
            if occurrence == 5:
                self.assertTrue(any(child["role"] == "continuation" for child in children), result["ancestry"])
            for child in children:
                self.assertLess(child["startChar"], child["endChar"])
                self.assertTrue(FIXTURE[child["startChar"]:child["endChar"]])

    def test_apply_all_child_ranges_are_exact_source_slices(self) -> None:
        multiline = self.extract("simp", occurrence=1)
        sequence = next(node for node in multiline["ancestry"]
                        if "tactic_<;>_" in node["kind"])
        children = sorted(sequence["branchChildren"], key=lambda child: child["startChar"])
        self.assertEqual(len(children), 2)
        self.assertEqual(
            [FIXTURE[child["startChar"] : child["endChar"]] for child in children],
            ["apply And.intro", "simp"],
        )
        self.assertEqual([child["role"] for child in children], ["left", "right"])

        nested = self.extract("simp", occurrence=2)
        nested_sequences = [node for node in nested["ancestry"]
                            if "tactic_<;>_" in node["kind"]]
        self.assertEqual(len(nested_sequences), 2)
        outer, inner = nested_sequences
        outer_children = sorted(outer["branchChildren"], key=lambda child: child["startChar"])
        inner_children = sorted(inner["branchChildren"], key=lambda child: child["startChar"])
        self.assertEqual(FIXTURE[outer_children[0]["startChar"] : outer_children[0]["endChar"]],
                         "by_cases h : True")
        self.assertEqual(FIXTURE[inner_children[0]["startChar"] : inner_children[0]["endChar"]],
                         "by_cases h₂ : True")
        self.assertEqual(FIXTURE[inner_children[1]["startChar"] : inner_children[1]["endChar"]],
                         "simp")

        continued = self.extract("simp", occurrence=5)
        self.assertTrue(any(
            child["role"] == "continuation"
            and FIXTURE[child["startChar"] : child["endChar"]] == "tauto"
            for node in continued["ancestry"]
            if "tactic_<;>_" in node["kind"]
            for child in node["branchChildren"]
        ))

    def test_authentication_rejects_changed_source_and_range(self) -> None:
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            ast.extract_tactic_ancestry(
                module="Mathlib.TacticSyntaxFixture", source_path=self.path,
                start_char=self.sites[0].start,
                end_char=self.sites[0].end,
                expected_text="simp", expected_source_sha256="0" * 64,
                require_pinned_path=False,
            )

    def test_ambiguous_syntax_result_is_rejected(self) -> None:
        refusal = [{"module": "Mathlib.TacticSyntaxFixture", "status": "refused",
                    "reason": "ambiguous_range", "matchCount": 2}]
        completed = unittest.mock.Mock(returncode=0, stdout=json.dumps(refusal), stderr="")
        site = self.sites[0]
        with patch.object(ast.subprocess, "run", return_value=completed):
            with self.assertRaisesRegex(ast.SyntaxExtractionError, "ambiguous_range"):
                ast.extract_tactic_ancestry(
                    module="Mathlib.TacticSyntaxFixture", source_path=self.path,
                    start_char=site.start, end_char=site.end,
                    expected_text=site.text, expected_source_sha256=self.digest,
                    require_pinned_path=False,
                )


if __name__ == "__main__":
    unittest.main()
