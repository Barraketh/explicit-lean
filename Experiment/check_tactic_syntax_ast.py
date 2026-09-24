#!/usr/bin/env python3
"""Focused source identity and tactic-ancestry tests for the Lean AST extractor."""

from __future__ import annotations

import hashlib
import json
import copy
from pathlib import Path
import subprocess
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

SIMP_INVENTORY_FIXTURE = '''import Mathlib

def decoyText : String := "simp aesop (add simp)"
-- simp
attribute [simp] True.intro

theorem body : True := by
  simp

theorem only : True := by
  simp only [True.intro]

def recursive (n : Nat) : Nat := recursive (n - 1)
termination_by n
decreasing_by
  simp

theorem nested : True := by
  all_goals
    first | exact True.intro | simp

theorem configured : True := by
  aesop (add simp [True.intro])

example : True := by
  fun_prop (disch := simp)

theorem multi : True := by simp; simp

lemma letTyped : (let x := True; x) := by simp

theorem structured : And True True where
  left := by simp
  right := by simp

theorem equations : ∀ n : Nat, n = n
  | 0 => by simp
  | n + 1 => by simp
'''

PARSER_CONTEXT_FIXTURE = '''import Mathlib

def parserContextDocTarget : Nat := 0

@[inherit_doc parserContextDocTarget]
scoped syntax:max "t82⟦" term "⟧" : term
macro_rules | `(t82⟦$x⟧) => `($x)

syntax t82Binder := ident
syntax "t82BinderTerm " t82Binder : term
macro "t82_local_tac" : tactic => `(tactic| exact True.intro)

namespace ParserContextLocal
def sourceLocalName : Nat := 0
end ParserContextLocal
open ParserContextLocal (sourceLocalName)

open scoped ParserContextFixture in
theorem parserContextBody : True := by
  t82_local_tac
  simp
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
        cls.simp_inventory_digest = hashlib.sha256(
            SIMP_INVENTORY_FIXTURE.encode("utf-8")).hexdigest()
        cls.simp_candidate_with_import = S.add_import(SIMP_INVENTORY_FIXTURE)
        cls.simp_candidate_digest = hashlib.sha256(
            cls.simp_candidate_with_import.encode("utf-8")).hexdigest()
        cls.simp_inventory, cls.simp_candidate_inventory = ast.inventory_simp_tactics_batch([
            {"module": "Mathlib.SimpCommandInventoryFixture",
             "source": SIMP_INVENTORY_FIXTURE,
             "expected_source_sha256": cls.simp_inventory_digest},
            {"module": "Mathlib.SimpCommandInventoryFixture",
             "source": cls.simp_candidate_with_import,
             "expected_source_sha256": cls.simp_candidate_digest},
        ])

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

    def test_term_elaboration_gate_uses_authenticated_command_ast(self) -> None:
        path = ast.ROOT / ".lake" / "packages" / "mathlib" / "Mathlib" / "Logic" / "Basic.lean"
        ordinary = path.read_bytes()
        result = ast.inspect_term_elaboration_boundary(
            module="Mathlib.Logic.Basic", source_path=path,
            expected_source_sha256=hashlib.sha256(ordinary).hexdigest(),
        )
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["risks"], [])
        self.assertEqual(result["moduleSourceSha256"],
                         hashlib.sha256(ordinary).hexdigest())
        tactic_only = 'import Lean\nsyntax "gateTacticOnly" : tactic\n'
        with tempfile.TemporaryDirectory(prefix="term-gate-tactic-only-") as temp:
            tactic_path = Path(temp) / "TacticOnly.lean"
            tactic_path.write_text(tactic_only, encoding="utf-8")
            tactic_result = ast.inspect_term_elaboration_boundary(
                module="Mathlib.TermGateTacticOnly", source_path=tactic_path,
                expected_source_sha256=hashlib.sha256(tactic_only.encode()).hexdigest(),
                require_pinned_path=False,
            )
        self.assertEqual(tactic_result["status"], "ok", tactic_result)
        self.assertEqual(tactic_result["risks"], [])

    def test_term_elaboration_gate_refuses_source_local_term_hooks(self) -> None:
        dangerous = '''import Lean
syntax "hiddenSyntax" : term
macro "hiddenMacro" : term => `(0)
macro_rules | `(term| (1 + 0)) => `(1)
elab "hiddenElab" : term => `(0)
elab_rules : term | `(hiddenSyntax) => `(0)
@[term_elab Lean.Parser.Term.ident]
def hiddenIdentElab : Lean.Elab.Term.TermElab := fun _ _ => do
  Lean.Meta.Simp.simpGoal (← Lean.Elab.Term.getMainGoal)
initialize hiddenExtensionRegistrationProbe : IO Unit := pure ()
run_cmd pure ()
attribute [term_elab] hiddenIdentElab
'''
        with tempfile.TemporaryDirectory(prefix="term-gate-negative-") as temp:
            path = Path(temp) / "Dangerous.lean"
            path.write_text(dangerous, encoding="utf-8")
            result = ast.inspect_term_elaboration_boundary(
                module="Mathlib.TermGateDangerous", source_path=path,
                expected_source_sha256=hashlib.sha256(dangerous.encode()).hexdigest(),
                require_pinned_path=False,
            )
        self.assertEqual(result["status"], "refused", result)
        self.assertEqual(
            [risk["reason"] for risk in result["risks"]],
            ["source_term_syntax", "source_term_macro_or_elaborator",
             "source_term_macro_rules", "source_term_macro_or_elaborator",
             "source_term_macro_or_elaborator", "source_term_elab_attribute",
             "source_command_can_register_term_extension",
             "source_command_can_register_term_extension",
             "source_term_elab_attribute"],
        )
        self.assertIn("Lean.Meta.Simp.simpGoal", dangerous)
        for risk in result["risks"]:
            self.assertEqual(
                dangerous[risk["startChar"]:risk["endChar"]].splitlines()[0].split()[0],
                {"Lean.Parser.Command.syntax": "syntax",
                 "Lean.Parser.Command.macro": "macro",
                 "Lean.Parser.Command.macro_rules": "macro_rules",
                 "Lean.Parser.Command.elab": "elab",
                 "Lean.Parser.Command.elab_rules": "elab_rules",
                 "Lean.Parser.Command.declaration": "@[term_elab",
                 "Lean.Parser.Command.initialize": "initialize",
                 "Lean.runCmd": "run_cmd",
                 "Lean.Parser.Command.attribute": "attribute"}[risk["kind"]],
            )

    def test_term_elaboration_gate_authenticates_bytes_and_pinned_identity(self) -> None:
        ordinary = "import Lean\ndef x : Nat := 1\n"
        with tempfile.TemporaryDirectory(prefix="term-gate-identity-") as temp:
            path = Path(temp) / "Identity.lean"
            path.write_text(ordinary, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                ast.inspect_term_elaboration_boundary(
                    module="Mathlib.TermGateIdentity", source_path=path,
                    expected_source_sha256="0" * 64, require_pinned_path=False,
                )

    def test_executable_proof_hole_ast_audit_ignores_comments_and_strings(self) -> None:
        clean = '''import Lean
/-- The words sorry and admit here are documentation. -/
def tokenAuditText : String := "sorry admit"
-- sorry admit
theorem tokenAuditClean : True := by exact True.intro
'''
        clean_result = ast.audit_executable_proof_holes(
            module="Mathlib.ProofHoleCleanFixture", source=clean,
            expected_source_sha256=hashlib.sha256(clean.encode()).hexdigest(),
        )
        self.assertEqual(clean_result["status"], "ok", clean_result)
        self.assertEqual(clean_result["proofHoles"], [])
        dirty = '''import Lean
theorem tokenAuditSorry : True := by exact sorry
def tokenAuditAdmit : Nat := admit
'''
        dirty_result = ast.audit_executable_proof_holes(
            module="Mathlib.ProofHoleDirtyFixture", source=dirty,
            expected_source_sha256=hashlib.sha256(dirty.encode()).hexdigest(),
        )
        self.assertEqual(dirty_result["status"], "refused", dirty_result)
        self.assertEqual([item["token"] for item in dirty_result["proofHoles"]],
                         ["sorry", "admit"])

    def test_inventory_accepts_imported_command_macro_kinds(self) -> None:
        result = copy.deepcopy(self.simp_inventory)
        result["commands"][0]["kind"] = "Demo.ImportedCommandMacro.expansion"
        validated = ast._validate_simp_inventory_result(
            result,
            module="Mathlib.SimpCommandInventoryFixture",
            source=SIMP_INVENTORY_FIXTURE,
            source_bytes=SIMP_INVENTORY_FIXTURE.encode("utf-8"),
            digest=self.simp_inventory_digest,
            request_id=result["requestId"],
        )
        self.assertEqual(
            validated["commands"][0]["kind"],
            "Demo.ImportedCommandMacro.expansion",
        )

    def test_inventory_installs_source_local_parser_context_without_semantic_declarations(self) -> None:
        digest = hashlib.sha256(PARSER_CONTEXT_FIXTURE.encode()).hexdigest()
        inventory = ast.inventory_simp_tactics(
            module="Mathlib.ParserContextFixture",
            source=PARSER_CONTEXT_FIXTURE,
            expected_source_sha256=digest,
        )
        self.assertEqual(inventory["status"], "ok", inventory)
        sites = [
            site for command in inventory["commands"] for site in command["simpSites"]
        ]
        self.assertEqual(len(sites), 1)
        self.assertEqual(
            PARSER_CONTEXT_FIXTURE[sites[0]["startChar"]:sites[0]["endChar"]],
            "simp",
        )

    def test_direct_simp_inventory_covers_executable_command_contexts_only(self) -> None:
        commands = self.simp_inventory["commands"]
        body = next(command for command in commands
                    if "theorem body" in SIMP_INVENTORY_FIXTURE[
                        command["startChar"]:command["endChar"]])
        only = next(command for command in commands
                    if "theorem only" in SIMP_INVENTORY_FIXTURE[
                        command["startChar"]:command["endChar"]])
        decreasing = next(command for command in commands
                           if "decreasing_by" in SIMP_INVENTORY_FIXTURE[
                               command["startChar"]:command["endChar"]])
        nested = next(command for command in commands
                      if "theorem nested" in SIMP_INVENTORY_FIXTURE[
                          command["startChar"]:command["endChar"]])
        configured = next(command for command in commands
                          if "theorem configured" in SIMP_INVENTORY_FIXTURE[
                              command["startChar"]:command["endChar"]])
        disch = next(command for command in commands
                     if "fun_prop (disch := simp)" in SIMP_INVENTORY_FIXTURE[
                         command["startChar"]:command["endChar"]])
        multi = next(command for command in commands
                     if "theorem multi" in SIMP_INVENTORY_FIXTURE[
                         command["startChar"]:command["endChar"]])
        let_typed = next(command for command in commands
                         if "lemma letTyped" in SIMP_INVENTORY_FIXTURE[
                             command["startChar"]:command["endChar"]])
        structured = next(command for command in commands
                          if "theorem structured" in SIMP_INVENTORY_FIXTURE[
                              command["startChar"]:command["endChar"]])
        equations = next(command for command in commands
                         if "theorem equations" in SIMP_INVENTORY_FIXTURE[
                             command["startChar"]:command["endChar"]])
        self.assertEqual(len(body["simpSites"]), 1)
        self.assertEqual(len(only["simpSites"]), 1)
        only_site = only["simpSites"][0]
        self.assertTrue(SIMP_INVENTORY_FIXTURE[
            only_site["startChar"]:only_site["endChar"]].startswith("simp only"))
        self.assertEqual(len(decreasing["simpSites"]), 1)
        self.assertEqual(len(nested["simpSites"]), 1)
        self.assertEqual(len(configured["simpSites"]), 0)
        self.assertEqual(len(disch["simpSites"]), 1)
        self.assertEqual(len(multi["simpSites"]), 2)
        self.assertEqual(let_typed["theoremBodyForm"], "term")
        self.assertTrue(SIMP_INVENTORY_FIXTURE[
            let_typed["theoremBody"]["startChar"]:
            let_typed["theoremBody"]["endChar"]].startswith("by simp"))
        self.assertEqual(structured["theoremBodyForm"], "whereStructInst")
        self.assertTrue(SIMP_INVENTORY_FIXTURE[
            structured["theoremBody"]["startChar"]:
            structured["theoremBody"]["endChar"]].startswith("where"))
        self.assertEqual(equations["theoremBodyForm"], "equations")
        self.assertTrue(SIMP_INVENTORY_FIXTURE[
            equations["theoremBody"]["startChar"]:
            equations["theoremBody"]["endChar"]].lstrip().startswith("| 0"))
        direct_spans = [
            SIMP_INVENTORY_FIXTURE[site["startChar"]:site["endChar"]]
            for command in commands for site in command["simpSites"]
        ]
        self.assertEqual(sum(len(command["simpSites"]) for command in commands), 12)
        self.assertEqual(direct_spans.count("simp"), 11)
        self.assertEqual(sum(span.startswith("simp only") for span in direct_spans), 1)

    def test_success_postcondition_checks_the_full_owned_command(self) -> None:
        source = SIMP_INVENTORY_FIXTURE
        inventory = self.simp_inventory
        command_rows = []
        source_bytes = source.encode("utf-8")
        for command in inventory["commands"]:
            start, stop = command["startByte"], command["endByte"]
            command_rows.append({
                "ordinal": command["commandOrdinal"],
                "start": start,
                "end": stop,
                "kind": command["kind"],
                "sha256": hashlib.sha256(source_bytes[start:stop]).hexdigest(),
            })
        body_ordinal = next(command["commandOrdinal"] for command in inventory["commands"]
                            if "theorem body" in source[
                                command["startChar"]:command["endChar"]])
        config_ordinal = next(command["commandOrdinal"] for command in inventory["commands"]
                              if "theorem configured" in source[
                                  command["startChar"]:command["endChar"]])
        def cached_inventory(modules, *, repo_root=ast.ROOT):
            self.assertEqual([entry["module"] for entry in modules], [
                "Mathlib.SimpCommandInventoryFixture",
                "Mathlib.SimpCommandInventoryFixture",
            ])
            self.assertEqual([entry["source"] for entry in modules], [
                source, self.simp_candidate_with_import,
            ])
            return [self.simp_inventory, self.simp_candidate_inventory]

        with patch.object(ast, "inventory_simp_tactics_batch", side_effect=cached_inventory):
            with self.assertRaisesRegex(ast.SyntaxExtractionError, "still owns executable simp"):
                ast.assert_success_commands_have_no_simp(
                    module="Mathlib.SimpCommandInventoryFixture",
                    original_source=source,
                    candidate_source=self.simp_candidate_with_import,
                    expected_source_sha256=self.simp_inventory_digest,
                    command_rows=command_rows,
                    success_ordinals={body_ordinal},
                    candidate_replacements={body_ordinal: source_bytes[
                        command_rows[body_ordinal]["start"]:
                        command_rows[body_ordinal]["end"]
                    ].decode("utf-8")},
                )
            ast.assert_success_commands_have_no_simp(
                module="Mathlib.SimpCommandInventoryFixture",
                original_source=source,
                candidate_source=self.simp_candidate_with_import,
                    expected_source_sha256=self.simp_inventory_digest,
                    command_rows=command_rows,
                    success_ordinals={config_ordinal},
                    candidate_replacements={config_ordinal: source_bytes[
                        command_rows[config_ordinal]["start"]:
                        command_rows[config_ordinal]["end"]
                    ].decode("utf-8")},
                )


class TermElaborationExtensionGateChecks(unittest.TestCase):
    def _inspect(self, module: str, source: str) -> dict:
        temp = tempfile.TemporaryDirectory(prefix="term-extension-category-")
        self.addCleanup(temp.cleanup)
        path = Path(temp.name) / "ExtensionFixture.lean"
        path.write_text(source, encoding="utf-8")
        return ast.inspect_term_elaboration_boundary(
            module=module, source_path=path,
            expected_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
            repo_root=ast.ROOT, require_pinned_path=False,
        )

    def test_existing_term_extension_refusals_keep_their_classification(self) -> None:
        source = '''import Lean
syntax "hiddenSyntax" : term
macro "hiddenMacro" : term => `(0)
macro_rules | `(term| (1 + 0)) => `(1)
elab "hiddenElab" : term => `(0)
elab_rules : term | `(hiddenSyntax) => `(0)
@[term_elab Lean.Parser.Term.ident]
def hiddenIdentElab : Lean.Elab.Term.TermElab := fun _ _ => do
  Lean.Meta.Simp.simpGoal (← Lean.Elab.Term.getMainGoal)
initialize hiddenExtensionRegistrationProbe : IO Unit := pure ()
run_cmd pure ()
attribute [term_elab] hiddenIdentElab
'''
        result = self._inspect("Mathlib.T77ExistingTermExtensions", source)
        self.assertEqual(result["status"], "refused", result)
        self.assertEqual(
            [risk["reason"] for risk in result["risks"]],
            [
                "source_term_syntax",
                "source_term_macro_or_elaborator",
                "source_term_macro_rules",
                "source_term_macro_or_elaborator",
                "source_term_macro_or_elaborator",
                "source_term_elab_attribute",
                "source_command_can_register_term_extension",
                "source_command_can_register_term_extension",
                "source_term_elab_attribute",
            ],
        )

    def test_command_elaborator_meta_simp_is_refused_before_full_compile(self) -> None:
        source = '''import Lean
import Lean.Meta.Tactic.Simp
open Lean Elab Command
syntax "t77HiddenCommand" : command
elab_rules : command
  | `(t77HiddenCommand) => do
      liftTermElabM do
        let termStx ← `(term| 1 + 0)
        let e ← Lean.Elab.Term.elabTerm termStx none
        let ctx ← Lean.Meta.Simp.Context.mkDefault
        let _ ← Lean.Meta.simp e ctx
      liftIO <| IO.println "T77_COMMAND_ELAB_EXECUTED"
t77HiddenCommand
'''
        with tempfile.TemporaryDirectory(prefix="term-command-elab-compile-") as temp:
            path = Path(temp) / "CommandElab.lean"
            path.write_text(source, encoding="utf-8")
            result = ast.inspect_term_elaboration_boundary(
                module="Mathlib.T77CommandElabProbe", source_path=path,
                expected_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                repo_root=ast.ROOT, require_pinned_path=False,
            )
            self.assertEqual(result["status"], "refused", result)
            self.assertEqual(
                [(risk["reason"], risk.get("category")) for risk in result["risks"]],
                [("source_command_macro_or_elaborator", "command")],
            )

            # Recompiling the same full source really runs the extension.  The
            # gate must refuse before the campaign's isolated candidate
            # compiler reaches this command.
            compiled = subprocess.run(
                ["lake", "env", "lean", str(path)], cwd=ast.ROOT,
                text=True, capture_output=True, check=False, timeout=30,
            )
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            self.assertIn("T77_COMMAND_ELAB_EXECUTED", compiled.stdout)

    def test_macro_and_elaborator_commands_are_refused_across_categories(self) -> None:
        source = '''import Lean
syntax "t77CommandMacro" : command
macro "t77CommandMacro" : command => `(command| #check Nat)
syntax "t77TacticMacro" : tactic
macro "t77TacticMacro" : tactic => `(tactic| skip)
syntax "t77CommandMacroRules" : command
macro_rules
  | `(t77CommandMacroRules) => `(command| #check Nat)
syntax "t77TacticMacroRules" : tactic
macro_rules
  | `(tactic| t77TacticMacroRules) => `(tactic| skip)
elab "t77TermElab" : term => `(0)
elab "t77CommandElab" : command => pure ()
elab "t77TacticElab" : tactic => throwUnsupportedSyntax
elab "t77DoElemElab" : doElem => throwUnsupportedSyntax
elab "t77UnknownCategoryElab" : t77UnknownCategory => throwUnsupportedSyntax
syntax "t77CommandElabRules" : command
syntax "t77TacticElabRules" : tactic
elab_rules : command
  | `(t77CommandElabRules) => pure ()
elab_rules : tactic
  | `(tactic| t77TacticElabRules) => throwUnsupportedSyntax
'''
        result = self._inspect("Mathlib.T77ExtensionCategories", source)
        self.assertEqual(result["status"], "refused", result)
        self.assertEqual(
            [(risk["reason"], risk.get("category")) for risk in result["risks"]],
            [
                ("source_command_macro_or_elaborator", "command"),
                ("source_tactic_macro_or_elaborator", "tactic"),
                ("source_macro_rules_any_category", None),
                ("source_macro_rules_any_category", None),
                ("source_term_macro_or_elaborator", "term"),
                ("source_command_macro_or_elaborator", "command"),
                ("source_tactic_macro_or_elaborator", "tactic"),
                ("source_doElem_macro_or_elaborator", "doElem"),
                ("source_t77UnknownCategory_macro_or_elaborator", "t77UnknownCategory"),
                ("source_command_macro_or_elaborator", "command"),
                ("source_tactic_macro_or_elaborator", "tactic"),
            ],
        )

    def test_extension_registration_attributes_cover_command_tactic_and_macro(self) -> None:
        source = '''import Lean
syntax (name := t77AttributeCommandKind) "t77AttributeCommand" : command
syntax (name := t77AttributeTacticKind) "t77AttributeTactic" : tactic
@[command_elab t77AttributeCommandKind]
def t77CommandExtension : Lean.Elab.Command.CommandElab := fun _ => pure ()
@[tactic t77AttributeTacticKind]
def t77TacticExtension : Lean.Elab.Tactic.Tactic := fun _ => pure ()
attribute [builtin_command_elab t77AttributeCommandKind] t77CommandExtension
attribute [macro t77AttributeCommandKind] t77CommandExtension
'''
        result = self._inspect("Mathlib.T77ExtensionAttributes", source)
        self.assertEqual(result["status"], "refused", result)
        self.assertEqual(
            [(risk["reason"], risk.get("attribute")) for risk in result["risks"]],
            [
                ("source_command_elab_attribute", "command_elab"),
                ("source_tactic_elab_attribute", "tactic"),
                ("source_command_elab_attribute", "builtin_command_elab"),
                ("source_macro_attribute", "macro"),
            ],
        )

    def test_specialized_elaborator_attributes_are_refused(self) -> None:
        source = '''import Lean
@[builtin_inductive_elab Lean.Parser.Command.inductive]
def t77BuiltinInductiveExtension : Lean.Elab.Command.InductiveElabDescr := default
attribute [inductive_elab Lean.Parser.Command.structure] t77BuiltinInductiveExtension
attribute [builtin_doElem_control_info Lean.Parser.Term.doExpr] t77BuiltinInductiveExtension
attribute [doElem_control_info Lean.Parser.Term.doExpr] t77BuiltinInductiveExtension
attribute [quot_precheck Lean.Parser.Term.num] t77BuiltinInductiveExtension
attribute [builtin_quot_precheck Lean.Parser.Term.num] t77BuiltinInductiveExtension
attribute [grind_tactic Lean.Parser.Tactic.Grind.atom] t77BuiltinInductiveExtension
attribute [builtin_grind_tactic Lean.Parser.Tactic.Grind.atom] t77BuiltinInductiveExtension
attribute [try_tactic Lean.Parser.Tactic.exact] t77BuiltinInductiveExtension
attribute [builtin_try_tactic Lean.Parser.Tactic.exact] t77BuiltinInductiveExtension
attribute [sym_simproc Lean.Parser.Sym.Simp.control] t77BuiltinInductiveExtension
attribute [builtin_sym_simproc Lean.Parser.Sym.Simp.control] t77BuiltinInductiveExtension
attribute [sym_discharger Lean.Parser.Sym.Simp.control] t77BuiltinInductiveExtension
attribute [builtin_sym_discharger Lean.Parser.Sym.Simp.control] t77BuiltinInductiveExtension
attribute [sym_dsimproc Lean.Parser.Sym.Simp.control] t77BuiltinInductiveExtension
attribute [builtin_sym_dsimproc Lean.Parser.Sym.Simp.control] t77BuiltinInductiveExtension
attribute [try_suggestion] t77BuiltinInductiveExtension
'''
        result = self._inspect("Mathlib.T77SpecializedExtensionAttributes", source)
        self.assertEqual(result["status"], "refused", result)
        self.assertEqual(
            [(risk["reason"], risk.get("attribute")) for risk in result["risks"]],
            [
                ("source_inductive_elab_attribute", "builtin_inductive_elab"),
                ("source_inductive_elab_attribute", "inductive_elab"),
                ("source_do_control_info_attribute", "builtin_doElem_control_info"),
                ("source_do_control_info_attribute", "doElem_control_info"),
                ("source_quotation_precheck_attribute", "quot_precheck"),
                ("source_quotation_precheck_attribute", "builtin_quot_precheck"),
                ("source_grind_tactic_attribute", "grind_tactic"),
                ("source_grind_tactic_attribute", "builtin_grind_tactic"),
                ("source_try_tactic_attribute", "try_tactic"),
                ("source_try_tactic_attribute", "builtin_try_tactic"),
                ("source_sym_simproc_attribute", "sym_simproc"),
                ("source_sym_simproc_attribute", "builtin_sym_simproc"),
                ("source_sym_discharger_attribute", "sym_discharger"),
                ("source_sym_discharger_attribute", "builtin_sym_discharger"),
                ("source_sym_dsimproc_attribute", "sym_dsimproc"),
                ("source_sym_dsimproc_attribute", "builtin_sym_dsimproc"),
                ("source_try_suggestion_attribute", "try_suggestion"),
            ],
        )

    def test_passive_command_and_tactic_syntax_remain_allowed(self) -> None:
        source = '''import Lean
syntax "t77ParserOnlyCommand" : command
syntax "t77ParserOnlyTactic" : tactic
def parserNameIsOnlyAValue (term_parser : Nat) : Nat := term_parser
def term_elab : Nat := 1
def command_elab : Nat := term_elab
def quotedParserAttribute := `(attr| term_parser)
def quotedElaboratorAttribute := `(attr| command_elab)
'''
        result = self._inspect("Mathlib.T77ParserOnly", source)
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["risks"], [])

    def test_parser_registration_and_hook_attributes_are_refused(self) -> None:
        source = '''import Lean
@[builtin_term_parser] def t77HiddenTermParser : Lean.Parser.Parser :=
  leading_parser:leadPrec "t77_hidden_term"
def t77HiddenCommandParser : Lean.Parser.Parser :=
  leading_parser "t77_hidden_command"
attribute [command_parser] t77HiddenCommandParser
attribute [builtin_command_parser] t77HiddenCommandParser
attribute [term_parser] t77HiddenCommandParser
def t77HiddenTacticParser : Lean.Parser.Parser :=
  leading_parser "t77_hidden_tactic"
attribute [builtin_tactic_parser] t77HiddenTacticParser
attribute [tactic_parser] t77HiddenTacticParser
def t77HiddenDoElemParser : Lean.Parser.Parser :=
  leading_parser "t77_hidden_doElem"
attribute [doElem_parser] t77HiddenDoElemParser
attribute [builtin_doElem_parser] t77HiddenDoElemParser
attribute [builtin_level_parser] t77HiddenDoElemParser
attribute [builtin_syntax_parser] t77HiddenDoElemParser
attribute [stx_parser] t77HiddenDoElemParser
attribute [builtin_prec_parser] t77HiddenDoElemParser
attribute [prec_parser] t77HiddenDoElemParser
attribute [builtin_attr_parser] t77HiddenDoElemParser
attribute [attr_parser] t77HiddenDoElemParser
attribute [builtin_prio_parser] t77HiddenDoElemParser
attribute [prio_parser] t77HiddenDoElemParser
attribute [builtin_structInstFieldDecl_parser] t77HiddenDoElemParser
attribute [run_parser_attribute_hooks] t77HiddenTermParser
attribute [run_builtin_parser_attribute_hooks] t77HiddenTermParser
'''
        result = self._inspect("Mathlib.T77ParserRegistrationAttributes", source)
        self.assertEqual(result["status"], "refused", result)
        self.assertEqual(
            [(risk["reason"], risk.get("attribute")) for risk in result["risks"]],
            [
                ("source_parser_attribute", "builtin_term_parser"),
                ("source_parser_attribute", "command_parser"),
                ("source_parser_attribute", "builtin_command_parser"),
                ("source_parser_attribute", "term_parser"),
                ("source_parser_attribute", "builtin_tactic_parser"),
                ("source_parser_attribute", "tactic_parser"),
                ("source_parser_attribute", "doElem_parser"),
                ("source_parser_attribute", "builtin_doElem_parser"),
                ("source_parser_attribute", "builtin_level_parser"),
                ("source_parser_attribute", "builtin_syntax_parser"),
                ("source_parser_attribute", "stx_parser"),
                ("source_parser_attribute", "builtin_prec_parser"),
                ("source_parser_attribute", "prec_parser"),
                ("source_parser_attribute", "builtin_attr_parser"),
                ("source_parser_attribute", "attr_parser"),
                ("source_parser_attribute", "builtin_prio_parser"),
                ("source_parser_attribute", "prio_parser"),
                ("source_parser_attribute", "builtin_structInstFieldDecl_parser"),
                ("source_parser_attribute_hook", "run_parser_attribute_hooks"),
                ("source_parser_attribute_hook", "run_builtin_parser_attribute_hooks"),
            ],
        )


if __name__ == "__main__":
    unittest.main()
