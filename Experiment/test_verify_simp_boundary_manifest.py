#!/usr/bin/env python3
"""Adversarial fixtures for the generic boundary-manifest verifier."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

import verify_simp_boundary_manifest as verifier


class ManifestVerifierTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="fresh-boundary-verifier-")
        self.root = Path(self.temp.name)
        self.mathlib = self.root / "mathlib"
        self.source_path = self.mathlib / "Mathlib" / "A.lean"
        self.source_path.parent.mkdir(parents=True)
        source = b"theorem a : True := by simp\n"
        self.source_path.write_bytes(source)
        self.repository = self.root / "repo"
        self.repository.mkdir()
        implementation = self.repository / "tool.py"
        implementation.write_bytes(b"stable implementation\n")
        self.source = source
        start = source.index(b"simp")
        end = start + len(b"simp")
        module = "Mathlib/A.lean"
        compiled = "Mathlib.A"
        occurrence = {
            "id": verifier.inventory.occurrence_id(module, start, end),
            "kind": "simp",
            "source": "simp",
            "startByte": start,
            "endByte": end,
            "line": 1,
            "column": start,
            "syntaxKind": "Lean.Parser.Tactic.simp",
            "ancestors": ["Lean.Parser.Tactic.simp"],
            "commandKind": "Lean.Parser.Command.theorem",
            "commandStartByte": 0,
            "commandEndByte": len(source),
            "scopePaths": [{
                "ancestors": ["Lean.Parser.Tactic.simp"],
                "commandKind": "Lean.Parser.Command.theorem",
                "commandStartByte": 0,
                "commandEndByte": len(source),
            }],
            "executionRole": "direct_executable",
            "declarationKind": "proof",
            "action": "materialize",
            "reason": "fixture proof declaration",
            "declarations": [{
                "module": compiled,
                "name": "a",
                "startByte": 0,
                "endByte": len(source),
                "selectionStartByte": 0,
                "selectionEndByte": 10,
                "isProof": True,
            }],
        }
        self.manifest = {
            "reportSchema": verifier.SCHEMA,
            "kind": verifier.KIND,
            "allowDirty": False,
            "allowUnresolved": False,
            "repositoryCommit": "a" * 40,
            "mathlibCommit": "b" * 40,
            "lean": {"version": "4.32.2", "commit": "c" * 40},
            "modulePrefix": "Mathlib/",
            "moduleFileCount": 1,
            "inventoriedModuleCount": 1,
            "occurrenceCount": 1,
            "nestedOccurrenceCount": 0,
            "duplicateSyntaxRecords": 0,
            "duplicateScopeSyntaxRecords": 0,
            "fullFrontendFallbacks": [],
            "scopeFrontendFallbacks": [],
            "scopeProbe": {
                "module": verifier.scope.SCOPE_PROBE_IMPORT,
                "scheduling": verifier.scope.SCOPE_PROBE_SCHEDULING,
                "temporaryCopyOnly": True,
                "reportCommand": "simp_engine_boundary_scope_report",
            },
            "countsByExecutionRole": {"direct_executable": 1},
            "countsByDeclarationKind": {"proof": 1},
            "countsByAction": {"materialize": 1},
            "implementationHashes": {"tool.py": hashlib.sha256(implementation.read_bytes()).hexdigest()},
            "manualOverrides": {
                "sha256": "d" * 64,
                "schema": 1,
                "environment": {
                    "mathlibCommit": "b" * 40,
                    "lean": {"version": "4.32.2", "commit": "c" * 40},
                },
            },
            "modules": [{
                "module": module,
                "compiledModule": compiled,
                "moduleHash": hashlib.sha256(module.encode()).hexdigest(),
                "sourceHash": hashlib.sha256(source).hexdigest(),
                "duplicateSyntaxRecords": 0,
                "duplicateScopeSyntaxRecords": 0,
                "occurrences": [occurrence],
            }],
        }
        self.path = self.root / "manifest.json"
        self.write()

    def tearDown(self) -> None:
        self.temp.cleanup()

    def write(self) -> None:
        self.path.write_text(json.dumps(self.manifest, sort_keys=True), encoding="utf-8")

    def verify(self, *, complete: bool = False) -> None:
        verifier.verify_manifest(
            self.path,
            repository_root=self.repository,
            mathlib_root=self.mathlib,
            require_complete=complete,
            check_environment=False,
        )

    def rejects(self, needle: str) -> None:
        with self.assertRaisesRegex(RuntimeError, needle):
            self.verify()

    def test_valid_fixture_and_self_hash(self) -> None:
        self.verify()
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        occurrence["commandKind"] = None
        occurrence["commandStartByte"] = None
        occurrence["commandEndByte"] = None
        for path in occurrence["scopePaths"]:
            path["commandKind"] = None
            path["commandStartByte"] = None
            path["commandEndByte"] = None
        self.write()
        self.verify()
        payload = copy.deepcopy(self.manifest)
        payload["selfHash"] = verifier.sha256(verifier.canonical_json(payload))
        self.manifest = payload
        self.write()
        self.verify()

    def test_self_hash_schema_kind_and_unknown_fields_fail_closed(self) -> None:
        self.manifest["selfHash"] = "0" * 64
        self.write()
        self.rejects("selfHash")
        self.manifest.pop("selfHash")
        self.manifest["kind"] = "other"
        self.write()
        self.rejects("kind")
        self.manifest["kind"] = verifier.KIND
        self.manifest["unexpected"] = True
        self.write()
        self.rejects("fields changed")
        self.manifest.pop("unexpected")
        self.manifest["reportSchema"] = 2.0
        self.write()
        self.rejects("schema")

        self.manifest["reportSchema"] = verifier.SCHEMA
        self.manifest["manifestHash"] = "0" * 64
        self.write()
        self.rejects("manifestHash")

        self.manifest.pop("manifestHash")
        self.manifest["selfHash"] = "A" * 64
        self.write()
        self.rejects("selfHash")

    def test_source_hash_range_text_and_id_are_bound(self) -> None:
        for mutation, needle in (
            (lambda: self.manifest["modules"][0].update(sourceHash="0" * 64), "sourceHash"),
            (lambda: self.manifest["modules"][0]["occurrences"][0].update(source="simp?"), "stale occurrence source"),
            (lambda: self.manifest["modules"][0]["occurrences"][0].update(endByte=999), "invalid occurrence range"),
            (lambda: self.manifest["modules"][0]["occurrences"][0].update(id="0" * 16), "occurrence ID"),
        ):
            original = copy.deepcopy(self.manifest)
            mutation()
            self.write()
            self.rejects(needle)
            self.manifest = original

    def test_paths_duplicates_missing_and_counts_fail_closed(self) -> None:
        original = copy.deepcopy(self.manifest)
        self.manifest["modules"][0]["module"] = "Mathlib/../Outside.lean"
        self.write(); self.rejects("module path")
        self.manifest = copy.deepcopy(original)
        self.manifest["modules"].append(copy.deepcopy(self.manifest["modules"][0]))
        self.write(); self.rejects("duplicate module")
        self.manifest = copy.deepcopy(original)
        self.manifest["occurrenceCount"] = 2
        self.write(); self.rejects("counts")
        self.manifest = copy.deepcopy(original)
        self.write()
        self.verify()
        self.manifest["moduleFileCount"] = 2
        self.write(); self.rejects("counts")

    def test_scope_action_declaration_and_unresolved_policy_fail_closed(self) -> None:
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        occurrence["action"] = "retain"
        self.write(); self.rejects("scope dimensions")
        occurrence["action"] = "materialize"
        occurrence["declarations"][0]["module"] = "Other.A"
        self.write(); self.rejects("disagrees")
        occurrence["declarations"][0]["module"] = "Mathlib.A"
        occurrence["executionRole"] = "unresolved"
        occurrence["declarationKind"] = "unknown"
        occurrence["action"] = "unresolved"
        self.manifest["countsByExecutionRole"] = {"unresolved": 1}
        self.manifest["countsByDeclarationKind"] = {"unknown": 1}
        self.manifest["countsByAction"] = {"unresolved": 1}
        self.write(); self.rejects("unresolved occurrences")

    def test_command_containment_and_is_proof_mutations_fail_closed(self) -> None:
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        occurrence["commandStartByte"] = occurrence["endByte"] + 1
        occurrence["scopePaths"][0]["commandStartByte"] = occurrence["commandStartByte"]
        self.write(); self.rejects("outside command range")
        occurrence["commandStartByte"] = 0
        occurrence["scopePaths"][0]["commandStartByte"] = 0
        occurrence["declarations"][0]["isProof"] = False
        self.write(); self.rejects("proof classification")
        occurrence["declarations"][0]["isProof"] = True
        occurrence["declarations"] = []
        self.write(); self.rejects("scope declaration list is empty")

    def test_execution_evidence_shape_is_checked(self) -> None:
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        occurrence["executionEvidence"] = {
            "status": "complete_proof_declaration",
            "executionCount": True,
            "callers": [],
            "module": "Mathlib.A",
            "scheduling": verifier.scope.SCOPE_PROBE_SCHEDULING,
        }
        self.write(); self.rejects("executionCount")

    def test_inventory_fallback_mismatch_is_rejected(self) -> None:
        output = json.dumps({
            "file": str(self.source_path),
            "kind": "simp",
            "startByte": self.source.index(b"simp"),
            "endByte": self.source.index(b"simp") + 4,
            "line": 1,
            "column": self.source.index(b"simp"),
            "syntaxKind": "Lean.Parser.Tactic.simp",
            "source": "simp",
        })
        result = SimpleNamespace(returncode=0, stdout="SIMP_ENGINE_INVENTORY_FULL_FALLBACK file=" + str(self.source_path) + "\n" + output + "\n")
        with patch("subprocess.run", return_value=result), patch.object(
            verifier, "_freshness_snapshot", return_value={}
        ):
            with self.assertRaisesRegex(RuntimeError, "fallback set differs"):
                verifier.recompute_inventory(
                    self.path,
                    mathlib_root=self.mathlib,
                    repository_root=self.repository,
                )

    def test_freshness_guard_rejects_changed_inputs(self) -> None:
        before = {"manifest": "before", "sources": {}, "implementation": {}}
        after = {"manifest": "after", "sources": {}, "implementation": {}}
        with patch.object(verifier, "_freshness_snapshot", return_value=after):
            with self.assertRaisesRegex(RuntimeError, "changed authenticated inputs"):
                verifier._assert_fresh(
                    before,
                    self.path,
                    self.manifest,
                    self.repository,
                    self.mathlib,
                    "fixture subprocess",
                )

    def test_inspection_flags_are_not_available_on_acceptance_command(self) -> None:
        with patch("sys.argv", ["verify_simp_boundary_manifest.py", "accept", str(self.path), "--skip-environment"]):
            with self.assertRaises(SystemExit) as result:
                verifier.main()
        self.assertEqual(result.exception.code, 2)

    def test_acceptance_api_requires_authenticated_digest(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "authenticated digest"):
            verifier.verify_manifest(
                self.path,
                repository_root=self.repository,
                mathlib_root=self.mathlib,
                require_complete=False,
                check_environment=False,
                require_authenticated_digest=True,
            )

    def test_implementation_and_manual_identity_are_checked(self) -> None:
        self.manifest["implementationHashes"]["tool.py"] = "0" * 64
        self.write(); self.rejects("implementationHashes")
        self.manifest["implementationHashes"]["tool.py"] = hashlib.sha256(b"stable implementation\n").hexdigest()
        self.manifest["manualOverrides"]["schema"] = 2
        self.write(); self.rejects("manualOverrides.schema")

    def test_exposed_package_identity_has_a_closed_shape(self) -> None:
        self.manifest["packageIdentity"] = {
            "manifestSha256": "e" * 64,
            "packages": [{"name": "mathlib", "type": "git", "rev": "b" * 40}],
        }
        self.write(); self.verify()
        self.manifest["packageIdentity"]["packages"][0]["rev"] = "bad"
        self.write(); self.rejects(r"packageIdentity.packages\[0\].*rev")

    def test_supplied_repository_commit_is_exactly_compared(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "repositoryCommit"):
            verifier.verify_manifest(
                self.path,
                repository_root=self.repository,
                mathlib_root=self.mathlib,
                expected_repository_commit="f" * 40,
                require_complete=False,
                check_environment=False,
            )

    def test_whole_mode_rejects_missing_module_even_when_counts_match(self) -> None:
        self.verify()
        (self.mathlib / "Mathlib" / "B.lean").write_bytes(b"theorem b : True := by trivial\n")
        with self.assertRaisesRegex(RuntimeError, "whole-corpus set differs"):
            verifier.verify_manifest(
                self.path,
                repository_root=self.repository,
                mathlib_root=self.mathlib,
                require_complete=True,
                check_environment=False,
            )


if __name__ == "__main__":
    unittest.main()
