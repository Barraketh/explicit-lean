#!/usr/bin/env python3
"""Adversarial fixtures for the generic boundary-manifest verifier."""

from __future__ import annotations

import copy
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import inspect
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

    def test_irreducible_computation_may_include_its_proof_helper(self) -> None:
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        occurrence["declarationKind"] = "computational"
        occurrence["declarations"][0]["isProof"] = False
        proof_helper = copy.deepcopy(occurrence["declarations"][0])
        proof_helper["name"] = "a_def"
        proof_helper["isProof"] = True
        occurrence["declarations"].append(proof_helper)
        self.manifest["countsByDeclarationKind"] = {"computational": 1}
        self.write(); self.rejects("computational classification")

        occurrence["ancestors"].insert(
            0, "Lean.Elab.Command.command_Irreducible_def____"
        )
        self.write(); self.verify()

        occurrence["declarations"][0]["isProof"] = True
        self.write(); self.rejects("computational classification")

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

    def test_unnamed_example_proof_may_use_valid_execution_evidence(self) -> None:
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        occurrence["commandKind"] = "Lean.Parser.Command.example"
        occurrence["scopePaths"][0]["commandKind"] = "Lean.Parser.Command.example"
        occurrence["declarations"] = []
        occurrence["executionEvidence"] = {
            "status": "complete_proof_declaration",
            "executionCount": 1,
            "callers": [{
                "caller": "_private.Mathlib.A.0.simpEngineScopeExample_fixture",
                "executionCount": 1,
                "isProofDeclaration": True,
            }],
            "module": "Mathlib.A",
            "scheduling": verifier.scope.SCOPE_PROBE_SCHEDULING,
        }
        self.write(); self.verify()

    def test_empty_proof_owner_exception_is_narrow_and_fail_closed(self) -> None:
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        proof_declarations = copy.deepcopy(occurrence["declarations"])
        occurrence["commandKind"] = "Lean.Parser.Command.example"
        occurrence["scopePaths"][0]["commandKind"] = "Lean.Parser.Command.example"
        occurrence["declarations"] = []
        original = copy.deepcopy(occurrence)

        self.write(); self.rejects("scope declaration list is empty")

        occurrence["executionEvidence"] = {
            "status": "complete_nonproof_declaration",
            "executionCount": 1,
            "callers": [{
                "caller": "forged",
                "executionCount": 1,
                "isProofDeclaration": False,
            }],
            "module": "Mathlib.A",
            "scheduling": verifier.scope.SCOPE_PROBE_SCHEDULING,
        }
        self.write(); self.rejects("scope declaration list is empty")

        occurrence["executionEvidence"] = {
            "status": "complete_proof_declaration",
            "executionCount": 1,
            "callers": [{
                "caller": "a",
                "executionCount": 1,
                "isProofDeclaration": True,
            }],
            "module": "Mathlib.A",
            "scheduling": verifier.scope.SCOPE_PROBE_SCHEDULING,
        }
        occurrence["declarations"] = proof_declarations
        occurrence["declarations"][0]["isProof"] = False
        self.write(); self.rejects("proof classification")

        self.manifest["modules"][0]["occurrences"][0] = copy.deepcopy(original)
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        occurrence["commandKind"] = "Lean.Parser.Command.theorem"
        occurrence["scopePaths"][0]["commandKind"] = "Lean.Parser.Command.theorem"
        occurrence["executionEvidence"] = {
            "status": "complete_proof_declaration",
            "executionCount": 1,
            "callers": [{
                "caller": "a",
                "executionCount": 1,
                "isProofDeclaration": True,
            }],
            "module": "Mathlib.A",
            "scheduling": verifier.scope.SCOPE_PROBE_SCHEDULING,
        }
        self.write(); self.rejects("scope declaration list is empty")

    def test_variable_signature_may_have_no_compiled_owner(self) -> None:
        occurrence = self.manifest["modules"][0]["occurrences"][0]
        occurrence["commandKind"] = "Lean.Parser.Command.variable"
        occurrence["scopePaths"][0]["commandKind"] = "Lean.Parser.Command.variable"
        occurrence["declarationKind"] = "signature_or_default"
        occurrence["declarations"] = []
        self.manifest["countsByDeclarationKind"] = {"signature_or_default": 1}
        self.write(); self.verify()

        occurrence["commandKind"] = "Lean.Parser.Command.theorem"
        occurrence["scopePaths"][0]["commandKind"] = "Lean.Parser.Command.theorem"
        self.write(); self.rejects("scope declaration list is empty")

        occurrence["commandKind"] = "Lean.Parser.Command.variable"
        occurrence["scopePaths"][0]["commandKind"] = "Lean.Parser.Command.variable"
        occurrence["executionEvidence"] = {
            "status": "missing_execution",
            "executionCount": 0,
            "callers": [],
            "module": None,
            "scheduling": verifier.scope.SCOPE_PROBE_SCHEDULING,
        }
        self.write(); self.rejects("scope declaration list is empty")

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
            verifier, "run_process", return_value=result
        ), patch.object(verifier, "_freshness_snapshot", return_value={}):
            with self.assertRaisesRegex(RuntimeError, "fallback set differs"):
                verifier.recompute_inventory(
                    self.path,
                    mathlib_root=self.mathlib,
                    repository_root=self.repository,
                )

    def test_fresh_inventory_is_split_into_bounded_processes(self) -> None:
        paths = [self.root / f"Module{i}.lean" for i in range(129)]
        completed = SimpleNamespace(returncode=0, stdout="")
        with patch.object(verifier, "run_process", return_value=completed) as run:
            outputs = verifier._run_fresh_inventory_batches(
                paths, repository=self.repository, timeout=60
            )
        self.assertEqual(outputs, [""] * 129)
        commands = [call.args[0] for call in run.call_args_list]
        self.assertEqual([len(command[4:]) for command in commands], [1] * 129)
        self.assertTrue(all(
            command[3] == "--header-imports" for command in commands
        ))

    def test_fresh_inventory_batches_follow_transitive_import_closure(self) -> None:
        modules = ["Mathlib/A.lean", "Mathlib/B.lean", "Mathlib/C.lean", "Mathlib/D.lean"]
        paths = []
        for module in modules:
            path = self.mathlib / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"module\n-- {module}\n", encoding="utf-8")
            paths.append(path)
        def entry(module: str, imports: list[str]) -> tuple[str, dict[str, object]]:
            digest = verifier.sha256((self.mathlib / module).read_bytes())
            return f"{module}@{digest}", {
                "module": module, "sourceHash": digest, "dependencies": imports,
            }
        dependency_map = dict([
            entry("Mathlib/A.lean", ["Mathlib.B"]),
            entry("Mathlib/B.lean", ["Mathlib.C"]),
            entry("Mathlib/C.lean", []),
            entry("Mathlib/D.lean", []),
        ])
        batches = verifier._fresh_inventory_batches_by_closure(
            paths, modules, dependency_map=dependency_map, max_import_modules=2
        )
        self.assertEqual([[path.name for path in batch] for batch in batches],
                         [["A.lean"], ["B.lean", "C.lean"], ["D.lean"]])

    def test_fresh_inventory_dependency_map_is_complete_and_source_bound(self) -> None:
        modules = ["Mathlib/A.lean", "Mathlib/B.lean"]
        paths = []
        for module in modules:
            path = self.mathlib / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("module\n", encoding="utf-8")
            paths.append(path)
        def entry(module: str, digest: str | None = None) -> tuple[str, dict[str, object]]:
            actual = verifier.sha256((self.mathlib / module).read_bytes())
            value = actual if digest is None else digest
            return f"{module}@{value}", {
                "module": module, "sourceHash": value, "dependencies": [],
            }
        missing = dict([entry(modules[0])])
        with self.assertRaisesRegex(RuntimeError, "module set differs"):
            verifier._fresh_inventory_batches_by_closure(
                paths, modules, dependency_map=missing, max_import_modules=2
            )
        stale = dict([entry(modules[0], "0" * 64), entry(modules[1])])
        with self.assertRaisesRegex(RuntimeError, "source hash differs"):
            verifier._fresh_inventory_batches_by_closure(
                paths, modules, dependency_map=stale, max_import_modules=2
            )

    def test_fresh_inventory_memory_guard_fails_closed(self) -> None:
        with patch.object(verifier, "_available_memory_bytes", return_value=13 * 1024**3):
            self.assertIsNone(verifier._inventory_memory_guard(1))
        with patch.object(verifier, "_available_memory_bytes", return_value=11 * 1024**3):
            self.assertRegex(verifier._inventory_memory_guard(1) or "", "below the strict verifier reserve")
        with patch.object(verifier, "_available_memory_bytes", side_effect=RuntimeError("no telemetry")):
            self.assertRegex(verifier._inventory_memory_guard(1) or "", "telemetry unavailable")

    def test_fresh_inventory_rejects_dependency_map_change(self) -> None:
        modules = ["Mathlib/A.lean", "Mathlib/B.lean"]
        paths = []
        records = {}
        for module in modules:
            path = self.mathlib / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("module\n", encoding="utf-8")
            paths.append(path)
            digest = verifier.sha256(path.read_bytes())
            records[f"{module}@{digest}"] = {
                "module": module, "sourceHash": digest, "dependencies": [],
            }
        map_path = self.root / "dependency-map.json"
        map_path.write_text(json.dumps(records, sort_keys=True), encoding="utf-8")
        completed = SimpleNamespace(returncode=0, stdout="")
        calls = []
        def mutate_map(*_args, **_kwargs):
            calls.append(True)
            if len(calls) == 1:
                map_path.write_text(json.dumps({"changed": True}), encoding="utf-8")
            return completed
        with patch.object(verifier, "run_process", side_effect=mutate_map):
            with self.assertRaisesRegex(RuntimeError, "dependency map changed"):
                verifier._run_fresh_inventory_batches(
                    paths, repository=self.repository, timeout=60,
                    module_names=modules, dependency_map=map_path,
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

    def test_inspection_flags_are_not_available_on_verify_command(self) -> None:
        digest = verifier.sha256(self.path.read_bytes())
        with patch("sys.argv", [
            "verify_simp_boundary_manifest.py", "verify", str(self.path),
            "--expected-sha256", digest, "--lake-path", str(self.root / "lake"),
            "--expected-lake-sha256", "0" * 64, "--lean-path", str(self.root / "lean"),
            "--expected-lean-sha256", "0" * 64, "--skip-environment",
        ]):
            with self.assertRaises(SystemExit) as result:
                verifier.main()
        self.assertEqual(result.exception.code, 2)

    def test_verify_cli_authenticates_generator_compatible_raw_fixture(self) -> None:
        self.assertEqual(set(self.manifest), verifier.TOP_LEVEL_FIELDS)
        digest = verifier.sha256(self.path.read_bytes())
        summary = {"kind": verifier.KIND, "reportSchema": verifier.SCHEMA, "modules": 1, "occurrences": 1, "actions": {"materialize": 1}}
        with patch("sys.argv", [
            "verify_simp_boundary_manifest.py", "verify", str(self.path),
            "--expected-sha256", digest, "--repository-root", str(self.repository),
            "--mathlib-root", str(self.mathlib), "--lake-path", str(self.root / "lake"),
            "--expected-lake-sha256", "a" * 64, "--lean-path", str(self.root / "lean"),
            "--expected-lean-sha256", "b" * 64,
        ]), patch.object(verifier, "verify_strict", return_value={
            **summary, "kind": "simp_engine_boundary_manifest_source_verification",
            "expectedSha256": digest, "manifestSha256": digest,
            "sourceConsistencyVerified": True, "independentSemanticOracleVerified": False,
        }) as strict, patch("sys.stdout", new_callable=io.StringIO) as output:
            verifier.main()
        strict.assert_called_once()
        receipt = json.loads(output.getvalue())
        self.assertEqual(receipt["kind"], "simp_engine_boundary_manifest_source_verification")
        self.assertEqual(receipt["expectedSha256"], digest)
        self.assertEqual(receipt["manifestSha256"], digest)
        self.assertTrue(receipt["sourceConsistencyVerified"])
        self.assertFalse(receipt["independentSemanticOracleVerified"])
        self.assertNotIn("accepted", receipt)

    def test_expected_digest_is_checked_before_json_parsing(self) -> None:
        self.path.write_bytes(b"not json\n")
        with self.assertRaisesRegex(RuntimeError, "expected-sha256"):
            verifier.verify_raw_manifest_digest(self.path, "0" * 64)
        self.write()
        self.path.write_bytes(b"not json\n")
        with patch("sys.argv", [
            "verify_simp_boundary_manifest.py", "verify", str(self.path),
            "--expected-sha256", "0" * 64, "--repository-root", str(self.repository),
            "--mathlib-root", str(self.mathlib), "--lake-path", str(self.root / "lake"),
            "--expected-lake-sha256", "a" * 64, "--lean-path", str(self.root / "lean"),
            "--expected-lean-sha256", "b" * 64,
        ]), patch.object(verifier, "verify_manifest") as structural:
            with self.assertRaises(SystemExit):
                verifier.main()
        structural.assert_not_called()

    def test_strict_api_has_no_diagnostic_bypass_parameters(self) -> None:
        parameters = inspect.signature(verifier.verify_strict).parameters
        self.assertNotIn("require_complete", parameters)
        self.assertNotIn("check_environment", parameters)
        with self.assertRaises(TypeError):
            verifier.verify_strict(  # type: ignore[call-arg]
                self.path, repository_root=self.repository, mathlib_root=self.mathlib,
                expected_sha256="0" * 64, lake_path=self.root / "lake",
                expected_lake_sha256="0" * 64, lean_path=self.root / "lean",
                expected_lean_sha256="0" * 64, require_complete=False,
            )

    def test_strict_snapshot_catches_replacement_after_initial_read(self) -> None:
        digest = verifier.sha256(self.path.read_bytes())
        replacement = self.path.with_suffix(".replacement")
        replacement.write_bytes(self.path.read_bytes() + b"\n")
        parse_calls = 0
        original_parse = verifier._parse_manifest
        def parse(raw):
            nonlocal parse_calls
            parse_calls += 1
            parsed = original_parse(raw)
            if parse_calls == 1:
                self.path.write_bytes(replacement.read_bytes())
            return parsed
        with patch.object(verifier, "_parse_manifest", side_effect=parse), patch.object(
            verifier, "_verify_manifest", return_value={"kind": verifier.KIND}
        ), patch.object(verifier, "recompute_source_consistency"):
            with self.assertRaisesRegex(RuntimeError, "manifest (path identity|content) changed"):
                verifier.verify_strict(
                    self.path, repository_root=self.repository, mathlib_root=self.mathlib,
                    expected_sha256=digest, lake_path=self.root / "lake",
                    expected_lake_sha256="a" * 64, lean_path=self.root / "lean",
                    expected_lean_sha256="b" * 64,
                )

    def test_scope_recomputation_binds_to_verifier_checkout(self) -> None:
        verifier_root = Path(verifier.__file__).resolve().parents[1]
        with self.assertRaisesRegex(RuntimeError, "bound to the verifier checkout"):
            verifier._fresh_scope_and_declarations(
                self.path, self.manifest, self.repository, self.mathlib, 1
            )
        self.assertEqual(verifier._scope_recompute_root(verifier_root), verifier_root)

    def test_inspection_receipt_has_distinct_nonacceptance_kind(self) -> None:
        with patch("sys.argv", [
            "verify_simp_boundary_manifest.py", "inspect", str(self.path),
            "--repository-root", str(self.repository), "--mathlib-root", str(self.mathlib),
            "--skip-environment",
        ]), patch("sys.stdout", new_callable=io.StringIO) as output:
            verifier.main()
        receipt = json.loads(output.getvalue())
        self.assertEqual(receipt["kind"], "simp_engine_boundary_manifest_inspection")
        self.assertNotIn("accepted", receipt)
        self.assertNotIn("sourceConsistencyVerified", receipt)

    def test_pinned_lake_resolver_rejects_path_shadow_shim(self) -> None:
        (self.repository / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": "mathlib", "type": "git", "rev": "b" * 40}]}),
            encoding="utf-8",
        )
        shadow = self.root / "lake-shadow"
        shadow.write_text("#!/bin/sh\necho shadowed\n", encoding="utf-8")
        shadow.chmod(0o755)
        lean = self.root / "lean"
        lean.write_text("#!/bin/sh\necho shadowed\n", encoding="utf-8")
        lean.chmod(0o755)
        with patch("subprocess.run") as run:
            def shadow_run(args, **kwargs):
                if args[0] == "git" and args[1:3] == ("rev-parse", "HEAD"):
                    value = "b" * 40 if kwargs.get("cwd") == self.mathlib else "a" * 40
                    return SimpleNamespace(returncode=0, stdout=value + "\n")
                return SimpleNamespace(returncode=0, stdout="")
            run.side_effect = shadow_run
            with self.assertRaisesRegex(RuntimeError, "does not contain explicit Lean"):
                verifier._verify_environment(
                    self.manifest, self.repository, self.mathlib, None,
                    lake_path=shadow, expected_lake_sha256=verifier.sha256(shadow.read_bytes()),
                    lean_path=lean, expected_lean_sha256=verifier.sha256(lean.read_bytes()),
                )

    def test_pinned_lake_resolver_positive_identity_control(self) -> None:
        lake_manifest = {"packages": [{"name": "mathlib", "type": "git", "rev": "b" * 40}]}
        (self.repository / "lake-manifest.json").write_text(json.dumps(lake_manifest), encoding="utf-8")
        (self.repository / "lean-toolchain").write_text("leanprover/lean4:v4.32.2\n", encoding="utf-8")
        prefix = self.root / "pinned-toolchain"
        lean = prefix / "bin" / "lean"
        lean.parent.mkdir(parents=True)
        lean.write_text("#!/bin/sh\necho 'Lean (version 4.32.2, commit " + "c" * 40 + ")'\n", encoding="utf-8")
        lean.chmod(0o755)
        lake = self.root / "lake"
        lake.write_text(
            "#!/bin/sh\n"
            "if [ \"$3\" = \"--print-prefix\" ]; then echo '" + str(prefix) + "'; else exec '" + str(lean) + "' --version; fi\n",
            encoding="utf-8",
        )
        lake.chmod(0o755)
        original_run = subprocess.run
        def fake_run(args, **kwargs):
            if args[0] == "git" and args[1:3] == ("rev-parse", "HEAD"):
                value = "a" * 40 if kwargs["cwd"] == self.repository else "b" * 40
                return SimpleNamespace(returncode=0, stdout=value + "\n")
            if args[0] == "git" and args[1] == "status":
                return SimpleNamespace(returncode=0, stdout="")
            return original_run(args, **kwargs)
        with patch("subprocess.run", side_effect=fake_run):
            identity = verifier._verify_environment(
                self.manifest, self.repository, self.mathlib, None,
                lake_path=lake, expected_lake_sha256=verifier.sha256(lake.read_bytes()),
                lean_path=lean, expected_lean_sha256=verifier.sha256(lean.read_bytes()),
            )
        self.assertEqual(identity["leanPath"], str(lean.resolve()))
        self.assertEqual(identity["leanBinarySha256"], verifier.sha256(lean.read_bytes()))

    def test_nonmocked_pinned_environment_bypasses_hostile_lake(self) -> None:
        trusted_dir = self.root / "trusted-bin"
        hostile_dir = self.root / "hostile-bin"
        trusted_dir.mkdir(); hostile_dir.mkdir()
        trusted_marker = self.root / "trusted-called"
        hostile_marker = self.root / "hostile-called"
        trusted = trusted_dir / "lake"
        hostile = hostile_dir / "lake"
        trusted.write_text("#!/bin/sh\necho trusted > '" + str(trusted_marker) + "'\n", encoding="utf-8")
        hostile.write_text("#!/bin/sh\necho hostile > '" + str(hostile_marker) + "'\n", encoding="utf-8")
        trusted.chmod(0o755); hostile.chmod(0o755)
        original_path = os.environ.get("PATH", "")
        os.environ["PATH"] = str(hostile_dir) + os.pathsep + original_path
        try:
            with verifier._pinned_lake_environment(trusted, verifier.sha256(trusted.read_bytes())) as effective:
                result = subprocess.run(["lake"], text=True, stdout=subprocess.PIPE, check=False)
                self.assertEqual(result.returncode, 0)
                self.assertEqual(effective["path"], str(trusted.resolve()))
                self.assertIn(str(trusted_dir.resolve()), [str(Path(entry).resolve()) for entry in effective["PATH"].split(os.pathsep)])
            self.assertTrue(trusted_marker.is_file())
            self.assertFalse(hostile_marker.exists())
        finally:
            os.environ["PATH"] = original_path

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
