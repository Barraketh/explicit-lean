#!/usr/bin/env python3
"""Focused authenticated manifest projection and cleanup checks."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import boundary_materialize_shard as materializer
import campaign_worker as worker
import simp_engine_inventory as inventory
from unittest import mock


class ManifestCapsuleTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="manifest-capsule-")
        self.root = Path(self.temp.name)
        self.source = b"theorem a : True := by simp\n"
        self.module = "Mathlib/A.lean"
        source_path = self.root / self.module
        source_path.parent.mkdir(parents=True)
        source_path.write_bytes(self.source)
        start = self.source.index(b"simp")
        occurrence = {
            "id": inventory.occurrence_id(self.module, start, start + 4),
            "kind": "simp", "source": "simp", "startByte": start, "endByte": start + 4,
            "syntaxKind": "Lean.Parser.Tactic.simp", "executionRole": "direct_executable",
            "declarationKind": "proof", "action": "materialize",
        }
        self.record = {
            "module": self.module, "compiledModule": "Mathlib.A",
            "moduleHash": materializer.sha256(self.module.encode()),
            "sourceHash": materializer.sha256(self.source), "occurrences": [occurrence],
        }
        self.manifest = {
            "kind": "simp_engine_boundary_manifest", "reportSchema": 2,
            "allowDirty": False, "allowUnresolved": False,
            "modulePrefix": "Mathlib/", "inventoriedModuleCount": 2,
            "moduleFileCount": 2, "occurrenceCount": 2,
            "nestedOccurrenceCount": 0, "duplicateSyntaxRecords": 0,
            "duplicateScopeSyntaxRecords": 0, "fullFrontendFallbacks": [],
            "scopeFrontendFallbacks": [],
            "scopeProbe": {
                "module": materializer.scope.SCOPE_PROBE_IMPORT,
                "scheduling": materializer.scope.SCOPE_PROBE_SCHEDULING,
                "temporaryCopyOnly": True,
                "reportCommand": "simp_engine_boundary_scope_report",
            },
            "countsByExecutionRole": {"direct_executable": 2},
            "countsByDeclarationKind": {"proof": 2}, "countsByAction": {"materialize": 2},
            "implementationHashes": {"fixture": "hash"},
            "repositoryCommit": "repository", "mathlibCommit": "mathlib",
            "lean": {"version": "4.32.2", "commit": "lean"},
            "manualOverrides": {
                "sha256": "d" * 64, "schema": 1,
                "environment": {
                    "mathlibCommit": "mathlib",
                    "lean": {"version": "4.32.2", "commit": "lean"},
                },
            },
            "modules": [self.record, {**self.record, "module": "Mathlib/B.lean",
                "compiledModule": "Mathlib.B", "moduleHash": materializer.sha256(b"Mathlib/B.lean"),
                "occurrences": [{**occurrence, "id": inventory.occurrence_id("Mathlib/B.lean", start, start + 4)}]}],
        }
        self.manifest_path = self.root / "manifest.json"
        self.manifest_bytes = json.dumps(self.manifest, sort_keys=True, separators=(",", ":")).encode()
        self.manifest_path.write_bytes(self.manifest_bytes)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def capsule(self) -> tuple[dict[str, object], Path]:
        selected = materializer.validate_capsule_module_record(
            self.module, self.record, self.root / self.module
        )
        capsule = materializer.make_manifest_capsule(
            self.manifest_path, self.manifest_bytes, self.manifest, [selected]
        )
        path = self.root / "capsule.json"
        path.write_text(json.dumps(capsule, sort_keys=True, separators=(",", ":")))
        return capsule, path

    def test_streams_and_authenticates_selected_record(self) -> None:
        capsule, _path = self.capsule()
        actual, size, records = materializer.stream_manifest_capsule(self.manifest_path, capsule)
        self.assertEqual(actual, materializer.sha256(self.manifest_bytes))
        self.assertEqual(size, len(self.manifest_bytes))
        self.assertEqual(json.loads(records[self.module]), self.record)
        self.assertNotIn("record", capsule["selectedModules"][0])

    def test_rejects_wrong_manifest_hash_and_swapped_module_record(self) -> None:
        capsule, _path = self.capsule()
        wrong_hash = copy.deepcopy(capsule)
        wrong_hash["manifestHash"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError, "manifest changed"):
            materializer.stream_manifest_capsule(self.manifest_path, wrong_hash)
        swapped = copy.deepcopy(capsule)
        swapped["selectedModules"][0]["span"] = list(
            materializer._module_object_spans(self.manifest_bytes)[1]["Mathlib/B.lean"]
        )
        with self.assertRaisesRegex(RuntimeError, "selected manifest record hash"):
            materializer.stream_manifest_capsule(self.manifest_path, swapped)
        forged_global = copy.deepcopy(capsule)
        forged_global["globalIdentity"]["occurrenceCount"] = 999
        with self.assertRaisesRegex(RuntimeError, "global identity fields"):
            materializer.stream_manifest_capsule(self.manifest_path, forged_global)

    def test_rejects_inconsistent_authenticated_global_counts(self) -> None:
        capsule, _path = self.capsule()
        identity = capsule["globalIdentity"]
        self.assertIsInstance(identity, dict)
        identity["occurrenceCount"] = 3
        with self.assertRaisesRegex(RuntimeError, "count map does not sum"):
            materializer.validate_capsule_global_identity(identity)

    def test_rejects_changed_capsule_and_source(self) -> None:
        capsule, path = self.capsule()
        payload = path.read_bytes()
        with self.assertRaisesRegex(RuntimeError, "wrong hash"):
            materializer.read_manifest_capsule(path, expected_hash="0" * 64)
        path.write_bytes(payload + b" ")
        with self.assertRaisesRegex(RuntimeError, "wrong hash"):
            materializer.read_manifest_capsule(path, expected_hash=materializer.sha256(payload))
        path.write_bytes(payload)
        (self.root / self.module).write_bytes(self.source + b"-- changed\n")
        with self.assertRaisesRegex(RuntimeError, "source hash"):
            materializer.validate_capsule_module_record(self.module, self.record, self.root / self.module)

    def test_cleanup_protects_manifest_capsule_and_database_aliases(self) -> None:
        output = self.root / "boundary" / "run" / "report.json"
        debug = self.root / "boundary" / "run" / "report-run"
        capsule = output
        database = self.root / "overrides.json"
        for path in (capsule, database):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("immutable")
        with self.assertRaisesRegex(RuntimeError, "overlaps a cleanup target"):
            materializer.validate_cleanup_targets(
                self.root / "boundary" / "run" / "manifest.json",
                output, debug, protected_inputs=[capsule],
            )
        alias = debug / "db-alias.json"
        alias.parent.mkdir(parents=True, exist_ok=True)
        alias.symlink_to(database)
        with self.assertRaisesRegex(RuntimeError, "overlaps a cleanup target"):
            materializer.validate_cleanup_targets(
                self.root / "boundary" / "run" / "manifest.json",
                output, debug, protected_inputs=[alias],
            )

    def test_capsule_publication_rejects_symlinked_capsules_leaf(self) -> None:
        selected = materializer.validate_capsule_module_record(
            self.module, self.record, self.root / self.module
        )
        boundary = self.root / "boundary"
        boundary.mkdir()
        target = self.root / "outside"
        target.mkdir()
        (boundary / "capsules").symlink_to(target, target_is_directory=True)
        with mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", boundary):
            with self.assertRaisesRegex(RuntimeError, "must not be a symlink"):
                worker._write_manifest_capsule(
                    self.manifest_path, self.manifest_bytes, self.manifest,
                    [selected], boundary / "runs",
                )

    def test_capsule_publication_rejects_symlinked_capsule_file(self) -> None:
        selected = materializer.validate_capsule_module_record(
            self.module, self.record, self.root / self.module
        )
        boundary = self.root / "boundary"
        with mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", boundary):
            capsule_path, _capsule_hash = worker._write_manifest_capsule(
                self.manifest_path, self.manifest_bytes, self.manifest,
                [selected], boundary / "runs",
            )
            payload = capsule_path.read_bytes()
            outside = self.root / "outside-capsule.json"
            outside.write_bytes(payload)
            capsule_path.unlink()
            capsule_path.symlink_to(outside)
            with self.assertRaisesRegex(RuntimeError, "file must not be a symlink"):
                worker._write_manifest_capsule(
                    self.manifest_path, self.manifest_bytes, self.manifest,
                    [selected], boundary / "runs",
                )

    def test_capsule_expectations_match_ordinary_module_contract(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "only valid for one"):
            materializer.validate_capsule_expectations(
                {self.module: self.record}, [self.module, self.module + "x"], 1, None
            )
        materializer.validate_capsule_expectations(
            {self.module: self.record}, [self.module], 1, 1
        )
        with self.assertRaisesRegex(RuntimeError, "expect-total mismatch"):
            materializer.validate_capsule_expectations(
                {self.module: self.record}, [self.module], 2, None
            )
        with self.assertRaisesRegex(RuntimeError, "expect-materialize mismatch"):
            materializer.validate_capsule_expectations(
                {self.module: self.record}, [self.module], None, 2
            )


if __name__ == "__main__":
    raise SystemExit(unittest.main())
