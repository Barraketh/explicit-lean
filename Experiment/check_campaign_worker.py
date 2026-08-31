#!/usr/bin/env python3
"""Focused worker tests; no Lean corpus subprocesses are started."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import campaign_worker as worker
from translation_index import claim_work, connect, import_manifest, plan_work, status


class CampaignWorkerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="campaign-worker-")
        self.root = Path(self.temp.name)
        (self.root / "Mathlib").mkdir()
        self.db = self.root / "index.sqlite3"
        self.boundary = self.root / "boundary-materialization"
        storage = mock.patch.object(worker.shutil, "disk_usage", return_value=mock.Mock(free=64 * 1024**3))
        storage.start()
        self.addCleanup(storage.stop)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def manifest(self, *, empty: bool = False, allow_unresolved: bool = False) -> Path:
        source = "theorem a : True := by simp\n" if not empty else "theorem b : True := by exact True.intro\n"
        module = "Mathlib/A.lean" if not empty else "Mathlib/Empty.lean"
        path = self.root / module
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        occurrences = []
        if not empty:
            start = source.index("simp")
            occurrences.append({
                "id": hashlib.sha256(f"{module}:{start}:{start + 4}".encode()).hexdigest()[:16],
                "kind": "simp", "source": "simp", "startByte": start, "endByte": start + 4,
                "syntaxKind": "Lean.Parser.Tactic.simp", "action": "materialize",
                "executionRole": "direct_executable", "declarationKind": "proof",
            })
        value = {
            "kind": "simp_engine_boundary_manifest", "reportSchema": 2,
            "allowDirty": False, "allowUnresolved": allow_unresolved,
            "moduleFileCount": 1, "occurrenceCount": len(occurrences),
            "implementationHashes": {"fixture": "fixture-hash"},
            "repositoryCommit": "fixture-repository", "mathlibCommit": "fixture-mathlib",
            "lean": {"version": "4.32.2", "commit": "fixture-lean"},
            "modules": [{
                "module": module, "compiledModule": module[:-5].replace("/", "."),
                "moduleHash": "fixture-module", "sourceHash": hashlib.sha256(source.encode()).hexdigest(),
                "occurrences": occurrences,
            }],
        }
        result = self.root / ("diagnostic.json" if allow_unresolved else "manifest.json")
        result.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
        return result

    def manifest_many(self, names: list[str]) -> Path:
        modules = []
        for name in names:
            module = f"Mathlib/{name}.lean"
            source = f"theorem {name.lower()} : True := by simp\n"
            path = self.root / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
            start = source.index("simp")
            modules.append({
                "module": module, "compiledModule": module[:-5].replace("/", "."),
                "moduleHash": "fixture-module", "sourceHash": hashlib.sha256(source.encode()).hexdigest(),
                "occurrences": [{
                    "id": hashlib.sha256(f"{module}:{start}:{start + 4}".encode()).hexdigest()[:16],
                    "kind": "simp", "source": "simp", "startByte": start, "endByte": start + 4,
                    "syntaxKind": "Lean.Parser.Tactic.simp", "action": "materialize",
                    "executionRole": "direct_executable", "declarationKind": "proof",
                }],
            })
        value = {
            "kind": "simp_engine_boundary_manifest", "reportSchema": 2,
            "allowDirty": False, "allowUnresolved": False,
            "moduleFileCount": len(modules), "occurrenceCount": len(modules),
            "implementationHashes": {"fixture": "fixture-hash"},
            "repositoryCommit": "fixture-repository", "mathlibCommit": "fixture-mathlib",
            "lean": {"version": "4.32.2", "commit": "fixture-lean"}, "modules": modules,
        }
        result = self.root / "many.json"
        result.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
        return result

    def fake_report(self, manifest: Path, module: str, *, unobserved: bool = False, failed_variant: bool = False) -> dict[str, object]:
        occurrence = hashlib.sha256(f"{module}:23:27".encode()).hexdigest()[:16]
        return {
            "manifestPath": str(manifest.resolve()),
            "manifestHash": hashlib.sha256(manifest.read_bytes()).hexdigest(),
            "manifestPolicy": {"allowDirty": False, "allowUnresolved": False},
            "selectedModules": [module], "compileSuccess": True,
            "unobservedIds": [occurrence] if unobserved else [],
            "aggregate": {"unobservedCount": 1 if unobserved else 0},
            "occurrenceResults": [{
                "occurrence": occurrence, "action": "materialize", "coveredBy": None,
                "classification": "unobserved_executable" if unobserved else "materialized",
                "executionCount": 0 if unobserved else 1, "variantCount": 0 if unobserved else 1,
                "successVariantCount": 0 if unobserved or failed_variant else 1,
                "failureVariantCount": 1 if failed_variant else 0,
            }],
        }

    def run_fixture(self, manifest: Path, invoke, **options) -> dict[str, object]:
        with mock.patch.object(worker, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", self.boundary), \
             mock.patch.object(worker.materializer, "verify_implementation_hashes"), \
             mock.patch.object(worker.materializer, "verify_environment", return_value={"fixture": True}), \
             mock.patch.object(worker.materializer.corpus, "assert_repository"), \
             mock.patch.object(worker.materializer, "validate_shard_shape", side_effect=lambda value: value), \
             mock.patch.object(worker, "invoke_materializer", side_effect=invoke):
            return worker.run_worker(
                self.db, manifest, self.boundary / "runs", "worker-test",
                module_timeout=10, budget_guard=lambda: {"canDispatch": True}, **options,
            )

    def test_verified_report_counts_and_filter_claims_only_requested_module(self) -> None:
        manifest = self.manifest()
        def invoke(path, output, module, timeout):
            output.write_text(json.dumps(self.fake_report(manifest, module)), encoding="utf-8")
            return 0, "ok"
        result = self.run_fixture(manifest, invoke)
        self.assertEqual(result["succeeded"], 1)
        connection = connect(self.db)
        try:
            self.assertEqual(status(connection)["translated"], 1)
        finally:
            connection.close()

    def test_claim_filter_does_not_take_unrequested_queue_work(self) -> None:
        manifest = self.manifest_many(["A", "B"])
        connection = connect(self.db)
        try:
            import_manifest(connection, manifest, source_root=self.root)
            plan_work(connection, "impl", "tool")
            leases = claim_work(connection, "worker", modules=["Mathlib/B.lean"])
            self.assertEqual([lease.module for lease in leases], ["Mathlib/B.lean"])
            self.assertEqual(
                connection.execute(
                    "SELECT state FROM work_queue WHERE module='Mathlib/A.lean'"
                ).fetchone()[0],
                "queued",
            )
        finally:
            connection.close()

    def test_unobserved_report_is_candidate_and_remains_retryable(self) -> None:
        manifest = self.manifest()
        def invoke(path, output, module, timeout):
            output.write_text(json.dumps(self.fake_report(manifest, module, unobserved=True)), encoding="utf-8")
            return 0, "candidate"
        result = self.run_fixture(manifest, invoke)
        self.assertEqual(result["candidateReports"], 1)
        connection = connect(self.db)
        try:
            self.assertEqual(status(connection)["translated"], 0)
            self.assertEqual(connection.execute("SELECT state FROM work_queue").fetchone()[0], "queued")
        finally:
            connection.close()

    def test_failure_is_skipped_until_explicit_retry(self) -> None:
        manifest = self.manifest()
        calls = 0
        def failing(path, output, module, timeout):
            nonlocal calls
            calls += 1
            return 1, "failed"
        first = self.run_fixture(manifest, failing)
        self.assertEqual(first["failures"], 1)
        second = self.run_fixture(manifest, failing)
        self.assertEqual(second["skippedFailed"], 1)
        self.assertEqual(calls, 1)
        with mock.patch.object(worker, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", self.boundary), \
             mock.patch.object(worker.materializer, "verify_implementation_hashes"), \
             mock.patch.object(worker.materializer, "verify_environment", return_value={"fixture": True}), \
             mock.patch.object(worker.materializer.corpus, "assert_repository"), \
             mock.patch.object(worker, "invoke_materializer", side_effect=failing):
            worker.run_worker(self.db, manifest, self.boundary / "runs", "worker-test", retry_failed=True, budget_guard=lambda: {"canDispatch": True})
        self.assertEqual(calls, 2)

    def test_limit_advances_past_verified_and_partial_prefix(self) -> None:
        manifest = self.manifest_many(["A", "B", "C"])
        calls: list[str] = []
        def invoke(path, output, module, timeout):
            calls.append(module)
            output.write_text(json.dumps(self.fake_report(
                manifest, module, unobserved=module.endswith("B.lean")
            )), encoding="utf-8")
            return 0, "ok"
        first = self.run_fixture(manifest, invoke, max_modules=2)
        self.assertEqual(first["succeeded"], 1)
        self.assertEqual(first["candidateReports"], 1)
        second = self.run_fixture(manifest, invoke, max_modules=1)
        self.assertEqual(second["processed"], 1)
        self.assertEqual(calls, ["Mathlib/A.lean", "Mathlib/B.lean", "Mathlib/C.lean"])

    def test_budget_denial_and_default_empty_module_skip(self) -> None:
        manifest = self.manifest(empty=True)
        with mock.patch.object(worker, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", self.boundary), \
             mock.patch.object(worker.materializer, "verify_implementation_hashes"):
            result = worker.run_worker(self.db, manifest, self.boundary / "runs", "worker-test", budget_guard=lambda: {"canDispatch": False})
        self.assertEqual(result["skippedEmpty"], 1)
        self.assertEqual(result["processed"], 0)
        with self.assertRaisesRegex(RuntimeError, "diagnostic manifests"):
            with mock.patch.object(worker.materializer, "verify_implementation_hashes"):
                worker.run_worker(self.db, self.manifest(allow_unresolved=True), self.boundary / "runs", "worker-test", budget_guard=lambda: {"canDispatch": True})


    def test_protect_inputs_and_preflight_before_index_mutation(self) -> None:
        manifest = self.manifest()
        with mock.patch.object(worker.materializer, "verify_implementation_hashes"), \
             mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", self.root), \
             mock.patch.object(worker.materializer.corpus, "assert_repository", side_effect=RuntimeError("moving_ref")):
            with self.assertRaisesRegex(RuntimeError, "manifest must not"):
                worker.run_worker(self.db, manifest, self.root, "test", budget_guard=lambda: {"canDispatch": True})
            with self.assertRaisesRegex(RuntimeError, "database must not"):
                worker.run_worker(self.boundary / "database", manifest, self.boundary, "test", budget_guard=lambda: {"canDispatch": True})
            with self.assertRaisesRegex(RuntimeError, "moving_ref"):
                worker.run_worker(self.db, manifest, self.boundary, "test", budget_guard=lambda: {"canDispatch": True})
        self.assertFalse(self.db.exists(), "preflight failure created or changed the index")

    def test_low_storage_stops_before_index_or_lease_mutation(self) -> None:
        manifest = self.manifest()
        reserve = worker.DEFAULT_MINIMUM_FREE_BYTES
        with mock.patch.object(worker.shutil, "disk_usage", return_value=mock.Mock(free=reserve - 1)):
            result = self.run_fixture(manifest, lambda *args: self.fail("materializer started"))
        self.assertTrue(result["storageDenied"])
        self.assertFalse(result["budgetDenied"])
        self.assertEqual(result["processed"], 0)
        self.assertFalse(self.db.exists(), "storage denial created the index")
        self.assertEqual(result["storage"]["freeBytes"], reserve - 1)

    def test_storage_loss_preserves_completed_result_and_unclaimed_queue(self) -> None:
        manifest = self.manifest_many(["A", "B"])
        reserve = worker.DEFAULT_MINIMUM_FREE_BYTES
        calls = []
        def invoke(path, output, module, timeout):
            calls.append(module)
            output.write_text(json.dumps(self.fake_report(manifest, module)), encoding="utf-8")
            return 0, "ok"
        # Enough room at preflight and A's claim, then no room to start B.
        with mock.patch.object(worker.shutil, "disk_usage", side_effect=[
            mock.Mock(free=reserve), mock.Mock(free=reserve), mock.Mock(free=reserve - 1)
        ]):
            result = self.run_fixture(manifest, invoke)
        self.assertEqual(calls, ["Mathlib/A.lean"])
        self.assertEqual(result["succeeded"], 1)
        self.assertTrue(result["storageDenied"])
        connection = connect(self.db)
        try:
            states = dict(connection.execute("SELECT module,state FROM work_queue"))
            self.assertEqual(states, {"Mathlib/A.lean": "succeeded", "Mathlib/B.lean": "queued"})
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM attempts").fetchone()[0], 1)
        finally:
            connection.close()

    def test_unknown_storage_stops_and_reports_error(self) -> None:
        manifest = self.manifest()
        with mock.patch.object(worker.shutil, "disk_usage", side_effect=OSError("volume unavailable")):
            result = self.run_fixture(manifest, lambda *args: self.fail("materializer started"))
        self.assertTrue(result["storageDenied"])
        self.assertIsNone(result["storage"]["freeBytes"])
        self.assertIn("volume unavailable", result["storage"]["error"])
        self.assertFalse(self.db.exists())


if __name__ == "__main__":
    raise SystemExit(unittest.main())
