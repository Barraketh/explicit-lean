#!/usr/bin/env python3
"""Isolated protocol tests for the schema-13 v10 supervisor/bootstrap."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import Mock, patch

import campaign_supervisor_v10 as supervisor
import campaign_worker
from translation_index import connect, occurrence_id


class V10SupervisorTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="schema13-v10-")
        self.root = Path(self.temp.name)
        self.source_root = self.root / "source"
        (self.source_root / "Mathlib").mkdir(parents=True)
        self.boundary = self.root / "boundary-materialization"
        self.output_parent = self.boundary / "outputs"
        self.output_parent.mkdir(parents=True)
        self.manifest_dir = self.root / "manifests"
        self.manifest_dir.mkdir()
        self.database = self.root / "index.sqlite3"
        self.lock = self.root / "schema13-v10.lock"
        self.manual = self.root / "manual.json"
        self.manual.write_bytes(b"fixture-manual-v1")
        self._write_source("A")
        self._write_source("B")
        self.v9 = self._write_manifest("v9", "r" * 40)
        self.v10 = self._write_manifest("v10", "s" * 40)
        self.v9_hash = hashlib.sha256(self.v9.read_bytes()).hexdigest()
        self.v10_hash = hashlib.sha256(self.v10.read_bytes()).hexdigest()
        self.dependency_map = self.root / "dependency-map.json"
        self.dependency_map.write_text(json.dumps({
            f"Mathlib/{module}.lean@{hashlib.sha256((self.source_root / 'Mathlib' / f'{module}.lean').read_bytes()).hexdigest()}": []
            for module in ("A", "B")
        }), encoding="utf-8")
        self.config = supervisor.SupervisorConfig(
            database=self.database,
            manifest=self.v10,
            dependency_map=self.dependency_map,
            source_root=self.source_root,
            output_parent=self.output_parent,
            manual_overrides=self.manual,
            expected_v9_manifest_path=self.v9,
            expected_v9_manifest_hash=self.v9_hash,
            expected_v10_manifest_hash=self.v10_hash,
            expected_modules=2,
            expected_occurrences=2,
            run_id="fixture-v10",
            minimum_free_bytes=1,
            module_timeout=10,
            max_passes=2,
            max_seconds=10,
            start_pass=1,
        )
        # The fixture deliberately exercises the supervisor/index protocol,
        # while implementation source authentication belongs to the producer.
        self.verify_hashes = patch.object(
            supervisor.materializer, "verify_implementation_hashes"
        )
        self.verify_hashes.start()
        self.addCleanup(self.verify_hashes.stop)
        self.boundary_root = patch.object(
            supervisor.materializer, "BOUNDARY_DEBUG_ROOT", self.boundary
        )
        self.boundary_root.start()
        self.addCleanup(self.boundary_root.stop)
        self.mathlib_root = patch.object(campaign_worker, "MATHLIB", self.source_root)
        self.mathlib_root.start()
        self.addCleanup(self.mathlib_root.stop)
        self.materializer_mathlib_root = patch.object(supervisor.materializer, "MATHLIB", self.source_root)
        self.materializer_mathlib_root.start()
        self.addCleanup(self.materializer_mathlib_root.stop)
        self.validators = [
            patch.object(supervisor.materializer.corpus, "enforce_manifest_policy"),
            patch.object(supervisor.materializer, "validate_manifest_selection", return_value=[]),
            patch.object(supervisor.materializer, "verify_environment", return_value={"fixture": True}),
            patch.object(supervisor.manual_overlay, "_load_overlay_projected", return_value=Mock(identity=lambda: {"fixture": "overlay"})),
        ]
        for validator in self.validators:
            validator.start()
            self.addCleanup(validator.stop)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def _write_source(self, module: str) -> None:
        (self.source_root / "Mathlib" / f"{module}.lean").write_text(
            f"theorem {module.lower()} : True := by simp\n", encoding="utf-8"
        )

    def _write_manifest(self, label: str, repository: str) -> Path:
        modules = []
        for module in ("A", "B"):
            path = self.source_root / "Mathlib" / f"{module}.lean"
            source = path.read_text(encoding="utf-8")
            start = source.index("simp")
            name = f"Mathlib/{module}.lean"
            modules.append({
                "module": name,
                "compiledModule": f"Mathlib.{module}",
                "sourceHash": hashlib.sha256(source.encode()).hexdigest(),
                # The source-version join is immutable across manifests; the
                # v10 manifest/toolchain identity is checked separately
                # without pretending this is a new source version.
                "moduleHash": hashlib.sha256(name.encode()).hexdigest(),
                "occurrences": [{
                    "id": occurrence_id(name, start, start + 4),
                    "kind": "simp",
                    "source": "simp",
                    "startByte": start,
                    "endByte": start + 4,
                    "syntaxKind": "Lean.Parser.Tactic.simp",
                    "executionRole": "direct_executable",
                    "declarationKind": "proof",
                    "action": "materialize",
                }],
            })
        value = {
            "kind": "simp_engine_boundary_manifest", "reportSchema": 2,
            "allowDirty": False, "allowUnresolved": False,
            "repositoryCommit": repository, "mathlibCommit": "m" * 40,
            "lean": {"version": "4.32.2", "commit": "l" * 40},
            "modulePrefix": "Mathlib/", "moduleFileCount": 2,
            "inventoriedModuleCount": 2, "occurrenceCount": 2,
            "nestedOccurrenceCount": 0, "duplicateSyntaxRecords": 0,
            "duplicateScopeSyntaxRecords": 0, "fullFrontendFallbacks": [],
            "scopeFrontendFallbacks": [],
            "scopeProbe": {"module": "fixture", "scheduling": "fixture",
                            "temporaryCopyOnly": True, "reportCommand": "fixture"},
            "countsByExecutionRole": {"direct_executable": 2},
            "countsByDeclarationKind": {"proof": 2},
            "countsByAction": {"materialize": 2},
            "implementationHashes": {"fixture": label},
            "manualOverrides": {"sha256": "0" * 64, "schema": 1,
                                 "environment": {}},
            "modules": modules,
        }
        path = self.manifest_dir / (
            supervisor.V10_MANIFEST_LABEL if label == "v10" else "schema13-isolated-closed-manifest-v9.json"
        )
        path.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
        return path

    def _import_v9(self) -> None:
        connection = connect(self.database)
        try:
            from translation_index import import_manifest
            import_manifest(connection, self.v9, source_root=self.source_root)
        finally:
            connection.close()

    def test_v9_index_bootstraps_to_authenticated_v10_before_ordering(self) -> None:
        self._import_v9()
        with patch.object(supervisor, "ordered_modules", side_effect=AssertionError("ordering ran during bootstrap")):
            snapshot, path, payload, value, manifest_hash, overlay = supervisor.bootstrap_index(self.config)
        self.assertEqual(path, snapshot.manifest.resolve())
        self.assertEqual(manifest_hash, self.v10_hash)
        self.assertEqual(payload, snapshot.manifest_bytes)
        self.assertEqual(value["repositoryCommit"], "s" * 40)
        connection = connect(self.database)
        try:
            self.assertEqual(
                [(row[0], row[1]) for row in connection.execute(
                    "SELECT manifest_hash,COUNT(*) FROM modules GROUP BY manifest_hash"
                )],
                [(self.v10_hash, 2)],
            )
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM manifests").fetchone()[0], 2)
        finally:
            connection.close()

    def test_authenticated_v10_index_can_resume_without_requiring_v9_again(self) -> None:
        self._import_v9()
        first = supervisor.bootstrap_index(self.config)
        second = supervisor.bootstrap_index(self.config)
        self.assertNotEqual(first[0].root, second[0].root)
        self.assertEqual(first[4], second[4], self.v10_hash)

    def test_manual_override_mismatch_fails_before_v10_import(self) -> None:
        self._import_v9()
        bad = self.root / "manual-mismatch.json"
        bad.write_bytes(b"different-manual-bytes")
        config = self.config.__class__(**{**self.config.__dict__, "manual_overrides": bad})
        loader = patch.object(
            supervisor.manual_overlay, "_load_overlay_projected",
            side_effect=RuntimeError("manual override database hash does not match manifest"),
        )
        with loader, self.assertRaisesRegex(RuntimeError, "manual override database hash"):
            supervisor.bootstrap_index(config)
        connection = connect(self.database)
        try:
            self.assertEqual(
                [(row[0], row[1]) for row in connection.execute(
                    "SELECT manifest_hash,COUNT(*) FROM modules GROUP BY manifest_hash"
                )],
                [(self.v9_hash, 2)],
            )
        finally:
            connection.close()

    def test_live_current_lease_blocks_bootstrap_but_expired_lease_is_reaped(self) -> None:
        self._import_v9()
        connection = connect(self.database)
        try:
            connection.execute(
                "INSERT INTO work_queue(module,cache_key,state,worker,lease_expires_at,updated_at) "
                "VALUES ('Mathlib/A.lean','legacy-key','running','legacy-worker',?,?)",
                (time.time() + 3600, time.time()),
            )
        finally:
            connection.close()
        with self.assertRaisesRegex(RuntimeError, "current worker leases are active"):
            supervisor.bootstrap_index(self.config)

    def test_source_root_mismatch_is_rejected_before_bootstrap(self) -> None:
        self._import_v9()
        config = self.config.__class__(**{**self.config.__dict__, "source_root": self.root})
        with self.assertRaisesRegex(RuntimeError, "source root must equal"):
            supervisor.run_supervisor(config)

    def test_v10_cache_identity_is_fresh_and_exact(self) -> None:
        self._import_v9()
        snapshot, _, _, value, _hash, overlay = supervisor.bootstrap_index(self.config)
        modules, deferred = supervisor.ordered_modules(self.config, value, self.v10_hash, overlay, snapshot)
        self.assertEqual(modules, ["Mathlib/A.lean", "Mathlib/B.lean"])
        self.assertEqual(deferred, 0)
        value = json.loads(self.v10.read_text())
        old_value = json.loads(self.v9.read_text())
        old_impl, old_toolchain = campaign_worker._identities(old_value, overlay.identity())
        new_impl, new_toolchain = campaign_worker._identities(value, overlay.identity())
        connection = connect(self.database)
        try:
            from translation_index import cache_key
            old_key, _ = cache_key(connection, modules[0], old_impl, old_toolchain)
            new_key, _ = cache_key(connection, modules[0], new_impl, new_toolchain)
            queue_key = connection.execute(
                "SELECT cache_key FROM work_queue WHERE module=?", (modules[0],)
            ).fetchone()[0]
        finally:
            connection.close()
        self.assertNotEqual(old_key, new_key)
        self.assertEqual(queue_key, new_key)
        self.assertNotEqual(old_toolchain, new_toolchain)

    def test_v9_success_cannot_be_relabelled_as_v10_cache(self) -> None:
        self._import_v9()
        snapshot, _, _, value, _hash, overlay = supervisor.bootstrap_index(self.config)
        value = json.loads(self.v10.read_text())
        implementation, toolchain = campaign_worker._identities(value, overlay.identity())
        connection = connect(self.database)
        try:
            from translation_index import cache_key
            key, dependency = cache_key(connection, "Mathlib/A.lean", implementation, toolchain)
            row = connection.execute(
                "SELECT source_hash,analysis_identity FROM modules WHERE module='Mathlib/A.lean'"
            ).fetchone()
            canonical = lambda item: json.dumps(item, sort_keys=True, separators=(",", ":"))
            connection.execute(
                "INSERT INTO result_cache(cache_key,module,source_hash,analysis_identity,"
                "implementation_identity,toolchain_identity,dependency_identity,status,"
                "translation_status,result_json,failure,log_ref,artifact_ref,recorded_at) "
                "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (key, "Mathlib/A.lean", row[0], row[1], canonical(implementation),
                 canonical(toolchain), dependency, "success", "verified_translated",
                 json.dumps({"manifestHash": self.v9_hash}), None, None, None, 0),
            )
        finally:
            connection.close()
        with self.assertRaisesRegex(RuntimeError, "bound to a different manifest"):
            supervisor.ordered_modules(self.config, value, self.v10_hash, overlay, snapshot)

    def test_exit125_a_then_b_success_stays_one_pass_and_next_pass_is_unique(self) -> None:
        self._import_v9()
        calls = []

        def fake_worker(database, manifest, output, worker, **kwargs):
            calls.append((worker, Path(output), list(kwargs["modules"]), kwargs.get("retry_failed", False), kwargs["module_timeout"], kwargs["max_seconds"]))
            if len(calls) == 1:
                # Model c328's durable exit-125 result: A is abandoned and
                # requeued, while B remains a successful same-pass result.
                connection = connect(database)
                try:
                    key = connection.execute(
                        "SELECT cache_key FROM work_queue WHERE module='Mathlib/A.lean'"
                    ).fetchone()[0]
                    cursor = connection.execute(
                        "INSERT INTO attempts(module,cache_key,worker,status,failure,started_at,finished_at) "
                        "VALUES ('Mathlib/A.lean',?,?, 'abandoned', ?, 0, 1)",
                        (key, worker, supervisor.RESOURCE_FAILURE),
                    )
                    connection.execute(
                        "UPDATE work_queue SET state='queued',last_attempt_id=?,worker=NULL,"
                        "lease_expires_at=NULL WHERE module='Mathlib/A.lean'",
                        (cursor.lastrowid,),
                    )
                finally:
                    connection.close()
                return {"manifestHash": self.v10_hash, "processed": 2, "succeeded": 1, "failures": 0,
                        "resourceStopped": True, "memoryDenied": False,
                        "budgetDenied": False, "storageDenied": False, "timedOut": False}
            return {"manifestHash": self.v10_hash, "processed": 1, "succeeded": 1, "failures": 0,
                    "resourceStopped": False, "memoryDenied": False,
                    "budgetDenied": False, "storageDenied": False, "timedOut": False}

        admitted = {"canDispatch": True, "availableBytes": 64, "minimumFreeMemoryBytes": 1}
        storage = {"canDispatch": True, "freeBytes": 64, "minimumFreeBytes": 1}
        with patch.object(supervisor.campaign_budget, "check", return_value={"canDispatch": True}), \
             patch.object(supervisor.campaign_worker, "memory_status", return_value=admitted), \
             patch.object(supervisor.campaign_worker, "storage_status", return_value=storage), \
             patch.object(supervisor.campaign_worker, "run_worker", side_effect=fake_worker):
            self.assertEqual(supervisor.run_supervisor(self.config), 0)
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0][2], ["Mathlib/A.lean", "Mathlib/B.lean"])
        self.assertIn("Mathlib/A.lean", calls[1][2])
        self.assertFalse(calls[0][3])
        self.assertLessEqual(calls[0][4], self.config.module_timeout)
        self.assertLessEqual(calls[0][5], self.config.max_seconds)
        self.assertNotEqual(calls[0][0], calls[1][0])
        self.assertNotEqual(calls[0][1], calls[1][1])
        self.assertIn("pass-1", calls[0][0])
        self.assertIn("pass-2", calls[1][0])

    def test_budget_storage_memory_and_time_stops_are_fail_closed(self) -> None:
        cases = (
            ("budget", {"canDispatch": False}, {"canDispatch": True}, {"canDispatch": True}),
            ("storage", {"canDispatch": True}, {"canDispatch": True}, {"canDispatch": False}),
        )
        for label, budget, memory, storage in cases:
            with self.subTest(label=label):
                self._import_v9()
                run = Mock(return_value={})
                with patch.object(supervisor.campaign_budget, "check", return_value=budget), \
                     patch.object(supervisor.campaign_worker, "memory_status", return_value=memory), \
                     patch.object(supervisor.campaign_worker, "storage_status", return_value=storage), \
                     patch.object(supervisor.campaign_worker, "run_worker", run):
                    self.assertEqual(supervisor.run_supervisor(self.config), 0)
                run.assert_not_called()
                self.database.unlink()
        self._import_v9()
        run = Mock(return_value={})
        denied = {"canDispatch": False, "availableBytes": None, "error": "telemetry"}
        with patch.object(supervisor.campaign_budget, "check", return_value={"canDispatch": True}), \
             patch.object(supervisor.campaign_worker, "memory_status", return_value=denied), \
             patch.object(supervisor.campaign_worker, "storage_status", return_value={"canDispatch": True}), \
             patch.object(supervisor.time, "sleep"), \
             patch.object(supervisor.time, "monotonic", side_effect=[0.0, 0.0, 2.0, 2.0, 2.0]), \
             patch.object(supervisor.campaign_worker, "run_worker", run):
            config = self.config.__class__(**{**self.config.__dict__, "max_seconds": 1})
            self.assertEqual(supervisor.run_supervisor(config), 0)
        run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
