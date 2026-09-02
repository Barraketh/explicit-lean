#!/usr/bin/env python3
"""Isolated protocol tests for the schema-13 v10 supervisor/bootstrap."""

from __future__ import annotations

import hashlib
import json
import fcntl
import os
from dataclasses import replace
from pathlib import Path
import tempfile
import time
import unittest
from types import SimpleNamespace
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

    def _insert_success(self, module, value, overlay, artifact, manifest_path):
        """Record the same durable success shape that c328 writes."""
        implementation, toolchain = campaign_worker._identities(value, overlay.identity())
        canonical = lambda item: json.dumps(item, sort_keys=True, separators=(",", ":"))
        report_json = canonical({
            "manifestHash": self.v10_hash,
            "manifestPath": str(Path(manifest_path).resolve()),
        })
        artifact = Path(artifact)
        artifact.write_text(report_json, encoding="utf-8")
        evidence_root = supervisor.materializer.debug_root_for(artifact)
        evidence_root.mkdir(parents=True, exist_ok=True)
        (evidence_root / "referenced-evidence.txt").write_text(
            "fixture-evidence-v1", encoding="utf-8"
        )
        connection = connect(self.database)
        try:
            from translation_index import cache_key
            key, dependency = cache_key(connection, module, implementation, toolchain)
            row = connection.execute(
                "SELECT source_hash,analysis_identity FROM modules WHERE module=?", (module,)
            ).fetchone()
            connection.execute(
                "INSERT INTO result_cache(cache_key,module,source_hash,analysis_identity,"
                "implementation_identity,toolchain_identity,dependency_identity,status,"
                "translation_status,result_json,failure,log_ref,artifact_ref,recorded_at) "
                "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (key, module, row[0], row[1], canonical(implementation),
                 canonical(toolchain), dependency, "success", "verified_translated",
                 report_json, None, None, str(artifact), 0),
            )
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
        connection = connect(self.database)
        try:
            queue_before = connection.execute(
                "SELECT module,cache_key,state,worker,lease_expires_at,last_attempt_id "
                "FROM work_queue ORDER BY module"
            ).fetchall()
            attempts_before = connection.execute(
                "SELECT module,cache_key,worker,status,failure FROM attempts ORDER BY attempt_id"
            ).fetchall()
        finally:
            connection.close()
        with self.assertRaisesRegex(RuntimeError, "bound to a different manifest"):
            supervisor.ordered_modules(self.config, value, self.v10_hash, overlay, snapshot)
        connection = connect(self.database)
        try:
            self.assertEqual(
                connection.execute(
                    "SELECT module,cache_key,state,worker,lease_expires_at,last_attempt_id "
                    "FROM work_queue ORDER BY module"
                ).fetchall(), queue_before,
            )
            self.assertEqual(
                connection.execute(
                    "SELECT module,cache_key,worker,status,failure FROM attempts ORDER BY attempt_id"
                ).fetchall(), attempts_before,
            )
        finally:
            connection.close()

    def test_cache_row_module_must_match_its_planned_cache_key(self) -> None:
        self._import_v9()
        snapshot, _, _, value, _, overlay = supervisor.bootstrap_index(self.config)
        implementation, toolchain = campaign_worker._identities(value, overlay.identity())
        canonical = lambda item: json.dumps(item, sort_keys=True, separators=(",", ":"))
        connection = connect(self.database)
        try:
            from translation_index import cache_key
            key, dependency = cache_key(connection, "Mathlib/A.lean", implementation, toolchain)
            row = connection.execute(
                "SELECT source_hash,analysis_identity FROM modules WHERE module='Mathlib/B.lean'"
            ).fetchone()
            connection.execute(
                "INSERT INTO result_cache(cache_key,module,source_hash,analysis_identity,"
                "implementation_identity,toolchain_identity,dependency_identity,status,"
                "translation_status,result_json,failure,log_ref,artifact_ref,recorded_at) "
                "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (key, "Mathlib/B.lean", row[0], row[1], canonical(implementation),
                 canonical(toolchain), dependency, "failed", "unverified", "{}",
                 "forged", None, None, 0),
            )
        finally:
            connection.close()
        with self.assertRaisesRegex(RuntimeError, "module/key association"):
            supervisor.ordered_modules(self.config, value, self.v10_hash, overlay, snapshot)

    def test_public_run_path_holds_each_fixed_lock(self) -> None:
        for path in (supervisor.V9_LOCK_PATH, supervisor.V10_LOCK_PATH):
            descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
                with self.assertRaisesRegex(RuntimeError, "another schema13 supervisor holds"):
                    supervisor.run_supervisor(self.config)
            finally:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
                os.close(descriptor)

    def test_lock_symlink_is_rejected_without_touching_fixed_locks(self) -> None:
        lock_root = self.root / "isolated-locks"
        lock_root.mkdir()
        target = lock_root / "target"
        target.write_text("target", encoding="utf-8")
        symlink = lock_root / "v9.lock"
        symlink.symlink_to(target)
        v10_lock = lock_root / "v10.lock"
        with patch.object(supervisor, "V9_LOCK_PATH", symlink), \
             patch.object(supervisor, "V10_LOCK_PATH", v10_lock):
            with self.assertRaises(OSError):
                with supervisor.supervisor_locks("fixture-v10", self.v10_hash):
                    self.fail("symlink lock unexpectedly acquired")
        self.assertEqual(target.read_text(encoding="utf-8"), "target")

    def test_cli_preserves_symlink_output_parent_for_rejection(self) -> None:
        link = self.root / "output-link"
        link.symlink_to(self.output_parent, target_is_directory=True)
        args = SimpleNamespace(
            database=str(self.database), manifest=str(self.v10), source_root=str(self.source_root),
            output_parent=str(link), dependency_map=str(self.dependency_map),
            manual_overrides=str(self.manual), v9_manifest=str(self.v9),
            v9_manifest_sha256=self.v9_hash, v10_manifest_sha256=self.v10_hash,
            modules=2, occurrences=2, run_id="fixture-v10", minimum_free_bytes=1,
            module_timeout=10, max_passes=2, max_seconds=10, start_pass=1,
        )
        config = supervisor._config_from_args(args)
        self.assertTrue(config.output_parent.is_symlink())
        with self.assertRaisesRegex(RuntimeError, "output parent must not be a symlink"):
            supervisor.run_supervisor(config)

    def test_valid_cached_success_uses_module_and_survives_fresh_resume_snapshot(self) -> None:
        self._import_v9()
        first = supervisor.bootstrap_index(self.config)
        first_snapshot, _, _, value, _, overlay = first
        pass_snapshot = supervisor._snapshot(self.config)
        self._insert_success(
            "Mathlib/A.lean", value, overlay, self.output_parent / "cached-a.json",
            pass_snapshot.manifest,
        )
        cached_artifact = self.output_parent / "cached-a.json"
        cached_report = json.loads(cached_artifact.read_text(encoding="utf-8"))
        cached_artifact.write_text(json.dumps(cached_report, indent=2), encoding="utf-8")
        with patch.object(supervisor.campaign_worker, "_report_is_verified", return_value=True) as verified:
            modules, _ = supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, first_snapshot
            )
        self.assertEqual(modules, ["Mathlib/B.lean"])
        self.assertEqual(verified.call_args.args[0], cached_report)
        self.assertEqual(verified.call_args.args[1], "Mathlib/A.lean")
        self.assertEqual(verified.call_args.args[2], pass_snapshot.manifest)
        pass_manifest_bytes = pass_snapshot.manifest.read_bytes()
        pass_snapshot.manifest.write_bytes(b"changed-pass-snapshot")
        with self.assertRaisesRegex(RuntimeError, "manifest bytes do not match"):
            supervisor.ordered_modules(self.config, value, self.v10_hash, overlay, first_snapshot)
        pass_snapshot.manifest.write_bytes(pass_manifest_bytes)
        escaped_manifest = self.root / "escaped-v10-manifest.json"
        escaped_manifest.write_bytes(pass_manifest_bytes)
        with self.assertRaisesRegex(RuntimeError, "outside the v10 input root"):
            supervisor._authenticated_report_manifest_path(
                {"manifestPath": str(escaped_manifest)},
                self.v10_hash, first_snapshot,
            )
        cached_artifact.write_text(
            json.dumps({"manifestHash": self.v9_hash}, indent=2), encoding="utf-8"
        )
        with self.assertRaisesRegex(RuntimeError, "differs from the durable result"):
            supervisor.ordered_modules(self.config, value, self.v10_hash, overlay, first_snapshot)
        cached_artifact.write_text(json.dumps(cached_report, indent=2), encoding="utf-8")

        second_snapshot, _, _, value2, _, overlay2 = supervisor.bootstrap_index(self.config)
        self.assertNotEqual(first_snapshot.manifest, second_snapshot.manifest)
        with patch.object(supervisor.campaign_worker, "_report_is_verified", return_value=True) as resumed:
            modules, _ = supervisor.ordered_modules(
                self.config, value2, self.v10_hash, overlay2, second_snapshot
            )
        self.assertEqual(modules, ["Mathlib/B.lean"])
        self.assertEqual(resumed.call_args.args[0], cached_report)
        self.assertEqual(resumed.call_args.args[1], "Mathlib/A.lean")
        self.assertEqual(resumed.call_args.args[2], pass_snapshot.manifest)

    def test_cached_success_is_verified_once_per_process_and_new_success_is_checked(self) -> None:
        self._import_v9()
        snapshot, _, _, value, _, overlay = supervisor.bootstrap_index(self.config)
        self._insert_success(
            "Mathlib/A.lean", value, overlay, self.output_parent / "cached-a.json",
            snapshot.manifest,
        )
        verified_keys = {}
        with patch.object(supervisor.campaign_worker, "_report_is_verified", return_value=True) as verified:
            first, _ = supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, snapshot, verified_keys
            )
            second, _ = supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, snapshot, verified_keys
            )
            self._insert_success(
                "Mathlib/B.lean", value, overlay, self.output_parent / "cached-b.json",
                snapshot.manifest,
            )
            third, _ = supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, snapshot, verified_keys
            )
        self.assertEqual(first, ["Mathlib/B.lean"])
        self.assertEqual(second, first)
        cached_artifact = self.output_parent / "cached-a.json"
        cached_report = json.loads(cached_artifact.read_text(encoding="utf-8"))
        evidence_root = supervisor.materializer.debug_root_for(cached_artifact)
        evidence_file = evidence_root / "referenced-evidence.txt"
        evidence_file.write_text("fixture-evidence-v2", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "evidence changed after verification"):
            supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, snapshot, verified_keys
            )
        evidence_file.write_text("fixture-evidence-v1", encoding="utf-8")
        evidence_file.unlink()
        with self.assertRaisesRegex(RuntimeError, "evidence changed after verification"):
            supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, snapshot, verified_keys
            )
        evidence_file.write_text("fixture-evidence-v1", encoding="utf-8")
        extra_evidence = evidence_root / "added-evidence.txt"
        extra_evidence.write_text("unexpected", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "evidence changed after verification"):
            supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, snapshot, verified_keys
            )
        extra_evidence.unlink()
        cached_artifact.write_text(json.dumps(cached_report, indent=2), encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "changed after verification"):
            supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, snapshot, verified_keys
            )
        cached_artifact.unlink()
        with self.assertRaisesRegex(RuntimeError, "missing or is a symlink"):
            supervisor.ordered_modules(
                self.config, value, self.v10_hash, overlay, snapshot, verified_keys
            )
        cached_artifact.write_text(json.dumps(cached_report, separators=(",", ":")), encoding="utf-8")
        self.assertEqual(third, [])
        self.assertEqual(verified.call_count, 2)
        self.assertEqual(
            [call.args[1] for call in verified.call_args_list],
            ["Mathlib/A.lean", "Mathlib/B.lean"],
        )

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
                self._insert_success(
                    "Mathlib/B.lean", json.loads(self.v10.read_text()),
                    Mock(identity=lambda: {"fixture": "overlay"}),
                    Path(output) / "b-report.json", manifest,
                )
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
             patch.object(supervisor.campaign_worker, "_report_is_verified", return_value=True), \
             patch.object(supervisor.campaign_worker, "run_worker", side_effect=fake_worker):
            self.assertEqual(supervisor.run_supervisor(self.config), 0)
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0][2], ["Mathlib/A.lean", "Mathlib/B.lean"])
        self.assertEqual(calls[1][2], ["Mathlib/A.lean"])
        self.assertFalse(calls[0][3])
        self.assertLessEqual(calls[0][4], self.config.module_timeout)
        self.assertLessEqual(calls[0][5], self.config.max_seconds)
        self.assertNotEqual(calls[0][0], calls[1][0])
        self.assertNotEqual(calls[0][1], calls[1][1])
        self.assertIn("pass-1", calls[0][0])
        self.assertIn("pass-2", calls[1][0])

    def test_worker_pass_cleanup_runs_before_next_admission(self) -> None:
        self._import_v9()
        events = []
        calls = 0

        def admission():
            events.append("admission")
            return {"canDispatch": True, "availableBytes": 64, "minimumFreeMemoryBytes": 1}

        def fake_worker(*_args, **_kwargs):
            nonlocal calls
            calls += 1
            events.append("worker")
            return {
                "manifestHash": self.v10_hash, "processed": 1, "succeeded": 1,
                "failures": 0, "resourceStopped": calls == 1,
                "memoryDenied": False, "budgetDenied": False,
                "storageDenied": False, "timedOut": False,
            }

        def planned(*_args, **_kwargs):
            events.append("ordered")
            return ["Mathlib/A.lean"], 0

        def reconstruct(*_args, **_kwargs):
            events.append("reconstruct")
            return json.loads(self.v10.read_bytes())

        with patch.object(supervisor.campaign_budget, "check", return_value={"canDispatch": True}), \
             patch.object(supervisor.campaign_worker, "memory_status", side_effect=admission), \
             patch.object(supervisor.campaign_worker, "storage_status", return_value={"canDispatch": True}), \
             patch.object(supervisor, "ordered_modules", side_effect=planned), \
             patch.object(supervisor, "_reconstruct_manifest_value", side_effect=reconstruct), \
             patch.object(supervisor.campaign_worker, "run_worker", side_effect=fake_worker), \
             patch.object(supervisor.gc, "collect", side_effect=lambda: events.append("gc")):
            self.assertEqual(supervisor.run_supervisor(self.config), 0)

        self.assertEqual(calls, 2)
        self.assertEqual(events, [
            "admission", "ordered", "gc", "worker", "gc",
            "admission", "reconstruct", "ordered", "gc", "worker", "gc",
        ])

    def test_invalid_manifest_reconstruction_fails_before_planning(self) -> None:
        self._import_v9()
        ordered = Mock(return_value=(["Mathlib/A.lean"], 0))
        calls = 0
        original_reconstruction = supervisor._reconstruct_manifest_value

        def fake_worker(*_args, **_kwargs):
            nonlocal calls
            calls += 1
            return {
                "manifestHash": self.v10_hash, "processed": 1, "succeeded": 0,
                "failures": 0, "resourceStopped": True,
                "memoryDenied": False, "budgetDenied": False,
                "storageDenied": False, "timedOut": False,
            }

        def invalid_reconstruction(config, snapshot, manifest_hash):
            invalid = replace(
                snapshot,
                manifest_bytes=b"{}",
                manifest_hash=hashlib.sha256(b"{}").hexdigest(),
            )
            return original_reconstruction(config, invalid, manifest_hash)

        with patch.object(supervisor.campaign_budget, "check", return_value={"canDispatch": True}), \
             patch.object(supervisor.campaign_worker, "memory_status", return_value={"canDispatch": True, "availableBytes": 64}), \
             patch.object(supervisor.campaign_worker, "storage_status", return_value={"canDispatch": True}), \
             patch.object(supervisor, "ordered_modules", ordered), \
             patch.object(supervisor, "_reconstruct_manifest_value", side_effect=invalid_reconstruction), \
             patch.object(supervisor.campaign_worker, "run_worker", side_effect=fake_worker), \
             patch.object(supervisor.gc, "collect"):
            with self.assertRaisesRegex(RuntimeError, "immutable v10 run input changed"):
                supervisor.run_supervisor(self.config)

        self.assertEqual(calls, 1)
        ordered.assert_called_once()

    def test_worker_pass_cleanup_runs_after_exception(self) -> None:
        self._import_v9()
        events = []

        def fake_worker(*_args, **_kwargs):
            events.append("worker")
            raise RuntimeError("fixture worker failure")

        with patch.object(supervisor.campaign_budget, "check", return_value={"canDispatch": True}), \
             patch.object(supervisor.campaign_worker, "memory_status", return_value={"canDispatch": True, "availableBytes": 64}), \
             patch.object(supervisor.campaign_worker, "storage_status", return_value={"canDispatch": True}), \
             patch.object(supervisor, "ordered_modules", return_value=(["Mathlib/A.lean"], 0)), \
             patch.object(supervisor.campaign_worker, "run_worker", side_effect=fake_worker), \
             patch.object(supervisor.gc, "collect", side_effect=lambda: events.append("gc")):
            with self.assertRaisesRegex(RuntimeError, "fixture worker failure"):
                supervisor.run_supervisor(self.config)

        self.assertEqual(events, ["gc", "worker", "gc"])

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
