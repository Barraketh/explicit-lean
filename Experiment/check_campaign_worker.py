#!/usr/bin/env python3
"""Focused worker tests; no Lean corpus subprocesses are started."""

from __future__ import annotations

import hashlib
import json
from contextlib import nullcontext
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import campaign_worker as worker
from translation_index import cache_key, claim_work, connect, import_manifest, plan_work, status


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

    def test_stale_atomic_temp_cleanup_preserves_live_owner(self) -> None:
        stale = self.root / "stale.log.tmp-99999999-1"
        live = self.root / f"live.log.tmp-{worker.os.getpid()}-2"
        stale.write_text("stale", encoding="utf-8")
        live.write_text("live", encoding="utf-8")
        real_kill = worker.os.kill
        def probe(pid: int, signal: int) -> None:
            if pid == 99999999:
                raise ProcessLookupError
            real_kill(pid, signal)
        with mock.patch.object(worker.os, "kill", side_effect=probe):
            worker._cleanup_stale_atomic_temps(self.root)
        self.assertFalse(stale.exists())
        self.assertTrue(live.exists())

    def test_macos_memory_telemetry_is_conservative(self) -> None:
        vm_stat = (
            "Mach Virtual Memory Statistics: (page size of 16384 bytes)\n"
            "Pages free: 100.\n"
            "Pages active: 5000.\n"
            "Pages inactive: 9000.\n"
            "Pages speculative: 20.\n"
        )
        completed = worker.subprocess.CompletedProcess(
            ["vm_stat"], 0, stdout=vm_stat, stderr="",
        )
        with mock.patch.object(worker.sys, "platform", "darwin"), \
             mock.patch.object(worker.subprocess, "run", return_value=completed):
            self.assertEqual(worker.available_memory_bytes(), 120 * 16384)

    def test_materializer_memory_guard_is_distinct_and_fail_closed(self) -> None:
        with mock.patch.object(
            worker, "available_memory_bytes",
            return_value=worker.DEFAULT_MINIMUM_FREE_MEMORY_BYTES - 1,
        ):
            detail = worker._materializer_memory_guard(123)
        self.assertIn("below", detail)
        with mock.patch.object(
            worker, "available_memory_bytes", side_effect=RuntimeError("no telemetry"),
        ):
            self.assertIn("telemetry unavailable", worker._materializer_memory_guard(123))

        error = worker.ProcessResourceLimitExceeded(
            ["fixture"], "fixture reserve exhausted", stdout="partial output\n",
        )
        with mock.patch.object(worker, "run_process", side_effect=error):
            code, output = worker.invoke_materializer(
                self.root / "manifest.json", self.root / "result.json",
                "Mathlib/A.lean", 10,
            )
        self.assertEqual(code, 125)
        self.assertIn("partial output", output)
        self.assertIn("stopped by memory guard: fixture reserve exhausted", output)

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

    def manifest_many(self, names: list[str], dependencies: dict[str, list[str]] | None = None) -> Path:
        dependencies = dependencies or {}
        modules = []
        for name in names:
            module = f"Mathlib/{name}.lean"
            imports = dependencies.get(name, [])
            source = "".join(f"import {item}\n" for item in imports)
            source += f"theorem {name.lower()} : True := by simp\n"
            path = self.root / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
            start = source.index("simp")
            modules.append({
                "module": module, "compiledModule": module[:-5].replace("/", "."),
                "moduleHash": "fixture-module", "sourceHash": hashlib.sha256(source.encode()).hexdigest(),
                "imports": imports,
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

    def manifest_with_roles(self, roles_by_name: dict[str, list[str]]) -> Path:
        """Make a small closed-enough fixture with deliberate role mixtures."""
        modules = []
        for name, roles in roles_by_name.items():
            module = f"Mathlib/{name}.lean"
            source = f"theorem {name.lower()} : True := by " + " ".join("simp" for _ in roles) + "\n"
            path = self.root / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
            occurrences = []
            cursor = source.index("simp")
            for role in roles:
                end = cursor + 4
                reusable = role == "reusable_executable"
                occurrences.append({
                    "id": hashlib.sha256(f"{module}:{cursor}:{end}".encode()).hexdigest()[:16],
                    "kind": "simp", "source": "simp", "startByte": cursor, "endByte": end,
                    "syntaxKind": "Lean.Parser.Tactic.simp", "action": "materialize",
                    "executionRole": role,
                    "declarationKind": "caller_dependent" if reusable else "proof",
                })
                if cursor + 4 < len(source) and len(occurrences) < len(roles):
                    cursor = source.index("simp", end)
            modules.append({
                "module": module, "compiledModule": module[:-5].replace("/", "."),
                "moduleHash": "fixture-module", "sourceHash": hashlib.sha256(source.encode()).hexdigest(),
                "occurrences": occurrences,
            })
        value = {
            "kind": "simp_engine_boundary_manifest", "reportSchema": 2,
            "allowDirty": False, "allowUnresolved": False,
            "moduleFileCount": len(modules),
            "occurrenceCount": sum(len(item["occurrences"]) for item in modules),
            "implementationHashes": {"fixture": "fixture-hash"},
            "repositoryCommit": "fixture-repository", "mathlibCommit": "fixture-mathlib",
            "lean": {"version": "4.32.2", "commit": "fixture-lean"}, "modules": modules,
        }
        result = self.root / "roles.json"
        result.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
        return result

    def complete_manifest(self, *, mutate: str | None = None) -> Path:
        """Turn the one-module fixture into a schema-2 closed manifest."""
        manifest = self.manifest()
        value = json.loads(manifest.read_text(encoding="utf-8"))
        module = value["modules"][0]
        occurrence = module["occurrences"][0]
        module_name = module["module"]
        occurrence["executionRole"] = "reusable_executable"
        occurrence["declarationKind"] = "caller_dependent"
        module.update({
            "moduleHash": hashlib.sha256(module_name.encode()).hexdigest(),
            "duplicateSyntaxRecords": 0,
            "duplicateScopeSyntaxRecords": 0,
        })
        occurrence.update({
            "line": 1, "column": 1, "ancestors": [], "commandKind": None,
            "commandStartByte": None, "commandEndByte": None,
            "scopePaths": [{
                "ancestors": [], "commandKind": None,
                "commandStartByte": None, "commandEndByte": None,
            }],
            "reason": "fixture", "declarations": [],
        })
        if mutate == "stale_source":
            occurrence["source"] = "stale"
        elif mutate == "module_hash":
            module["moduleHash"] = "invalid-module-hash"
        value.update({
            "modulePrefix": "Mathlib/", "inventoriedModuleCount": 1,
            "nestedOccurrenceCount": 0, "duplicateSyntaxRecords": 0,
            "duplicateScopeSyntaxRecords": 0, "fullFrontendFallbacks": [],
            "scopeFrontendFallbacks": [],
            "scopeProbe": {
                "module": "ExplicitLean.SimpEngine.Boundary.ScopeProbe",
                "scheduling": "set_option Elab.async false", "temporaryCopyOnly": True,
                "reportCommand": "simp_engine_boundary_scope_report",
            },
            "countsByExecutionRole": {"reusable_executable": 1},
            "countsByDeclarationKind": {"caller_dependent": 1},
            "countsByAction": {"materialize": 1},
            "manualOverrides": {
                "sha256": "0" * 64, "schema": 1,
                "environment": {
                    "mathlibCommit": value["mathlibCommit"], "lean": value["lean"],
                },
            },
        })
        result = self.root / f"complete-{mutate or 'valid'}.json"
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
        evidence_side_effect = options.pop("evidence_side_effect", None)
        budget_guard = options.pop("budget_guard", lambda: {"canDispatch": True})
        authenticate_manifest = options.pop("authenticate_manifest", False)
        schema_patch = (
            nullcontext()
            if authenticate_manifest
            else mock.patch.object(worker, "_require_closed_manifest_fields")
        )
        # Most worker-behavior fixtures intentionally exercise small manifest
        # projections.  Only tests passing authenticate_manifest=True may
        # bypass this explicit test-only mock and exercise the production
        # closed-manifest boundary.
        with schema_patch, \
             mock.patch.object(worker, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", self.boundary), \
             mock.patch.object(worker.materializer, "verify_implementation_hashes"), \
             mock.patch.object(worker.materializer, "verify_environment", return_value={"fixture": True}), \
             mock.patch.object(worker.materializer.corpus, "assert_repository"), \
             mock.patch.object(worker.materializer, "validate_shard_shape", side_effect=lambda value: value), \
             mock.patch.object(worker, "available_memory_bytes", return_value=64 * 1024**3), \
             mock.patch.object(worker, "_selected_for_report_evidence", return_value=[]), \
             mock.patch.object(
                 worker.materializer, "verify_shard_evidence",
                 side_effect=evidence_side_effect,
             ), \
             mock.patch.object(worker.materializer, "verify_manual_overlay_evidence"), \
             mock.patch.object(worker, "invoke_materializer", side_effect=invoke):
            return worker.run_worker(
                self.db, manifest, self.boundary / "runs", "worker-test",
                module_timeout=10, budget_guard=budget_guard, **options,
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

    def test_full_evidence_failure_is_not_cached_as_translated(self) -> None:
        manifest = self.manifest()

        def invoke(path, output, module, timeout):
            output.write_text(
                json.dumps(self.fake_report(manifest, module)), encoding="utf-8"
            )
            return 0, "ok"

        result = self.run_fixture(
            manifest,
            invoke,
            evidence_side_effect=RuntimeError("forged durable evidence"),
        )
        self.assertEqual(result["succeeded"], 0)
        self.assertEqual(result["failures"], 1)
        connection = connect(self.db)
        try:
            self.assertEqual(status(connection)["translated"], 0)
        finally:
            connection.close()

    def test_manual_overlay_identity_invalidates_cache_and_binds_report(self) -> None:
        manifest = self.manifest()
        overlay_path = self.root / "manual-overrides.json"
        calls: list[dict[str, object]] = []

        def identity(tag: str) -> dict[str, object]:
            return {
                "kind": "simp_manual_overlay", "schema": 2,
                "database": {"sha256": tag * 64, "schema": 1, "environment": {}},
                "environment": {},
                "counts": {"modules": 1, "canonicalOccurrences": 1,
                           "manualOverrides": 0, "untouchedOccurrences": 1},
            }

        current = identity("a")

        def invoke(path, output, module, timeout, manual_path):
            self.assertEqual(manual_path, overlay_path.resolve())
            calls.append(current)
            report = self.fake_report(manifest, module)
            report["manualOverlay"] = current
            report["modules"] = [{}]
            output.write_text(json.dumps(report), encoding="utf-8")
            return 0, "ok"

        fake_overlay = mock.Mock(identity=lambda: current)
        with mock.patch.object(worker.manual_overlay, "load_overlay", return_value=fake_overlay):
            first = self.run_fixture(
                manifest, invoke, manual_overrides=overlay_path
            )
            self.assertEqual(first["succeeded"], 1)
            current = identity("b")
            second = self.run_fixture(
                manifest, invoke, manual_overrides=overlay_path
            )
            self.assertEqual(second["succeeded"], 1)
        self.assertEqual(len(calls), 2)
        connection = connect(self.db)
        try:
            self.assertEqual(
                connection.execute("SELECT COUNT(*) FROM result_cache").fetchone()[0], 2
            )
        finally:
            connection.close()

    def test_preflight_memoizes_dependency_walk_without_changing_keys(self) -> None:
        manifest = self.manifest_many(["A", "B", "Shared"], dependencies={
            "A": ["Mathlib.Shared"], "B": ["Mathlib.Shared"],
        })
        calls: list[tuple[str, str, object, object, dict[str, str], dict[str, str]]] = []
        real_cache_key = worker.cache_key

        def capture(*args, **kwargs):
            key, dependencies = real_cache_key(*args, **kwargs)
            calls.append((args[1], key, args[2], args[3], kwargs["identity_memo"], kwargs["source_memo"]))
            return key, dependencies

        def invoke(path, output, module, timeout):
            output.write_text(json.dumps(self.fake_report(manifest, module)), encoding="utf-8")
            return 0, "ok"

        with mock.patch.object(worker, "cache_key", side_effect=capture):
            result = self.run_fixture(manifest, invoke)
        self.assertEqual(result["succeeded"], 3)
        self.assertEqual([call[0] for call in calls], ["Mathlib/A.lean", "Mathlib/B.lean", "Mathlib/Shared.lean"])
        self.assertIs(calls[0][4], calls[1][4])
        self.assertIs(calls[0][5], calls[1][5])

        connection = connect(self.db)
        try:
            for module, memoized_key, implementation, toolchain, _, _ in calls:
                plain_key, _ = real_cache_key(connection, module, implementation, toolchain)
                fresh_memo_key, _ = real_cache_key(
                    connection, module, implementation, toolchain,
                    identity_memo={}, source_memo={},
                )
                self.assertEqual(memoized_key, plain_key)
                self.assertEqual(memoized_key, fresh_memo_key)
        finally:
            connection.close()

    def test_default_selection_skips_reusable_only_module(self) -> None:
        manifest = self.manifest()
        value = json.loads(manifest.read_text(encoding="utf-8"))
        value.update({
            "countsByExecutionRole": {"reusable_executable": 1},
            "countsByDeclarationKind": {"proof": 1},
            "countsByAction": {"materialize": 1},
        })
        value["modules"][0]["occurrences"][0]["executionRole"] = "reusable_executable"
        value["modules"][0]["occurrences"][0]["declarationKind"] = "caller_dependent"
        manifest.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
        def invoke(path, output, module, timeout):
            output.write_text(json.dumps(self.fake_report(manifest, module)), encoding="utf-8")
            return 0, "ok"
        with mock.patch.object(worker, "_write_manifest_capsule", side_effect=AssertionError("unexpected capsule")):
            result = self.run_fixture(manifest, invoke)
        self.assertEqual(result["processed"], 0)
        self.assertEqual(result["selected"], 0)
        self.assertEqual(result["skippedReusable"], 1)

    def test_default_selection_excludes_mixed_and_reusable_modules(self) -> None:
        manifest = self.manifest_with_roles({
            "Mixed": ["direct_executable", "reusable_executable"],
            "Reusable": ["reusable_executable"],
            "Direct": ["direct_executable"],
        })
        calls: list[str] = []

        def invoke(path, output, module, timeout):
            calls.append(module)
            output.write_text(json.dumps(self.fake_report(manifest, module)), encoding="utf-8")
            return 0, "ok"

        result = self.run_fixture(manifest, invoke)
        self.assertEqual(calls, ["Mathlib/Direct.lean"])
        self.assertEqual(result["selected"], 1)
        self.assertEqual(result["processed"], 1)
        self.assertEqual(result["skippedReusable"], 2)
        self.assertEqual(result["skippedEmpty"], 0)

    def test_explicit_reusable_selection_fails_with_exact_ids_before_dispatch(self) -> None:
        manifest = self.manifest_with_roles({"Reusable": ["reusable_executable"]})
        occurrence_id = json.loads(manifest.read_text(encoding="utf-8"))["modules"][0]["occurrences"][0]["id"]
        invoke = mock.Mock(side_effect=AssertionError("reusable module was dispatched"))
        with self.assertRaisesRegex(
            RuntimeError,
            rf"selected module contains reusable_executable occurrences: Mathlib/Reusable\.lean: \['{occurrence_id}'\]",
        ):
            self.run_fixture(manifest, invoke, modules=["Mathlib/Reusable.lean"])
        invoke.assert_not_called()

    def test_malformed_occurrence_fails_closed_before_selection(self) -> None:
        manifest = self.manifest()
        value = json.loads(manifest.read_text(encoding="utf-8"))
        value["modules"][0]["occurrences"] = [None]
        with self.assertRaisesRegex(RuntimeError, "invalid manifest occurrence.*occurrence must be an object"):
            worker._selected_modules(value, None)

    def test_reusable_only_invalid_manifest_rejected_before_budget_decision(self) -> None:
        for mutation, expected in (
            ("stale_source", "stale inventory"),
            ("module_hash", "module hash mismatch"),
        ):
            errors = []
            for can_dispatch in (False, True):
                manifest = self.complete_manifest(mutate=mutation)
                invoke = mock.Mock(side_effect=AssertionError("reusable module was dispatched"))
                with self.subTest(mutation=mutation, can_dispatch=can_dispatch):
                    with self.assertRaisesRegex(RuntimeError, expected) as raised:
                        self.run_fixture(
                            manifest,
                            invoke,
                            authenticate_manifest=True,
                            budget_guard=lambda: {"canDispatch": can_dispatch},
                        )
                    errors.append(str(raised.exception))
                invoke.assert_not_called()
            self.assertEqual(errors[0], errors[1])

    def test_incomplete_manifest_rejected_before_budget_decision(self) -> None:
        errors = []
        for can_dispatch in (False, True):
            manifest = self.complete_manifest()
            value = json.loads(manifest.read_text(encoding="utf-8"))
            value.pop("modulePrefix")
            value["modules"][0]["moduleHash"] = "invalid-module-hash"
            manifest.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
            invoke = mock.Mock(side_effect=AssertionError("incomplete manifest dispatched"))
            with self.subTest(can_dispatch=can_dispatch):
                with self.assertRaisesRegex(
                    RuntimeError,
                    r"exact closed manifest fields: missing=\['modulePrefix'\]",
                ) as raised:
                    self.run_fixture(
                        manifest,
                        invoke,
                        authenticate_manifest=True,
                        budget_guard=lambda: {"canDispatch": can_dispatch},
                    )
                errors.append(str(raised.exception))
            invoke.assert_not_called()
        self.assertEqual(errors[0], errors[1])

    def test_terminal_error_text_in_field_is_not_swallowed(self) -> None:
        errors = []
        for can_dispatch in (False, True):
            manifest = self.complete_manifest()
            value = json.loads(manifest.read_text(encoding="utf-8"))
            module = value["modules"][0]
            occurrence_id = module["occurrences"][0]["id"]
            module["compiledModule"] = (
                "selected module contains reusable_executable, which this runner does not "
                f"support: {module['module']}: ['{occurrence_id}']"
            )
            manifest.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
            invoke = mock.Mock(side_effect=AssertionError("forged manifest dispatched"))
            with self.subTest(can_dispatch=can_dispatch):
                with self.assertRaisesRegex(RuntimeError, "compiled module mismatch") as raised:
                    self.run_fixture(
                        manifest,
                        invoke,
                        authenticate_manifest=True,
                        budget_guard=lambda: {"canDispatch": can_dispatch},
                    )
                errors.append(str(raised.exception))
            invoke.assert_not_called()
        self.assertEqual(errors[0], errors[1])

    def test_explicit_direct_only_selection_dispatches(self) -> None:
        manifest = self.manifest_with_roles({"Direct": ["direct_executable"]})
        calls: list[str] = []

        def invoke(path, output, module, timeout):
            calls.append(module)
            output.write_text(json.dumps(self.fake_report(manifest, module)), encoding="utf-8")
            return 0, "ok"

        result = self.run_fixture(manifest, invoke, modules=["Mathlib/Direct.lean"])
        self.assertEqual(calls, ["Mathlib/Direct.lean"])
        self.assertEqual(result["selected"], 1)
        self.assertEqual(result["skippedReusable"], 0)

    def test_fresh_pass_rejects_changed_dependency_source(self) -> None:
        manifest = self.manifest_many(["A", "B"], dependencies={"A": ["Mathlib.B"]})
        connection = connect(self.db)
        try:
            import_manifest(connection, manifest, source_root=self.root)
            source = self.root / "Mathlib/B.lean"
            original = source.read_text(encoding="utf-8")
            try:
                source.write_text(original + "-- changed after import\n", encoding="utf-8")
                with self.assertRaisesRegex(RuntimeError, "source changed after import"):
                    cache_key(
                        connection, "Mathlib/A.lean", "impl", "tool",
                        identity_memo={}, source_memo={},
                    )
            finally:
                source.write_text(original, encoding="utf-8")
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
             mock.patch.object(worker, "_require_closed_manifest_fields"), \
             mock.patch.object(worker.materializer, "verify_implementation_hashes"), \
             mock.patch.object(worker.materializer, "verify_environment", return_value={"fixture": True}), \
             mock.patch.object(worker.materializer.corpus, "assert_repository"), \
             mock.patch.object(worker, "invoke_materializer", side_effect=failing):
            worker.run_worker(self.db, manifest, self.boundary / "runs", "worker-test", retry_failed=True, budget_guard=lambda: {"canDispatch": True})
        self.assertEqual(calls, 2)

    def test_memory_stop_keeps_log_and_requeues_without_result_failure(self) -> None:
        manifest = self.manifest_many(["A", "B"])
        calls: list[str] = []

        def stopped(path, output, module, timeout):
            calls.append(module)
            return 125, "child output before resource stop\n"

        result = self.run_fixture(manifest, stopped)
        self.assertEqual(result["processed"], 1)
        self.assertEqual(calls, ["Mathlib/A.lean"])
        self.assertEqual(result["candidates"], 2)
        self.assertEqual(result["failures"], 0)
        self.assertTrue(result["resourceStopped"])
        connection = connect(self.db)
        try:
            attempt = connection.execute("SELECT status,failure FROM attempts").fetchone()
            self.assertEqual(attempt["status"], "abandoned")
            self.assertIn("exit 125", attempt["failure"])
            states = connection.execute(
                "SELECT module,state FROM work_queue ORDER BY module"
            ).fetchall()
            self.assertEqual([(row["module"], row["state"]) for row in states], [
                ("Mathlib/A.lean", "queued"), ("Mathlib/B.lean", "queued"),
            ])
            self.assertIsNone(connection.execute("SELECT * FROM result_cache").fetchone())
            log_ref = self.root / "boundary-materialization" / "runs"
            logs = list(log_ref.glob("*.log"))
            self.assertEqual(len(logs), 1)
            self.assertEqual(logs[0].read_text(encoding="utf-8"), "child output before resource stop\n")
        finally:
            connection.close()

    def test_preclaim_memory_admission_stops_before_claim(self) -> None:
        manifest = self.manifest()
        calls = 0

        def invoke(path, output, module, timeout):
            nonlocal calls
            calls += 1
            return 125, "should not run"

        denied = {
            "canDispatch": False, "availableBytes": 1,
            "minimumFreeMemoryBytes": worker.DEFAULT_MINIMUM_FREE_MEMORY_BYTES,
        }
        with mock.patch.object(worker, "memory_status", return_value=denied):
            result = self.run_fixture(manifest, invoke)
        self.assertTrue(result["memoryDenied"])
        self.assertFalse(result["resourceStopped"])
        self.assertEqual(result["processed"], 0)
        self.assertEqual(calls, 0)
        connection = connect(self.db)
        try:
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM attempts").fetchone()[0], 0)
            self.assertEqual(connection.execute("SELECT state FROM work_queue").fetchone()[0], "queued")
        finally:
            connection.close()

    def test_keyboard_interrupt_abandons_claimed_lease(self) -> None:
        manifest = self.manifest()

        def interrupt(path, output, module, timeout):
            raise KeyboardInterrupt()

        with self.assertRaises(KeyboardInterrupt):
            self.run_fixture(manifest, interrupt)
        connection = connect(self.db)
        try:
            attempt = connection.execute("SELECT status,failure FROM attempts").fetchone()
            self.assertEqual(attempt["status"], "abandoned")
            self.assertIn("KeyboardInterrupt", attempt["failure"])
            self.assertEqual(connection.execute("SELECT state FROM work_queue").fetchone()[0], "queued")
            self.assertIsNone(connection.execute("SELECT * FROM result_cache").fetchone())
        finally:
            connection.close()

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

    def test_retry_limit_does_not_starve_never_attempted_modules(self) -> None:
        manifest = self.manifest_many(["A", "B", "C", "D"])
        calls: list[str] = []

        def invoke(path, output, module, timeout):
            calls.append(module)
            if module.endswith("A.lean"):
                return 1, "persistent failure"
            output.write_text(json.dumps(self.fake_report(
                manifest, module, unobserved=module.endswith("B.lean")
            )), encoding="utf-8")
            return 0, "ok"

        first = self.run_fixture(manifest, invoke, max_modules=2)
        self.assertEqual(first["processed"], 2)
        second = self.run_fixture(manifest, invoke, max_modules=2, retry_failed=True)
        self.assertEqual(second["processed"], 2)
        self.assertEqual(calls, [
            "Mathlib/A.lean", "Mathlib/B.lean", "Mathlib/C.lean", "Mathlib/D.lean",
        ])
        third = self.run_fixture(manifest, invoke, max_modules=2, retry_failed=True)
        self.assertEqual(third["processed"], 2)
        self.assertEqual(calls[-2:], ["Mathlib/A.lean", "Mathlib/B.lean"])

    def test_budget_denial_and_default_empty_module_skip(self) -> None:
        manifest = self.manifest(empty=True)
        with mock.patch.object(worker, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "MATHLIB", self.root), \
             mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", self.boundary), \
             mock.patch.object(worker, "_require_closed_manifest_fields"), \
             mock.patch.object(worker.materializer, "verify_implementation_hashes"):
            result = worker.run_worker(self.db, manifest, self.boundary / "runs", "worker-test", budget_guard=lambda: {"canDispatch": False})
        self.assertEqual(result["skippedEmpty"], 1)
        self.assertEqual(result["processed"], 0)
        with self.assertRaisesRegex(RuntimeError, "diagnostic manifests"):
            with mock.patch.object(worker, "_require_closed_manifest_fields"), \
                 mock.patch.object(worker.materializer, "verify_implementation_hashes"):
                worker.run_worker(self.db, self.manifest(allow_unresolved=True), self.boundary / "runs", "worker-test", budget_guard=lambda: {"canDispatch": True})


    def test_protect_inputs_and_preflight_before_index_mutation(self) -> None:
        manifest = self.manifest()
        with mock.patch.object(worker, "_require_closed_manifest_fields"), \
             mock.patch.object(worker.materializer, "verify_implementation_hashes"), \
             mock.patch.object(worker.materializer, "BOUNDARY_DEBUG_ROOT", self.root), \
             mock.patch.object(worker.materializer.corpus, "assert_repository", side_effect=RuntimeError("moving_ref")):
            with self.assertRaisesRegex(RuntimeError, "manifest must not"):
                worker.run_worker(self.db, manifest, self.root, "test", budget_guard=lambda: {"canDispatch": True})
            with self.assertRaisesRegex(RuntimeError, "database must not"):
                worker.run_worker(self.boundary / "database", manifest, self.boundary, "test", budget_guard=lambda: {"canDispatch": True})
            with mock.patch.object(
                worker.manual_overlay, "load_overlay",
                return_value=mock.Mock(identity=lambda: {}),
            ):
                with self.assertRaisesRegex(RuntimeError, "manual override database must not"):
                    worker.run_worker(
                        self.db, manifest, self.boundary, "test",
                        manual_overrides=self.boundary / "manual.json",
                        budget_guard=lambda: {"canDispatch": True},
                    )
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
