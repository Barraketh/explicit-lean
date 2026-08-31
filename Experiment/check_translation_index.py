#!/usr/bin/env python3
"""Focused tests for :mod:`translation_index`.

The fixtures are deliberately tiny.  They exercise database identity and lease
semantics without compiling the Mathlib corpus.
"""

from __future__ import annotations

import json
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from translation_index import (
    abandon_lease,
    claim_work,
    connect,
    import_manifest,
    occurrence_id,
    plan_work,
    order_retryable,
    record_result,
    status,
    _imports,
)


class TranslationIndexTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="translation-index-")
        self.root = Path(self.temp.name)
        (self.root / "Mathlib").mkdir()
        self.database = self.root / "index.sqlite3"
        self.connection = connect(self.database)

    def tearDown(self) -> None:
        self.connection.close()
        self.temp.cleanup()

    def test_retry_ordering_chunks_large_module_sets(self) -> None:
        modules = [f"Mathlib/M{i}.lean" for i in range(1001)]
        self.connection.executemany(
            "INSERT INTO work_queue(module,cache_key,state,updated_at) VALUES (?, ?, 'queued', 0)",
            [(module, f"key-{module}") for module in modules],
        )
        ordered = order_retryable(
            self.connection, modules, cache_keys={module: f"key-{module}" for module in modules},
        )
        self.assertEqual(ordered, modules)

    def test_retry_ordering_ignores_attempts_from_old_cache_key(self) -> None:
        modules = ["Mathlib/Changed.lean", "Mathlib/Retried.lean"]
        self.connection.executemany(
            "INSERT INTO work_queue(module,cache_key,state,updated_at) VALUES (?, ?, 'queued', 0)",
            [(modules[0], "new-key"), (modules[1], "same-key")],
        )
        self.connection.executemany(
            "INSERT INTO attempts(module,cache_key,worker,status,started_at) VALUES (?, ?, 'fixture', 'failure', ?)",
            [(modules[0], "old-key", 1), (modules[1], "same-key", 2)],
        )
        ordered = order_retryable(
            self.connection, modules,
            cache_keys={modules[0]: "new-key", modules[1]: "same-key"},
        )
        self.assertEqual(ordered, modules)

    def write_manifest(self, sources: dict[str, str], *, manifest_name: str = "manifest.json", unresolved: bool = False) -> Path:
        modules = []
        for module, source in sorted(sources.items()):
            path = self.root / module
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
            source_bytes = source.encode()
            occurrences = []
            marker = "simp"
            start = source.find(marker)
            if start >= 0:
                end = start + len(marker)
                occurrences.append({
                    "id": occurrence_id(module, start, end),
                    "kind": "simp",
                    "source": marker,
                    "startByte": start,
                    "endByte": end,
                    "syntaxKind": "Lean.Parser.Tactic.simp",
                    "action": "unresolved" if unresolved else "materialize",
                    "executionRole": "unresolved" if unresolved else "direct_executable",
                    "declarationKind": "unknown" if unresolved else "proof",
                    "disposition": "eligible",
                })
            modules.append({
                "module": module,
                "compiledModule": module[:-5].replace("/", "."),
                "moduleHash": "compiled-" + module,
                "sourceHash": hashlib.sha256(source_bytes).hexdigest(),
                "occurrences": occurrences,
            })
        manifest = {
            "kind": "simp_engine_boundary_manifest",
            "reportSchema": 2,
            "allowDirty": False,
            "allowUnresolved": unresolved,
            "moduleFileCount": len(modules),
            "occurrenceCount": sum(len(module["occurrences"]) for module in modules),
            "modules": modules,
        }
        path = self.root / manifest_name
        path.write_text(json.dumps(manifest, sort_keys=True), encoding="utf-8")
        return path

    def import_sources(self, sources: dict[str, str], *, manifest_name: str = "manifest.json", unresolved: bool = False) -> None:
        import_manifest(self.connection, self.write_manifest(sources, manifest_name=manifest_name, unresolved=unresolved), source_root=self.root, diagnostic=unresolved)

    def test_idempotent_import_preserves_validated_occurrences(self) -> None:
        sources = {"Mathlib/A.lean": "theorem a : True := by simp\n"}
        manifest = self.write_manifest(sources)
        first = import_manifest(self.connection, manifest, source_root=self.root)
        second = import_manifest(self.connection, manifest, source_root=self.root)
        self.assertEqual(first["manifestHash"], second["manifestHash"])
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM modules").fetchone()[0], 1)
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM occurrences").fetchone()[0], 1)
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM imports").fetchone()[0], 0)

    def test_exact_header_dependency_map_is_source_bound_and_complete(self) -> None:
        sources = {
            "Mathlib/A.lean": "import Mathlib.B\ntheorem a : True := by simp\n",
            "Mathlib/B.lean": "theorem b : True := by simp\n",
        }
        manifest = self.write_manifest(sources)
        payload = json.loads(manifest.read_text(encoding="utf-8"))
        dependency_map = {
            f"{record['module']}@{record['sourceHash']}": {
                "module": record["module"],
                "sourceHash": record["sourceHash"],
                "dependencies": ["Mathlib.B"] if record["module"] == "Mathlib/A.lean" else [],
            }
            for record in payload["modules"]
        }
        import_manifest(self.connection, manifest, source_root=self.root, dependency_map=dependency_map)
        self.assertEqual(
            self.connection.execute(
                "SELECT dependency FROM imports WHERE module='Mathlib/A.lean'"
            ).fetchone()[0],
            "Mathlib/B.lean",
        )
        missing = dict(dependency_map)
        del missing[next(iter(missing))]
        other = connect(self.root / "missing.sqlite3")
        try:
            with self.assertRaisesRegex(RuntimeError, "dependency map is missing"):
                import_manifest(other, manifest, source_root=self.root, dependency_map=missing)
        finally:
            other.close()

    def test_compiled_module_must_match_source_path(self) -> None:
        manifest = self.write_manifest({"Mathlib/A.lean": "theorem a : True := by simp\n"})
        payload = json.loads(manifest.read_text(encoding="utf-8"))
        payload["modules"][0]["compiledModule"] = "Mathlib.Wrong"
        bad = self.root / "bad-compiled.json"
        bad.write_text(json.dumps(payload), encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "compiledModule disagrees"):
            import_manifest(self.connection, bad, source_root=self.root)

    def test_identity_changes_and_transitive_dependency_invalidate_only_dependents(self) -> None:
        sources = {
            "Mathlib/A.lean": "import Mathlib.B\ntheorem a : True := by simp\n",
            "Mathlib/B.lean": "theorem b : True := by simp\n",
            "Mathlib/I.lean": "theorem i : True := by simp\n",
        }
        self.import_sources(sources)
        plan = plan_work(self.connection, {"implementation": 1}, "lean-1")
        keys = {entry["module"]: entry["cacheKey"] for entry in plan}
        for module in sources:
            record_result(self.connection, module, {"implementation": 1}, "lean-1", status="success", translated=True)
        self.assertEqual(status(self.connection)["translated"], 0)
        self.assertEqual(plan_work(self.connection, {"implementation": 1}, "lean-1")[2]["state"], "queued")
        record_result(self.connection, "Mathlib/I.lean", {"implementation": 1}, "lean-1", status="success", translated=True, verified=True)
        self.assertEqual(status(self.connection)["translated"], 1)
        record_result(self.connection, "Mathlib/I.lean", {"implementation": 1}, "lean-1", status="failure", translated=True, verified=True)
        self.assertEqual(status(self.connection)["translated"], 0)
        record_result(self.connection, "Mathlib/I.lean", {"implementation": 1}, "lean-1", status="success", translated=True, verified=True)
        # A source change changes B's identity and A's transitive dependency
        # identity, but leaves the independent module's cache reusable.
        sources["Mathlib/B.lean"] = "theorem b : True := by\n  simp\n"
        self.import_sources(sources, manifest_name="manifest-v2.json")
        refreshed = {entry["module"]: entry for entry in plan_work(self.connection, {"implementation": 1}, "lean-1")}
        self.assertEqual(refreshed["Mathlib/A.lean"]["state"], "queued")
        self.assertEqual(refreshed["Mathlib/B.lean"]["state"], "queued")
        self.assertEqual(refreshed["Mathlib/I.lean"]["state"], "succeeded")
        # Implementation and toolchain identities are part of the key too.
        self.assertNotEqual(
            keys["Mathlib/I.lean"],
            plan_work(self.connection, {"implementation": 2}, "lean-1")[2]["cacheKey"],
        )
        self.assertNotEqual(
            keys["Mathlib/I.lean"],
            plan_work(self.connection, {"implementation": 1}, "lean-2")[2]["cacheKey"],
        )

    def test_expired_lease_becomes_abandoned_and_can_be_reclaimed(self) -> None:
        self.import_sources({"Mathlib/A.lean": "theorem a : True := by simp\n"})
        plan_work(self.connection, "impl", "tool")
        first = claim_work(self.connection, "worker-1", lease_seconds=10, now=100)
        self.assertEqual(len(first), 1)
        with self.assertRaisesRegex(RuntimeError, "lease expired"):
            record_result(self.connection, "Mathlib/A.lean", "impl", "tool", status="success", attempt_id=first[0].attempt_id, worker="worker-1", now=111)
        second = claim_work(self.connection, "worker-2", lease_seconds=10, now=111)
        self.assertEqual(len(second), 1)
        self.assertNotEqual(first[0].attempt_id, second[0].attempt_id)
        self.assertEqual(
            self.connection.execute("SELECT status FROM attempts WHERE attempt_id=?", (first[0].attempt_id,)).fetchone()[0],
            "abandoned",
        )
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM attempts").fetchone()[0], 2)

    def test_abandon_lease_requeues_without_result_cache_and_checks_owner(self) -> None:
        self.import_sources({"Mathlib/A.lean": "theorem a : True := by simp\n"})
        plan = plan_work(self.connection, "impl", "tool")
        lease = claim_work(self.connection, "worker-1", now=100)[0]
        with self.assertRaisesRegex(RuntimeError, "owned by another worker"):
            abandon_lease(self.connection, lease.attempt_id, "worker-2", "interrupt", now=101)
        abandon_lease(self.connection, lease.attempt_id, "worker-1", "interrupt", now=101)
        attempt = self.connection.execute("SELECT status,failure,finished_at FROM attempts").fetchone()
        self.assertEqual(tuple(attempt), ("abandoned", "interrupt", 101))
        queue = self.connection.execute("SELECT state,worker,last_attempt_id FROM work_queue").fetchone()
        self.assertEqual(tuple(queue), ("queued", None, lease.attempt_id))
        self.assertIsNone(self.connection.execute("SELECT * FROM result_cache").fetchone())

    def test_source_edit_requires_a_refreshed_manifest(self) -> None:
        self.import_sources({"Mathlib/A.lean": "theorem a : True := by simp\n"})
        (self.root / "Mathlib/A.lean").write_text("theorem a : True := by\n  simp\n", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "refreshed manifest"):
            plan_work(self.connection, "impl", "tool")

    def test_same_source_reclassification_versions_analysis_and_invalidates_result(self) -> None:
        manifest = self.write_manifest({"Mathlib/A.lean": "theorem a : True := by simp\n"})
        import_manifest(self.connection, manifest, source_root=self.root)
        initial_key = plan_work(self.connection, "impl", "tool")[0]["cacheKey"]
        record_result(self.connection, "Mathlib/A.lean", "impl", "tool", status="success", translated=True, verified=True)
        self.assertEqual(status(self.connection)["translated"], 1)
        changed = json.loads(manifest.read_text(encoding="utf-8"))
        changed["modules"][0]["occurrences"][0]["classification"] = "improved_scope_pass"
        updated = self.root / "manifest-reclassified.json"
        updated.write_text(json.dumps(changed, sort_keys=True), encoding="utf-8")
        import_manifest(self.connection, updated, source_root=self.root)
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM occurrence_facts").fetchone()[0], 1)
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM occurrence_analyses").fetchone()[0], 2)
        self.assertEqual(self.connection.execute("SELECT classification FROM occurrences").fetchone()[0], "improved_scope_pass")
        self.assertEqual(status(self.connection)["translated"], 0)
        refreshed = plan_work(self.connection, "impl", "tool")[0]
        self.assertEqual(refreshed["state"], "queued")
        self.assertNotEqual(refreshed["cacheKey"], initial_key)
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM result_cache").fetchone()[0], 1)

    def test_diagnostic_manifest_keeps_unresolved_backlog_and_never_verifies(self) -> None:
        self.import_sources({"Mathlib/A.lean": "theorem a : True := by simp\n"}, unresolved=True)
        self.assertEqual(self.connection.execute("SELECT COUNT(*) FROM unresolved_backlog").fetchone()[0], 1)
        plan_work(self.connection, "impl", "tool")
        record_result(self.connection, "Mathlib/A.lean", "impl", "tool", status="success", translated=True)
        self.assertEqual(self.connection.execute("SELECT state FROM work_queue").fetchone()[0], "queued")
        self.assertEqual(len(claim_work(self.connection, "worker")), 1)
        with self.assertRaisesRegex(RuntimeError, "unresolved occurrences"):
            record_result(self.connection, "Mathlib/A.lean", "impl", "tool", status="success", translated=True, verified=True)
        self.assertEqual(status(self.connection)["translated"], 0)

    def test_diamond_dependencies_share_identity_source_reads(self) -> None:
        sources = {
            "Mathlib/D.lean": "import Mathlib.B Mathlib.C\ntheorem d : True := by simp\n",
            "Mathlib/B.lean": "import Mathlib.A\ntheorem b : True := by simp\n",
            "Mathlib/C.lean": "import Mathlib.A\ntheorem c : True := by simp\n",
            "Mathlib/A.lean": "theorem a : True := by simp\n",
        }
        self.import_sources(sources)
        reads = 0
        original = Path.read_bytes
        target = (self.root / "Mathlib/A.lean").resolve()

        def counted(path: Path) -> bytes:
            nonlocal reads
            if path.resolve() == target:
                reads += 1
            return original(path)

        with mock.patch.object(Path, "read_bytes", counted):
            plan_work(self.connection, "impl", "tool")
        self.assertLessEqual(reads, 2, "shared diamond dependency was reread per transitive path")

    def test_import_header_lexer_handles_nested_comments_and_multiline_imports(self) -> None:
        source = """/- comment with -- import Fake
           /- nested -/ and a hyphen -/
module

public meta import Mathlib.A
import
  Mathlib.B
import Mathlib.D
import all Lean.Elab.Tactic.Induction
import Mathlib.C -- import Mathlib.Fake
namespace N
"""
        self.assertEqual(_imports(source), ["Lean.Elab.Tactic.Induction", "Mathlib.A", "Mathlib.B", "Mathlib.C", "Mathlib.D"])
        self.assertEqual(_imports("public/-c-/meta/-c-/import Mathlib.A\n"), ["Mathlib.A"])
        with self.assertRaisesRegex(RuntimeError, "unsupported multiline import header"):
            _imports("import Mathlib.D\n  Mathlib.E\n")
        with self.assertRaisesRegex(RuntimeError, "unsupported import header"):
            _imports("module\nimport Mathlib.A where\n")


if __name__ == "__main__":
    raise SystemExit(unittest.main())
