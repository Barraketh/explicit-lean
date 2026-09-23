#!/usr/bin/env python3
"""Focused tests for per-site missing-trace recovery."""

from __future__ import annotations

import contextlib
import io
import pathlib
import os
import sqlite3
import tempfile
import unittest

import retry_missing_traces as retry


class MissingTraceRetryTests(unittest.TestCase):
    def test_missing_sites_are_source_ordered_and_command_scoped(self) -> None:
        self.assertEqual(
            retry.missing_site_ordinals([2, 5, 8], {2}, {8}), [5]
        )
        with self.assertRaises(retry.RetryError):
            retry.missing_site_ordinals([2, 5], {8}, set())

    def test_duplicate_or_unsorted_expected_sites_fail_closed(self) -> None:
        with self.assertRaises(retry.RetryError):
            retry.missing_site_ordinals([2, 2], set(), set())
        with self.assertRaises(retry.RetryError):
            retry.missing_site_ordinals([5, 2], set(), set())

    def test_status_selection_is_explicit_and_failed_rows_remain_audit_gated(self) -> None:
        self.assertEqual(retry.parse_statuses("record_failed"), ("record_failed",))
        self.assertEqual(retry.parse_statuses("pending,record_failed"),
                         ("pending", "record_failed"))
        self.assertEqual(retry.parse_statuses("render_failed,compile_failed"),
                         ("render_failed", "compile_failed"))
        with self.assertRaises(retry.RetryError):
            retry.parse_statuses("success")
        db = sqlite3.connect(":memory:")
        db.executescript("""
          CREATE TABLE simp_replacements(module_name TEXT, ordinal INTEGER,
            status TEXT, error TEXT);
          CREATE TABLE modules(name TEXT, source_sha256 TEXT);
          CREATE TABLE isolated_trace_audit(module_name TEXT, ordinal INTEGER,
            result_status TEXT, trace_state TEXT);
          CREATE TABLE isolated_trace_command_retry(module_name TEXT, ordinal INTEGER,
            source_sha256 TEXT, result_status TEXT);
          INSERT INTO modules VALUES('Mathlib.X','hash');
          INSERT INTO simp_replacements VALUES
            ('Mathlib.X',1,'pending',NULL),
            ('Mathlib.X',2,'record_failed','missing trace'),
            ('Mathlib.X',3,'record_failed','not audit eligible'),
            ('Mathlib.X',4,'compile_failed','gated compile failure'),
            ('Mathlib.X',5,'compile_failed','not audited compile failure'),
            ('Mathlib.X',6,'render_failed','stale source audit'),
            ('Mathlib.X',7,'record_failed','exact trace failure'),
            ('Mathlib.X',8,'compile_failed','baseline inconclusive'),
            ('Mathlib.X',9,'render_failed','baseline inconclusive');
          INSERT INTO isolated_trace_audit VALUES
            ('Mathlib.X',2,'record_failed','no_trace'),
            ('Mathlib.X',3,'success','complete');
          INSERT INTO isolated_trace_command_retry VALUES
            ('Mathlib.X',4,'hash','compile_failed'),
            ('Mathlib.X',6,'old-hash','render_failed'),
            ('Mathlib.X',7,'hash','trace_failed'),
            ('Mathlib.X',8,'hash','baseline_failed'),
            ('Mathlib.X',9,'hash','baseline_failed');
        """)
        self.assertEqual(retry._candidate_rows(db, None, ("record_failed",)),
                         [("Mathlib.X", 2, "record_failed", "missing trace"),
                          ("Mathlib.X", 7, "record_failed", "exact trace failure")])
        self.assertEqual(retry._candidate_rows(db, None, ("pending",)),
                         [("Mathlib.X", 1, "pending", None)])
        self.assertEqual(
            retry._candidate_rows(db, None, ("pending", "record_failed")),
            [("Mathlib.X", 1, "pending", None),
             ("Mathlib.X", 2, "record_failed", "missing trace"),
             ("Mathlib.X", 7, "record_failed", "exact trace failure")],
        )
        self.assertEqual(retry._candidate_rows(db, None, ("compile_failed",)),
                         [("Mathlib.X", 4, "compile_failed", "gated compile failure"),
                          ("Mathlib.X", 8, "compile_failed", "baseline inconclusive")])
        self.assertEqual(retry._candidate_rows(db, None, ("render_failed",)),
                         [("Mathlib.X", 9, "render_failed", "baseline inconclusive")])
        db.close()

    def test_manifest_is_authoritative_for_sharded_work(self) -> None:
        manifest = {"Mathlib.A", "Mathlib.B"}
        self.assertEqual(retry.resolve_module_selection(manifest, set()), manifest)
        self.assertEqual(retry.resolve_module_selection(manifest, {"Mathlib.B"}),
                         {"Mathlib.B"})
        with self.assertRaises(retry.RetryError):
            retry.resolve_module_selection(manifest, {"Mathlib.C"})
        with self.assertRaisesRegex(retry.RetryError, "contains no modules"):
            retry.resolve_module_selection(set(), set())
        with self.assertRaisesRegex(retry.RetryError, "provide either"):
            retry.resolve_module_selection(None, set())

    def test_pending_false_positive_is_noop_but_failed_row_without_site_fails_closed(self) -> None:
        pending = ("Mathlib.X", 10, "pending", None)
        failed = ("Mathlib.X", 11, "record_failed", "audit error")
        self.assertEqual(retry.partition_source_site_rows([pending], {}), ([], [pending]))
        self.assertEqual(
            retry.partition_source_site_rows([pending], {10: [3]}),
            ([pending], []),
        )
        with self.assertRaisesRegex(retry.RetryError, "record_failed command has no detected"):
            retry.partition_source_site_rows([failed], {})

    def test_target_site_without_command_owner_fails_closed(self) -> None:
        with self.assertRaisesRegex(retry.RetryError, "no command owner"):
            retry._renderer_pairs("theorem t : True := by simp\n", [])

    def test_cli_requires_explicit_module_or_manifest(self) -> None:
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                retry.main(["--database", "missing.sqlite3",
                            "--artifacts-root", "missing-artifacts",
                            "--scratch", "missing-scratch"])
        with tempfile.TemporaryDirectory(dir=retry.RUN_ROOT) as directory:
            manifest = pathlib.Path(directory) / "empty.txt"
            manifest.write_text("", encoding="utf-8")
            database = pathlib.Path(directory) / "must-not-be-created.sqlite3"
            with contextlib.redirect_stderr(io.StringIO()):
                result = retry.main([
                    "--database", str(database), "--artifacts-root", "missing-artifacts",
                    "--scratch", str(pathlib.Path(directory) / "scratch"),
                    "--manifest", str(manifest),
                ])
            self.assertEqual(result, 1)
            self.assertFalse(database.exists())

    def test_placeholder_guard_uses_lean_tokens(self) -> None:
        self.assertTrue(retry.placeholder_token("by sorry"))
        self.assertTrue(retry.placeholder_token("admit"))
        self.assertFalse(retry.placeholder_token("sorryAx sorryAxName"))
        self.assertFalse(retry.placeholder_token("admitted"))

    def test_database_guard_rejects_snapshot_and_out_of_scope_paths(self) -> None:
        with tempfile.TemporaryDirectory(dir=retry.RUN_ROOT) as directory:
            writable = pathlib.Path(directory) / "copy.sqlite3"
            writable.touch()
            self.assertEqual(retry.read_only_snapshot_guard(writable), writable.resolve())
        frozen = retry.SNAPSHOT_ROOT / "job-000.sqlite3"
        with self.assertRaises(retry.RetryError):
            retry.read_only_snapshot_guard(frozen)
        with tempfile.NamedTemporaryFile() as outside:
            with self.assertRaises(retry.RetryError):
                retry.read_only_snapshot_guard(pathlib.Path(outside.name))
        with tempfile.TemporaryDirectory(dir=retry.RUN_ROOT) as directory:
            original = pathlib.Path(directory) / "db.sqlite3"
            linked = pathlib.Path(directory) / "linked.sqlite3"
            original.touch()
            try:
                os.link(original, linked)
            except OSError as exc:
                self.skipTest(f"hard links unavailable: {exc}")
            with self.assertRaisesRegex(retry.RetryError, "hard link"):
                retry.read_only_snapshot_guard(linked)

    def test_per_site_results_commit_and_resume(self) -> None:
        db = sqlite3.connect(":memory:")
        db.execute(retry.RETRY_SCHEMA)
        source = "theorem t : True := by simp\n"
        site = retry.worker.align_sites(source)[1][0]
        record = self.trace_record("Mathlib/X.lean", site)
        trace_json = retry.json.dumps([record])
        values = ("Mathlib.X", 4, site.siteOrdinal, "a" * 64, site.callText, "recorded",
                  trace_json, None,
                  "2026-09-23T00:00:00+00:00")
        retry._persist_site(db, values)
        db.commit()
        owners = {site.siteOrdinal: 4}
        sites = {site.siteOrdinal: site}
        traces = retry._load_retried_traces(
            db, "Mathlib.X", "a" * 64, "Mathlib/X.lean", source, owners, sites)
        self.assertEqual(traces, {site.siteOrdinal: [record]})
        self.assertEqual(db.execute(
            "SELECT status,trace_json FROM isolated_trace_site_retry"
        ).fetchone(), ("recorded", trace_json))
        bad_values = ("Mathlib.X", 5, 10, "b" * 64, site.callText, "recorded",
                      '[{"proof":"by sorry"}]', None,
                      "2026-09-23T00:00:00+00:00")
        with self.assertRaises(retry.RetryError):
            retry._persist_site(db, bad_values)
        self.assertEqual(db.execute(
            "SELECT count(*) FROM isolated_trace_site_retry"
        ).fetchone()[0], 1)
        db.close()

    @staticmethod
    def trace_record(module_path: str, site: object) -> dict:
        return {
            "schema": "simp-trace-v2",
            "modulePath": module_path,
            "site": {
                "siteOrdinal": site.siteOrdinal,
                "startChar": site.startChar,
                "endChar": site.endChar,
                "callText": site.callText,
            },
            "occurrence": "fixture-occurrence",
            "invocation": 0,
            "invocations": 1,
            "locations": [],
        }

    def test_stored_retry_trace_rejects_duplicate_or_wrong_identity(self) -> None:
        source = "theorem t : True := by simp\n"
        site = retry.worker.align_sites(source)[1][0]
        module_path = "Mathlib/X.lean"
        good = self.trace_record(module_path, site)

        def make_db() -> sqlite3.Connection:
            db = sqlite3.connect(":memory:")
            db.execute(retry.RETRY_SCHEMA)
            db.commit()
            return db

        db = make_db()
        for command_ordinal in (4, 5):
            retry._persist_site(db, (
                "Mathlib.X", command_ordinal, site.siteOrdinal, "a" * 64,
                site.callText, "recorded", retry.json.dumps([good]), None,
                "2026-09-23T00:00:00+00:00"))
        with self.assertRaisesRegex(retry.RetryError, "duplicate persisted retry site"):
            retry._load_retried_traces(db, "Mathlib.X", "a" * 64, module_path,
                                       source, {site.siteOrdinal: 4},
                                       {site.siteOrdinal: site})
        db.close()

        db = make_db()
        retry._persist_site(db, (
            "Mathlib.X", 5, site.siteOrdinal, "a" * 64, site.callText,
            "recorded", retry.json.dumps([good]), None,
            "2026-09-23T00:00:00+00:00"))
        with self.assertRaisesRegex(retry.RetryError, "owner mismatch"):
            retry._load_retried_traces(db, "Mathlib.X", "a" * 64, module_path,
                                       source, {site.siteOrdinal: 4},
                                       {site.siteOrdinal: site})
        db.close()

        db = make_db()
        retry._persist_site(db, (
            "Mathlib.X", 4, site.siteOrdinal, "a" * 64, site.callText + " only",
            "recorded", retry.json.dumps([good]), None,
            "2026-09-23T00:00:00+00:00"))
        with self.assertRaisesRegex(retry.RetryError, "call text mismatch"):
            retry._load_retried_traces(db, "Mathlib.X", "a" * 64, module_path,
                                       source, {site.siteOrdinal: 4},
                                       {site.siteOrdinal: site})
        db.close()

        db = make_db()
        wrong = self.trace_record(module_path, site)
        wrong["site"]["callText"] += " only"
        retry._persist_site(db, (
            "Mathlib.X", 4, site.siteOrdinal, "a" * 64, site.callText,
            "recorded", retry.json.dumps([wrong]), None,
            "2026-09-23T00:00:00+00:00"))
        with self.assertRaisesRegex(retry.RetryError, "identity rejected"):
            retry._load_retried_traces(db, "Mathlib.X", "a" * 64, module_path,
                                       source, {site.siteOrdinal: 4},
                                       {site.siteOrdinal: site})
        db.close()

    def test_command_result_is_transactional_and_updates_only_target(self) -> None:
        db = sqlite3.connect(":memory:")
        db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,"
                   "status TEXT,replacement_text TEXT,error TEXT,"
                   "PRIMARY KEY(module_name,ordinal))")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',1,'pending',NULL,NULL)")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',2,'pending',NULL,NULL)")
        db.execute(retry.COMMAND_SCHEMA)
        db.commit()
        retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "pending",
                                      "compiled_success", "by exact h", None, None)
        self.assertEqual(db.execute(
            "SELECT status,replacement_text,error FROM simp_replacements "
            "WHERE module_name='Mathlib.X' AND ordinal=1").fetchone(),
            ("success", "by exact h", None))
        self.assertEqual(db.execute(
            "SELECT status,replacement_text,error FROM simp_replacements "
            "WHERE module_name='Mathlib.X' AND ordinal=2").fetchone(),
            ("pending", None, None))
        self.assertEqual(db.execute(
            "SELECT result_status,replacement_sha256 FROM isolated_trace_command_retry"
        ).fetchone(), ("compiled_success", retry.hashlib.sha256(b"by exact h").hexdigest()))
        with self.assertRaises(retry.RetryError):
            retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "pending",
                                          "compiled_success", "by sorry", None, None)
        with self.assertRaisesRegex(retry.RetryError, "nonblank replacement"):
            retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "pending",
                                          "compiled_success", " \n ", None, None)
        self.assertEqual(db.execute("SELECT COUNT(*) FROM isolated_trace_command_retry").fetchone()[0], 1)
        db.close()

    def test_existing_success_replacements_must_be_nonblank(self) -> None:
        db = sqlite3.connect(":memory:")
        db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,"
                   "status TEXT,replacement_text TEXT,error TEXT)")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',1,'success','  ',NULL)")
        with self.assertRaisesRegex(retry.RetryError, "blank replacement"):
            retry._existing_success_replacements(db, "Mathlib.X")
        db.close()

    def test_compile_failure_is_recorded_only_after_compiled_baseline(self) -> None:
        db = sqlite3.connect(":memory:")
        db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,"
                   "status TEXT,replacement_text TEXT,error TEXT,"
                   "PRIMARY KEY(module_name,ordinal))")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',1,'pending',NULL,NULL)")
        db.execute(retry.COMMAND_SCHEMA)
        db.commit()
        retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "pending",
                                      "baseline_failed", None, None, "baseline error")
        self.assertEqual(db.execute("SELECT status,error FROM simp_replacements").fetchone(),
                         ("pending", None))
        retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "pending",
                                      "compile_failed", None, None, "target command error")
        self.assertEqual(db.execute("SELECT status,error FROM simp_replacements").fetchone(),
                         ("compile_failed", "target command error"))
        db.close()

    def test_baseline_failure_rejects_a_concurrent_status_change(self) -> None:
        db = sqlite3.connect(":memory:")
        db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,"
                   "status TEXT,replacement_text TEXT,error TEXT,"
                   "PRIMARY KEY(module_name,ordinal))")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',1,'compile_failed',NULL,NULL)")
        db.execute(retry.COMMAND_SCHEMA)
        db.commit()
        with self.assertRaisesRegex(retry.RetryError, "status changed"):
            retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "record_failed",
                                          "baseline_failed", None, None, "baseline error")
        self.assertEqual(db.execute(
            "SELECT COUNT(*) FROM isolated_trace_command_retry").fetchone()[0], 0)
        db.close()

    def test_trace_failure_replaces_module_fanout_with_command_detail(self) -> None:
        db = sqlite3.connect(":memory:")
        db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,"
                   "status TEXT,replacement_text TEXT,error TEXT,"
                   "PRIMARY KEY(module_name,ordinal))")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',1,'record_failed',NULL,"
                   "'module-wide recorder fanout')")
        db.execute(retry.COMMAND_SCHEMA)
        db.commit()
        retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "record_failed",
                                      "trace_failed", None, "site 3 was not emitted", None)
        self.assertEqual(db.execute("SELECT status,error FROM simp_replacements").fetchone(),
                         ("record_failed", "site 3 was not emitted"))
        self.assertEqual(db.execute(
            "SELECT result_status,render_error FROM isolated_trace_command_retry"
        ).fetchone(), ("trace_failed", "site 3 was not emitted"))
        db.close()

    def test_render_failure_keeps_render_failed_primary_status(self) -> None:
        db = sqlite3.connect(":memory:")
        db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,"
                   "status TEXT,replacement_text TEXT,error TEXT,"
                   "PRIMARY KEY(module_name,ordinal))")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',1,'pending',NULL,NULL)")
        db.execute(retry.COMMAND_SCHEMA)
        db.commit()
        retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "pending",
                                      "render_failed", None, "unsupported render shape", None)
        self.assertEqual(db.execute("SELECT status,error FROM simp_replacements").fetchone(),
                         ("render_failed", "unsupported render shape"))
        self.assertEqual(db.execute(
            "SELECT result_status,render_error FROM isolated_trace_command_retry"
        ).fetchone(), ("render_failed", "unsupported render shape"))
        db.close()

    def test_pending_noop_is_transactional(self) -> None:
        db = sqlite3.connect(":memory:")
        db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,"
                   "status TEXT,replacement_text TEXT,error TEXT,"
                   "PRIMARY KEY(module_name,ordinal))")
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.X',1,'pending',NULL,NULL)")
        db.execute(retry.COMMAND_SCHEMA)
        db.commit()
        retry._persist_command_result(db, "Mathlib.X", 1, "a" * 64, "pending",
                                      "noop", None, None, None)
        self.assertEqual(db.execute("SELECT status,replacement_text,error FROM simp_replacements").fetchone(),
                         ("noop", None, None))
        self.assertEqual(db.execute(
            "SELECT result_status FROM isolated_trace_command_retry"
        ).fetchone(), ("noop",))
        db.close()


if __name__ == "__main__":
    unittest.main()
