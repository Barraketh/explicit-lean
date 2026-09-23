#!/usr/bin/env python3
"""Focused tests for per-site missing-trace recovery."""

from __future__ import annotations

import contextlib
import io
import pathlib
import os
import sqlite3
import tempfile
from types import SimpleNamespace
from unittest import mock
import unittest

import retry_missing_traces as retry


class MissingTraceRetryTests(unittest.TestCase):
    @contextlib.contextmanager
    def process_fixture(self, *, old_traces: bool = False,
                        statuses: tuple[str, ...] = ("record_failed", "record_failed")):
        with tempfile.TemporaryDirectory() as directory:
            base = pathlib.Path(directory)
            root = base / "repo"
            module_path = "Mathlib/X.lean"
            source = "theorem fixture : True := by exact True.intro\n"
            source_bytes = source.encode("utf-8")
            pinned = root / ".lake" / "packages" / "mathlib" / module_path
            pinned.parent.mkdir(parents=True)
            pinned.write_bytes(source_bytes)
            scratch = base / "scratch"
            scratch.mkdir()
            sites = [
                SimpleNamespace(siteOrdinal=index, startChar=index, endChar=index + 1,
                                callText=f"simp only [fixture_{index}]")
                for index in (1, 2)
            ]
            pairs = [(site, object()) for site in sites]
            owners = {site.siteOrdinal: site.siteOrdinal for site in sites}
            commands = [{"ordinal": index} for index in (1, 2)]
            traces = ({site.siteOrdinal: [self.trace_record(module_path, site)]
                       for site in sites} if old_traces else {})
            db = sqlite3.connect(":memory:")
            db.execute("CREATE TABLE modules(name TEXT,source_sha256 TEXT)")
            db.execute("INSERT INTO modules VALUES('Mathlib.X',?)", ("a" * 64,))
            db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,"
                       "status TEXT,replacement_text TEXT,error TEXT,"
                       "PRIMARY KEY(module_name,ordinal))")
            for ordinal, status in zip((1, 2), statuses):
                db.execute("INSERT INTO simp_replacements VALUES(?,?,?,NULL,'old failure')",
                           ("Mathlib.X", ordinal, status))
            db.execute(retry.RETRY_SCHEMA)
            db.execute(retry.RETRY_HISTORY_SCHEMA)
            db.execute(retry.COMMAND_SCHEMA)
            db.commit()
            stack = contextlib.ExitStack()
            stack.enter_context(mock.patch.object(retry, "ROOT", root))
            stack.enter_context(mock.patch.object(
                retry.worker, "module_rows",
                return_value=(module_path, source_bytes, source, commands)))
            stack.enter_context(mock.patch.object(
                retry, "_renderer_pairs", return_value=(pairs, owners)))
            stack.enter_context(mock.patch.object(
                retry.worker, "align_sites", return_value=([], sites)))
            stack.enter_context(mock.patch.object(
                retry, "_authenticated_old_traces",
                return_value=(traces, set(traces), None if old_traces else "no bundle")))
            stack.enter_context(mock.patch.object(
                retry, "_load_retried_traces", return_value={}))
            stack.enter_context(mock.patch.object(
                retry.worker, "module_with_replacements",
                side_effect=lambda _source, _commands, replacements:
                _source + "\n" + retry.json.dumps(sorted(replacements.items()))))
            try:
                yield {
                    "base": base, "root": root, "pinned": pinned,
                    "source": source, "source_bytes": source_bytes,
                    "module_path": module_path, "sites": sites,
                    "commands": commands, "traces": traces,
                    "scratch": scratch, "db": db, "stack": stack,
                    "targets": [("Mathlib.X", index, statuses[index - 1], "old failure")
                                for index in (1, 2)],
                }
            finally:
                stack.close()
                db.close()

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
            ('Mathlib.X',9,'render_failed','baseline inconclusive'),
            ('Mathlib.X',10,'render_failed','authenticated render failure'),
            ('Mathlib.X',11,'render_failed','audit status mismatch'),
            ('Mathlib.X',12,'render_failed','unsafe audit trace state'),
            ('Mathlib.X',13,'compile_failed','authenticated compile failure'),
            ('Mathlib.X',14,'render_failed','same simp status without audit');
          INSERT INTO isolated_trace_audit VALUES
            ('Mathlib.X',2,'record_failed','no_trace'),
            ('Mathlib.X',3,'success','complete'),
            ('Mathlib.X',10,'render_failed','render_failed'),
            ('Mathlib.X',11,'compile_failed','render_failed'),
            ('Mathlib.X',12,'render_failed','trace_authentication_failed'),
            ('Mathlib.X',13,'compile_failed','rendered');
          INSERT INTO isolated_trace_command_retry VALUES
            ('Mathlib.X',4,'hash','compile_failed'),
            ('Mathlib.X',6,'old-hash','render_failed'),
            ('Mathlib.X',7,'hash','trace_failed'),
            ('Mathlib.X',8,'hash','baseline_failed'),
            ('Mathlib.X',9,'hash','baseline_failed'),
            ('Mathlib.X',10,'hash','render_failed');
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
                          ("Mathlib.X", 8, "compile_failed", "baseline inconclusive"),
                          ("Mathlib.X", 13, "compile_failed", "authenticated compile failure")])
        self.assertEqual(retry._candidate_rows(db, None, ("render_failed",)),
                         [("Mathlib.X", 9, "render_failed", "baseline inconclusive"),
                          ("Mathlib.X", 10, "render_failed",
                           "authenticated render failure")])
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

    def test_bulk_site_recording_authenticates_and_persists_exact_batch(self) -> None:
        with self.process_fixture() as case:
            records = {site.siteOrdinal: [self.trace_record(case["module_path"], site)]
                       for site in case["sites"]}
            recorder = mock.Mock(return_value=(records, ""))
            identity = mock.Mock(return_value=({"identity": "accepted"}, records))
            compiler = mock.Mock(return_value=(True, "", None))
            with mock.patch.object(retry.worker, "record_sites", recorder), \
                    mock.patch.object(retry.worker.replay, "validate_identity", identity), \
                    mock.patch.object(retry.worker, "compile_candidate", compiler), \
                    mock.patch.object(retry, "_render_command",
                                      side_effect=lambda _src, row, _pairs, _traces:
                                      (f"by exact h{row['ordinal']}", None)):
                result = retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=None)

            self.assertEqual(recorder.call_count, 1)
            self.assertEqual(recorder.call_args.args[3], case["sites"])
            identity.assert_called_once()
            self.assertEqual(result["attempted"], 2)
            self.assertEqual(result["recorded"], 2)
            self.assertEqual(case["db"].execute(
                "SELECT site_ordinal,status FROM isolated_trace_site_retry "
                "ORDER BY site_ordinal").fetchall(), [(1, "recorded"), (2, "recorded")])
            self.assertEqual(case["db"].execute(
                "SELECT status,replacement_text FROM simp_replacements ORDER BY ordinal"
            ).fetchall(), [("success", "by exact h1"), ("success", "by exact h2")])
            self.assertEqual([call.args[3] for call in compiler.call_args_list], [0, 1])
            batch_module = compiler.call_args_list[1].args[1]
            self.assertIn("by exact h1", batch_module)
            self.assertIn("by exact h2", batch_module)

    def test_every_bulk_defect_falls_back_for_all_sites(self) -> None:
        for defect in ("missing", "extra", "identity", "exception", "bool_key", "float_key"):
            with self.subTest(defect=defect), self.process_fixture() as case:
                valid = {site.siteOrdinal: [self.trace_record(case["module_path"], site)]
                         for site in case["sites"]}
                extra_site = SimpleNamespace(
                    siteOrdinal=9, startChar=9, endChar=10, callText="simp [extra]")
                calls: list[list[int]] = []

                def record_sites(_source, _module_path, _pinned, selected, _work_dir):
                    ordinals = [site.siteOrdinal for site in selected]
                    calls.append(ordinals)
                    if len(selected) > 1:
                        if defect == "exception":
                            raise RuntimeError("bulk invocation failed")
                        if defect == "missing":
                            return {1: valid[1]}, ""
                        if defect == "identity":
                            return valid, ""
                        if defect == "bool_key":
                            return {True: valid[1], 2: valid[2]}, ""
                        if defect == "float_key":
                            return {1.0: valid[1], 2: valid[2]}, ""
                        return {**valid, 9: [self.trace_record(case["module_path"], extra_site)]}, ""
                    site = selected[0]
                    return {site.siteOrdinal: valid[site.siteOrdinal]}, ""

                compiler = mock.Mock(return_value=(True, "", None))
                identity_result = mock.Mock(side_effect=(
                    [({"identity": "rejected"}, {}),
                     ({"identity": "accepted"}, {1: valid[1]}),
                     ({"identity": "accepted"}, {2: valid[2]})]
                    if defect == "identity" else
                    [({"identity": "accepted"}, {1: valid[1]}),
                     ({"identity": "accepted"}, {2: valid[2]})]
                ))
                with mock.patch.object(retry.worker, "record_sites", side_effect=record_sites), \
                        mock.patch.object(retry.worker.replay, "validate_identity",
                                          identity_result) as identity, \
                        mock.patch.object(retry.worker, "compile_candidate", compiler), \
                        mock.patch.object(retry, "_render_command",
                                          side_effect=lambda _src, row, _pairs, _traces:
                                          (f"by exact h{row['ordinal']}", None)):
                    result = retry.process_module(
                        case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                        retry_failed=False, site_limit=None)

                self.assertEqual(calls, [[1, 2], [1], [2]])
                self.assertEqual(identity.call_count, 3 if defect == "identity" else 2)
                self.assertEqual(result["attempted"], 2)
                self.assertEqual(result["recorded"], 2)
                self.assertEqual(result["failed"], 0)
                self.assertEqual(case["db"].execute(
                    "SELECT site_ordinal,status FROM isolated_trace_site_retry "
                    "ORDER BY site_ordinal").fetchall(), [(1, "recorded"), (2, "recorded")])

    def test_explicit_site_limit_keeps_per_site_recording(self) -> None:
        with self.process_fixture() as case:
            records = {site.siteOrdinal: [self.trace_record(case["module_path"], site)]
                       for site in case["sites"]}
            calls: list[list[int]] = []

            def record_sites(_source, _module_path, _pinned, selected, _work_dir):
                calls.append([site.siteOrdinal for site in selected])
                site = selected[0]
                return {site.siteOrdinal: records[site.siteOrdinal]}, ""

            with mock.patch.object(retry.worker, "record_sites", side_effect=record_sites), \
                    mock.patch.object(retry.worker, "compile_candidate",
                                      return_value=(True, "", None)), \
                    mock.patch.object(retry, "_render_command",
                                      side_effect=lambda _src, row, _pairs, _traces:
                                      (f"by exact h{row['ordinal']}", None)):
                result = retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=2)

            self.assertEqual(calls, [[1], [2]])
            self.assertEqual(result["attempted"], 2)

    def test_batch_compile_success_credits_every_rendered_candidate(self) -> None:
        with self.process_fixture(old_traces=True) as case:
            recorder = mock.Mock(side_effect=AssertionError("all sites already traced"))
            compiler = mock.Mock(return_value=(True, "", None))
            with mock.patch.object(retry.worker, "record_sites", recorder), \
                    mock.patch.object(retry.worker, "compile_candidate", compiler), \
                    mock.patch.object(retry, "_render_command",
                                      side_effect=lambda _src, row, _pairs, _traces:
                                      (f"by exact h{row['ordinal']}", None)):
                result = retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=None)

            recorder.assert_not_called()
            self.assertEqual(result["attempted"], 0)
            self.assertEqual([call.args[3] for call in compiler.call_args_list], [0, 1])
            batch_module = compiler.call_args_list[1].args[1]
            self.assertIn("by exact h1", batch_module)
            self.assertIn("by exact h2", batch_module)
            self.assertEqual(case["db"].execute(
                "SELECT status,replacement_text FROM simp_replacements ORDER BY ordinal"
            ).fetchall(), [("success", "by exact h1"), ("success", "by exact h2")])
            self.assertEqual(result["commandResults"], {"compiled_success": 2})

    def test_refresh_ignores_stale_bundle_and_uses_fresh_records(self) -> None:
        with self.process_fixture(old_traces=True) as case:
            fresh = {site.siteOrdinal: [self.trace_record(case["module_path"], site)]
                     for site in case["sites"]}
            for records in fresh.values():
                records[0]["occurrence"] = "fresh-recorder-result"
            recorder = mock.Mock(return_value=(fresh, ""))
            identity = mock.Mock(return_value=({"identity": "accepted"}, fresh))
            rendered_traces: list[dict[int, list[dict]]] = []

            def render(_source, _row, _pairs, traces):
                rendered_traces.append(traces)
                return "by exact h", None

            with mock.patch.object(retry.worker, "record_sites", recorder), \
                    mock.patch.object(retry.worker.replay, "validate_identity", identity), \
                    mock.patch.object(retry.worker, "compile_candidate",
                                      return_value=(True, "", None)), \
                    mock.patch.object(retry, "_render_command", side_effect=render):
                result = retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=None, refresh_recorded=True)

            self.assertEqual(recorder.call_count, 1)
            self.assertEqual(result["recorded"], 2)
            self.assertTrue(rendered_traces)
            self.assertTrue(all(
                trace["occurrence"] == "fresh-recorder-result"
                for traces in rendered_traces for records in traces.values()
                for trace in records
            ))
            self.assertEqual(identity.call_count, 1)  # exact bulk batch

    def test_refresh_failure_archives_old_trace_and_keeps_command_status(self) -> None:
        with self.process_fixture(old_traces=False) as case:
            site = case["sites"][0]
            old_record = self.trace_record(case["module_path"], site)
            old_json = retry.json.dumps([old_record], sort_keys=True)
            retry._persist_site(case["db"], (
                "Mathlib.X", 1, site.siteOrdinal, "a" * 64, site.callText,
                "recorded", old_json, None, "old-time"))
            calls: list[list[int]] = []

            def fail_record(_source, _module, _pinned, selected, _work_dir):
                calls.append([s.siteOrdinal for s in selected])
                if len(selected) > 1:
                    raise RuntimeError("fresh bulk trace failed")
                raise RuntimeError("fresh site trace failed")

            with mock.patch.object(retry.worker, "record_sites", side_effect=fail_record), \
                    mock.patch.object(retry.worker, "compile_candidate",
                                      return_value=(True, "", None)):
                result = retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=True, site_limit=1, refresh_recorded=True)

            self.assertEqual(calls, [[1]])
            self.assertEqual(result["failed"], 1)
            self.assertEqual(case["db"].execute(
                "SELECT status,trace_json FROM isolated_trace_site_retry "
                "WHERE site_ordinal=1").fetchone(), ("record_failed", None))
            self.assertEqual(case["db"].execute(
                "SELECT status,trace_json,error FROM isolated_trace_site_retry_history "
                "WHERE site_ordinal=1").fetchone(), ("recorded", old_json, None))
            self.assertEqual(case["db"].execute(
                "SELECT status FROM simp_replacements WHERE ordinal=1").fetchone(),
                ("record_failed",))

    def test_single_site_wrong_extra_missing_and_identity_records_fail_closed(self) -> None:
        for defect in ("wrong", "extra", "missing", "identity", "bool_key", "float_key"):
            with self.subTest(defect=defect), self.process_fixture() as case:
                site = case["sites"][0]
                valid = self.trace_record(case["module_path"], site)
                other_site = SimpleNamespace(siteOrdinal=9, startChar=9, endChar=10,
                                             callText="simp [other]")
                extra = self.trace_record(case["module_path"], other_site)
                if defect == "wrong":
                    returned = {9: [extra]}
                elif defect == "extra":
                    returned = {site.siteOrdinal: [valid], 9: [extra]}
                elif defect == "missing":
                    returned = {}
                elif defect == "bool_key":
                    returned = {True: [valid]}
                elif defect == "float_key":
                    returned = {1.0: [valid]}
                else:
                    invalid = dict(valid)
                    invalid["site"] = dict(valid["site"], siteOrdinal=9)
                    returned = {site.siteOrdinal: [invalid]}

                with mock.patch.object(retry.worker, "record_sites",
                                      return_value=(returned, "")), \
                        mock.patch.object(retry.worker.replay, "validate_identity",
                                          return_value=({"identity": "rejected"}, {})), \
                        mock.patch.object(retry.worker, "compile_candidate",
                                          return_value=(True, "", None)):
                    result = retry.process_module(
                        case["db"], "Mathlib.X", [case["targets"][0]], {},
                        case["scratch"], retry_failed=False, site_limit=1,
                        refresh_recorded=True)

                self.assertEqual(result["failed"], 1)
                self.assertEqual(case["db"].execute(
                    "SELECT status,trace_json FROM isolated_trace_site_retry "
                    "WHERE site_ordinal=1").fetchone(), ("record_failed", None))

    def test_limited_failed_refresh_shadows_all_old_bundle_sites_on_default_retry(self) -> None:
        with self.process_fixture(old_traces=True) as case:
            first_recorder = mock.Mock(side_effect=RuntimeError("refresh recorder failed"))
            with mock.patch.object(retry.worker, "record_sites", first_recorder), \
                    mock.patch.object(retry.worker, "compile_candidate",
                                      return_value=(True, "", None)):
                first = retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=1, refresh_recorded=True)

            self.assertEqual(first["failed"], 1)
            self.assertEqual(first["deferred"], 1)
            self.assertEqual(case["db"].execute(
                "SELECT site_ordinal,status,error FROM isolated_trace_site_retry "
                "ORDER BY site_ordinal").fetchall(), [
                    (1, "record_failed", "RuntimeError: refresh recorder failed"),
                    (2, "record_failed", "recorded trace refresh deferred by site limit"),
                ])

            stale_recorder = mock.Mock(side_effect=AssertionError(
                "default retry must not retry or reuse shadowed traces"))
            render = mock.Mock(side_effect=AssertionError(
                "default retry must not render from stale bundle traces"))
            with mock.patch.object(retry.worker, "record_sites", stale_recorder), \
                    mock.patch.object(retry, "_render_command", render), \
                    mock.patch.object(retry.worker, "compile_candidate",
                                      return_value=(True, "", None)):
                second = retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=None, refresh_recorded=False)

            stale_recorder.assert_not_called()
            render.assert_not_called()
            self.assertEqual(second["recorded"], 0)
            self.assertEqual(case["db"].execute(
                "SELECT status,replacement_text FROM simp_replacements ORDER BY ordinal"
            ).fetchall(), [("record_failed", None), ("record_failed", None)])
            self.assertEqual(case["db"].execute(
                "SELECT result_status FROM isolated_trace_command_retry ORDER BY ordinal"
            ).fetchall(), [("trace_failed",), ("trace_failed",)])

    def test_refresh_shadow_set_is_atomic(self) -> None:
        with self.process_fixture(old_traces=False) as case:
            for ordinal, site in enumerate(case["sites"], 1):
                record = self.trace_record(case["module_path"], site)
                retry._persist_site(case["db"], (
                    "Mathlib.X", ordinal, site.siteOrdinal, "a" * 64,
                    site.callText, "recorded",
                    retry.json.dumps([record], sort_keys=True), None, "old-time"))
            case["db"].execute(
                "CREATE TRIGGER abort_second_refresh BEFORE UPDATE "
                "ON isolated_trace_site_retry "
                "WHEN NEW.site_ordinal=2 AND NEW.status='record_failed' "
                "BEGIN SELECT RAISE(ABORT, 'injected interruption'); END"
            )
            case["db"].commit()

            recorder = mock.Mock(side_effect=AssertionError(
                "recorder must start only after the complete shadow set commits"))
            with mock.patch.object(retry.worker, "record_sites", recorder), \
                    self.assertRaises(retry.sqlite3.IntegrityError):
                retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=None, refresh_recorded=True)

            recorder.assert_not_called()
            self.assertEqual(case["db"].execute(
                "SELECT site_ordinal,status,error FROM isolated_trace_site_retry "
                "ORDER BY site_ordinal").fetchall(), [
                    (1, "recorded", None),
                    (2, "recorded", None),
                ])
            self.assertEqual(case["db"].execute(
                "SELECT count(*) FROM isolated_trace_site_retry_history"
            ).fetchone(), (0,))

    def test_batch_compile_failure_credits_only_isolated_successes(self) -> None:
        with self.process_fixture(old_traces=True) as case:
            def compile_candidate(_module_path, candidate, _scratch, serial):
                if serial == 0:
                    return True, "", None
                if serial == 1:
                    return False, "combined candidates conflict", None
                return "by exact h2" not in candidate, "individual diagnostic", None

            compiler = mock.Mock(side_effect=compile_candidate)
            with mock.patch.object(retry.worker, "compile_candidate", compiler), \
                    mock.patch.object(retry, "_render_command",
                                      side_effect=lambda _src, row, _pairs, _traces:
                                      (f"by exact h{row['ordinal']}", None)):
                result = retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=None)

            self.assertEqual([call.args[3] for call in compiler.call_args_list], [0, 1, 2, 3])
            self.assertEqual(case["db"].execute(
                "SELECT status,replacement_text FROM simp_replacements ORDER BY ordinal"
            ).fetchall(), [("success", "by exact h1"), ("compile_failed", None)])
            self.assertEqual(result["commandResults"],
                             {"compiled_success": 1, "compile_failed": 1})

    def test_blank_or_unsafe_render_is_rejected_before_batch_compile(self) -> None:
        with self.process_fixture(old_traces=True) as case:
            compiler = mock.Mock(return_value=(True, "", None))
            def rendered(_source, row, _pairs, _traces):
                return ("   " if row["ordinal"] == 1 else "by sorry"), None

            with mock.patch.object(retry.worker, "render_command", side_effect=rendered), \
                    mock.patch.object(retry.worker, "compile_candidate", compiler):
                retry.process_module(
                    case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                    retry_failed=False, site_limit=None)

            self.assertEqual(compiler.call_count, 1)  # unchanged baseline only
            self.assertEqual(case["db"].execute(
                "SELECT status,replacement_text FROM simp_replacements ORDER BY ordinal"
            ).fetchall(), [("render_failed", None), ("render_failed", None)])
            self.assertEqual(case["db"].execute(
                "SELECT result_status FROM isolated_trace_command_retry ORDER BY ordinal"
            ).fetchall(), [("render_failed",), ("render_failed",)])

    def test_process_preserves_pinned_source_and_status_transaction_guards(self) -> None:
        with self.process_fixture(old_traces=True) as case:
            case["pinned"].write_text("different source\n", encoding="utf-8")
            with mock.patch.object(retry.worker, "compile_candidate") as compiler:
                with self.assertRaisesRegex(retry.RetryError, "pinned source mismatch"):
                    retry.process_module(
                        case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                        retry_failed=False, site_limit=None)
                compiler.assert_not_called()

        with self.process_fixture(old_traces=True) as case:
            def concurrent_status_change(_module_path, _candidate, _scratch, serial):
                if serial == 1:
                    case["db"].execute(
                        "UPDATE simp_replacements SET status='compile_failed' "
                        "WHERE module_name='Mathlib.X' AND ordinal=1")
                    case["db"].commit()
                return True, "", None

            with mock.patch.object(retry.worker, "compile_candidate",
                                   side_effect=concurrent_status_change), \
                    mock.patch.object(retry, "_render_command",
                                      side_effect=lambda _src, row, _pairs, _traces:
                                      (f"by exact h{row['ordinal']}", None)):
                with self.assertRaisesRegex(retry.RetryError, "status changed before commit"):
                    retry.process_module(
                        case["db"], "Mathlib.X", case["targets"], {}, case["scratch"],
                        retry_failed=False, site_limit=None)
            self.assertEqual(case["db"].execute(
                "SELECT status,replacement_text FROM simp_replacements "
                "WHERE ordinal=1").fetchone(), ("compile_failed", None))
            self.assertEqual(case["db"].execute(
                "SELECT COUNT(*) FROM isolated_trace_command_retry").fetchone()[0], 0)

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
