#!/usr/bin/env python3
"""Focused synthetic tests for simp replacement job fan-out and merge."""

from __future__ import annotations

import hashlib
import io
import sqlite3
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_replacement_jobs as jobs  # noqa: E402
import merge_simp_replacement_dbs as merger  # noqa: E402


SCHEMA = """
CREATE TABLE modules (name TEXT PRIMARY KEY, path TEXT NOT NULL UNIQUE, source BLOB NOT NULL, source_sha256 TEXT NOT NULL);
CREATE TABLE imports (module_name TEXT NOT NULL REFERENCES modules(name), imported_name TEXT NOT NULL, PRIMARY KEY(module_name, imported_name));
CREATE TABLE commands (module_name TEXT NOT NULL REFERENCES modules(name), ordinal INTEGER NOT NULL CHECK(ordinal >= 0), start_byte INTEGER NOT NULL CHECK(start_byte >= 0), end_byte INTEGER NOT NULL CHECK(end_byte > start_byte), kind TEXT NOT NULL, source_sha256 TEXT NOT NULL, source TEXT, body TEXT, PRIMARY KEY(module_name, ordinal));
CREATE TABLE simp_replacements (module_name TEXT NOT NULL, ordinal INTEGER NOT NULL, status TEXT NOT NULL DEFAULT 'pending', replacement_text TEXT, error TEXT, PRIMARY KEY(module_name, ordinal), FOREIGN KEY(module_name, ordinal) REFERENCES commands(module_name, ordinal));
"""


def make_db(path: Path, candidate_counts: tuple[int, ...] = (1, 1, 1, 1)) -> None:
    con = sqlite3.connect(path)
    con.executescript(SCHEMA)
    for index, count in enumerate(candidate_counts):
        name = module_name(index)
        source_text = "import Mathlib\n\n"
        command_rows = []
        for ordinal in range(count):
            command = f"theorem t{ordinal} : True := by simp"
            start = len(source_text.encode("utf-8"))
            source_text += command + "\n\n"
            stop = start + len(command.encode("utf-8"))
            command_rows.append((ordinal, start, stop, "Lean.Parser.Command.declaration",
                                 hashlib.sha256(command.encode("utf-8")).hexdigest(),
                                 command, "simp"))
        source = source_text.encode("utf-8")
        path_value = name.replace(".", "/") + ".lean"
        con.execute("INSERT INTO modules VALUES (?, ?, ?, ?)", (name, path_value, source, hashlib.sha256(source).hexdigest()))
        con.execute("INSERT INTO imports VALUES (?, ?)", (name, "Mathlib"))
        for row in command_rows:
            ordinal, start, stop, kind, digest, command, body = row
            con.execute("INSERT INTO commands VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                        (name, ordinal, start, stop, kind, digest, command, body))
            con.execute("INSERT INTO simp_replacements(module_name, ordinal) VALUES (?, ?)", (name, ordinal))
    con.commit()
    con.close()


def state(path: Path) -> list[tuple]:
    con = sqlite3.connect(path)
    result = con.execute("SELECT module_name, ordinal, status, replacement_text, error FROM simp_replacements ORDER BY module_name, ordinal").fetchall()
    con.close()
    return result


def dummy_update(job_dir: Path, module: str, ordinal: int, status: str, replacement: str | None = None, error: str | None = None) -> None:
    if replacement == "by exact True.intro":
        replacement = f"theorem t{ordinal} : True := by exact True.intro"
    con = sqlite3.connect(job_dir / jobs.DB_NAME)
    con.execute("UPDATE simp_replacements SET status=?, replacement_text=?, error=? WHERE module_name=? AND ordinal=?", (status, replacement, error, module, ordinal))
    con.commit()
    con.close()


def module_name(index: int) -> str:
    return f"Mathlib.Test.SimpReplacementJobs.M{index:02d}"


class SimpReplacementJobsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.primary = self.root / "primary.sqlite3"
        make_db(self.primary)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def prepare(
        self,
        jobs_count: int = 2,
        statuses: tuple[str, ...] = ("pending",),
    ) -> tuple[Path, list[list[str]]]:
        output = self.root / f"jobs-{jobs_count}"
        assignment = jobs.prepare(self.primary, output, jobs_count, statuses)
        return output, assignment

    def test_partition_has_exact_coverage_and_balances_weight(self) -> None:
        modules = [(f"M{i}", n, size) for i, (n, size) in enumerate(((10, 100), (9, 100), (8, 100), (1, 100), (1, 100), (1, 100)))]
        parts = jobs.partition_modules(modules, 3)
        self.assertEqual(sorted(x for p in parts for x in p), sorted(m[0] for m in modules))
        loads = [sum(count * 1_000_000 + size for name, count, size in modules if name in p) for p in parts]
        self.assertLess(max(loads) - min(loads), 3_000_000)
        self.assertEqual(len({name for part in parts for name in part}), len(modules))

    def test_prepare_copies_full_db_without_mutating_primary_and_emits_sorted_manifests(self) -> None:
        before = state(self.primary)
        output, assignments = self.prepare(2)
        self.assertEqual(before, state(self.primary))
        self.assertEqual(sorted(name for part in assignments for name in part), [f"M{i:02d}" for i in range(4)])
        for i, part in enumerate(assignments):
            directory = output / f"job-{i:03d}"
            self.assertEqual((directory / jobs.MANIFEST_NAME).read_text().splitlines(), sorted(part))
            self.assertEqual(state(directory / jobs.DB_NAME), before)

    def test_job_count_and_existing_output_reject_unsafe_fanout(self) -> None:
        with self.assertRaises(ValueError):
            jobs.partition_modules([("M", 1, 1)], 2)
        output, _ = self.prepare()
        with self.assertRaises(FileExistsError):
            jobs.prepare(self.primary, output, 2)

    def test_merge_resume_partial_job_and_idempotence(self) -> None:
        output, _ = self.prepare(2)
        job0, job1 = output / "job-000", output / "job-001"
        module0 = (job0 / jobs.MANIFEST_NAME).read_text().splitlines()[0]
        module1 = (job1 / jobs.MANIFEST_NAME).read_text().splitlines()[0]
        dummy_update(job0, module0, 0, "success", "by exact True.intro")
        dummy_update(job1, module1, 0, "noop")
        counts = merger.merge(self.primary, [job0, job1])
        self.assertEqual(counts["merged"], 2)
        self.assertEqual(merger.merge(self.primary, [job0, job1])["identical_existing"], 2)
        # Unfinished manifest rows stay pending and are discoverable for resume.
        retry = self.root / "retry.txt"
        retry_modules = jobs.write_retry_manifest(self.primary, retry, ("pending",))
        self.assertEqual(set(retry_modules), {module_name(i) for i in range(4)} - {module0, module1})

    def test_merge_refuses_success_with_an_owned_direct_simp_node(self) -> None:
        output, _ = self.prepare(1)
        job = output / "job-000"
        module = (job / jobs.MANIFEST_NAME).read_text().splitlines()[0]
        dummy_update(job, module, 0, "success", "theorem t0 : True := by simp")
        before = state(self.primary)
        with self.assertRaisesRegex(merger.MergeError, "still owns executable simp"):
            merger.merge(self.primary, [job])
        self.assertEqual(before, state(self.primary))

    def test_interrupted_job_pending_result_does_not_reset_terminal_primary(self) -> None:
        output, _ = self.prepare(2)
        job = output / "job-000"
        module = (job / jobs.MANIFEST_NAME).read_text().splitlines()[0]
        dummy_update(job, module, 0, "success", "by exact True.intro")
        merger.merge(self.primary, [job])
        # An older/interrupted copy can only report pending. It cannot erase the
        # already merged success in primary.
        dummy_update(job, module, 0, "pending")
        result = merger.merge(self.primary, [job])
        self.assertGreaterEqual(result["returned_pending"], 1)
        self.assertEqual(state(self.primary)[0][2], "success")

    def test_conflict_rolls_back_all_jobs(self) -> None:
        output, _ = self.prepare(2)
        job0, job1 = output / "job-000", output / "job-001"
        module0 = (job0 / jobs.MANIFEST_NAME).read_text().splitlines()[0]
        module1 = (job1 / jobs.MANIFEST_NAME).read_text().splitlines()[0]
        dummy_update(job0, module0, 0, "success", "by exact True.intro")
        dummy_update(job1, module1, 0, "record_failed", error="trace mismatch")
        primary = sqlite3.connect(self.primary)
        primary.execute("UPDATE simp_replacements SET status='success', replacement_text='by trivial' WHERE module_name=? AND ordinal=0", (module1,))
        primary.commit()
        primary.close()
        before = state(self.primary)
        with self.assertRaises(merger.MergeError):
            merger.merge(self.primary, [job0, job1])
        self.assertEqual(before, state(self.primary))

    def test_authorized_record_failed_refinement_to_success_is_idempotent(self) -> None:
        con = sqlite3.connect(self.primary)
        con.execute(
            "UPDATE simp_replacements SET status='record_failed', error='old trace failure' "
            "WHERE module_name=? AND ordinal=0", (module_name(0),)
        )
        con.commit()
        con.close()
        output, _ = self.prepare(1, ("pending", "record_failed"))
        job = output / "job-000"
        dummy_update(job, module_name(0), 0, "success", "by exact True.intro")

        with redirect_stdout(io.StringIO()):
            exit_code = merger.main([
                "--database", str(self.primary), "--replace-status", "record_failed", str(job)
            ])
        self.assertEqual(exit_code, 0)
        self.assertEqual(state(self.primary)[0][2:], ("success", "theorem t0 : True := by exact True.intro", None))
        repeated = merger.merge(self.primary, [job], replace_status={"record_failed"})
        self.assertEqual(repeated["identical_existing"], 1)
        self.assertEqual(state(self.primary)[0][2:], ("success", "theorem t0 : True := by exact True.intro", None))

    def test_authorized_record_failed_refinement_to_failure(self) -> None:
        con = sqlite3.connect(self.primary)
        con.execute(
            "UPDATE simp_replacements SET status='record_failed', error='old trace failure' "
            "WHERE module_name=? AND ordinal=0", (module_name(0),)
        )
        con.commit()
        con.close()
        output, _ = self.prepare(1, ("pending", "record_failed"))
        job = output / "job-000"
        dummy_update(job, module_name(0), 0, "compile_failed", error="fresh compile failure")

        merged = merger.merge(self.primary, [job], replace_status={"record_failed"})
        self.assertEqual(merged["merged"], 1)
        self.assertEqual(state(self.primary)[0][2:], ("compile_failed", None, "fresh compile failure"))

    def test_record_failed_terminal_conflict_requires_explicit_authorization(self) -> None:
        con = sqlite3.connect(self.primary)
        con.execute(
            "UPDATE simp_replacements SET status='record_failed', error='old trace failure' "
            "WHERE module_name=? AND ordinal=0", (module_name(0),)
        )
        con.commit()
        con.close()
        output, _ = self.prepare(1, ("pending", "record_failed"))
        job = output / "job-000"
        dummy_update(job, module_name(0), 0, "success", "by exact True.intro")
        before = state(self.primary)

        with self.assertRaises(merger.MergeError):
            merger.merge(self.primary, [job])
        self.assertEqual(before, state(self.primary))

    def test_replace_status_cannot_authorize_success_or_pending(self) -> None:
        output, _ = self.prepare(1)
        job = output / "job-000"
        for status in ("pending", "success"):
            with self.subTest(status=status), self.assertRaises(merger.MergeError):
                merger.merge(self.primary, [job], replace_status={status})

    def test_overlapping_and_malformed_manifests_reject(self) -> None:
        output, _ = self.prepare(2)
        job0, job1 = output / "job-000", output / "job-001"
        name = (job0 / jobs.MANIFEST_NAME).read_text().splitlines()[0]
        (job1 / jobs.MANIFEST_NAME).write_text(f"{name}\n", encoding="utf-8")
        with self.assertRaises(merger.MergeError):
            merger.merge(self.primary, [job0, job1])
        (job0 / jobs.MANIFEST_NAME).write_text(f" {name}\n", encoding="utf-8")
        with self.assertRaises(merger.MergeError):
            merger.merge(self.primary, [job0])

    def test_schema_drift_and_original_source_drift_reject(self) -> None:
        output, _ = self.prepare(2)
        job = output / "job-000"
        con = sqlite3.connect(job / jobs.DB_NAME)
        con.execute("ALTER TABLE simp_replacements ADD COLUMN surprise TEXT")
        con.commit()
        con.close()
        with self.assertRaises(merger.MergeError):
            merger.merge(self.primary, [job])
        # Restore a fresh worker copy, then alter original source content.
        output2 = self.root / "other"
        jobs.prepare(self.primary, output2, 2)
        job2 = output2 / "job-000"
        con = sqlite3.connect(job2 / jobs.DB_NAME)
        con.execute("UPDATE modules SET source=? WHERE name=?", (b"drift", module_name(0)))
        con.commit()
        con.close()
        with self.assertRaises(merger.MergeError):
            merger.merge(self.primary, [job2])

    def test_unassigned_mutation_and_missing_queue_row_reject(self) -> None:
        output, assignments = self.prepare(2)
        job = output / "job-000"
        unassigned = next(m for m in (module_name(i) for i in range(4)) if m not in assignments[0])
        con = sqlite3.connect(job / jobs.DB_NAME)
        con.execute("UPDATE simp_replacements SET status='noop' WHERE module_name=?", (unassigned,))
        con.commit()
        con.close()
        with self.assertRaises(merger.MergeError):
            merger.merge(self.primary, [job])

    def test_result_shape_validation_and_status_reporting(self) -> None:
        output, _ = self.prepare(2)
        job = output / "job-000"
        module = (job / jobs.MANIFEST_NAME).read_text().splitlines()[0]
        dummy_update(job, module, 0, "success", None)
        with self.assertRaises(merger.MergeError):
            merger.merge(self.primary, [job])
        report = jobs.render_status(self.primary)
        self.assertEqual(report["rows"], 4)
        self.assertEqual(report["statuses"]["pending"], 4)


if __name__ == "__main__":
    unittest.main()
