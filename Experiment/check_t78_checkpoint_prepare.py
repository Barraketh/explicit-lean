#!/usr/bin/env python3
"""Synthetic safety and determinism checks for the T78 checkpoint preparer."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sqlite3
import sys
import tempfile
import unittest
from contextlib import closing
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import t78_checkpoint_prepare as t78  # noqa: E402


SCHEMA = """
CREATE TABLE modules (
  name TEXT PRIMARY KEY, path TEXT NOT NULL UNIQUE,
  source BLOB NOT NULL, source_sha256 TEXT NOT NULL
);
CREATE TABLE imports (
  module_name TEXT NOT NULL, imported_name TEXT NOT NULL,
  PRIMARY KEY(module_name, imported_name)
);
CREATE TABLE commands (
  module_name TEXT NOT NULL, ordinal INTEGER NOT NULL CHECK(ordinal >= 0),
  start_byte INTEGER NOT NULL, end_byte INTEGER NOT NULL,
  kind TEXT NOT NULL, source_sha256 TEXT NOT NULL, source TEXT, body TEXT,
  PRIMARY KEY(module_name, ordinal)
);
CREATE TABLE simp_replacements (
  module_name TEXT NOT NULL, ordinal INTEGER NOT NULL,
  status TEXT NOT NULL DEFAULT 'pending', replacement_text TEXT, error TEXT,
  PRIMARY KEY(module_name, ordinal)
);
"""


def source_for(module: str) -> tuple[bytes, int, int, str]:
    declaration = f"theorem {module.rsplit('.', 1)[-1]} : True := by simp"
    source = ("import Mathlib\n\n" + declaration + "\n").encode("utf-8")
    start = source.index(declaration.encode("utf-8"))
    stop = start + len(declaration.encode("utf-8"))
    return source, start, stop, declaration


def make_database(path: Path, rows: dict[str, tuple[str, str | None, str | None]]) -> None:
    con = sqlite3.connect(path)
    con.executescript(SCHEMA)
    for module, value in sorted(rows.items()):
        source, start, stop, declaration = source_for(module)
        source_hash = hashlib.sha256(source).hexdigest()
        con.execute("INSERT INTO modules VALUES(?,?,?,?)", (
            module, module.replace(".", "/") + ".lean", source, source_hash))
        con.execute("INSERT INTO imports VALUES(?,?)", (module, "Mathlib"))
        con.execute("INSERT INTO commands VALUES(?,?,?,?,?,?,?,?)", (
            module, 0, start, stop, "Lean.Parser.Command.declaration",
            hashlib.sha256(declaration.encode("utf-8")).hexdigest(), declaration, "by simp"))
        con.execute("INSERT INTO simp_replacements VALUES(?,?,?,?,?)", (module, 0, *value))
    con.commit()
    con.close()


def make_two_command_database(path: Path, module: str) -> None:
    con = sqlite3.connect(path)
    con.executescript(SCHEMA)
    declarations = [
        "theorem first : True := by simp",
        "theorem second : True := by simp",
    ]
    source_text = "import Mathlib\n\n"
    ranges = []
    for declaration in declarations:
        start = len(source_text.encode("utf-8"))
        source_text += declaration + "\n"
        stop = len(source_text.encode("utf-8")) - 1
        ranges.append((start, stop, declaration))
    source = source_text.encode("utf-8")
    source_hash = hashlib.sha256(source).hexdigest()
    con.execute("INSERT INTO modules VALUES(?,?,?,?)", (
        module, module.replace(".", "/") + ".lean", source, source_hash))
    con.execute("INSERT INTO imports VALUES(?,?)", (module, "Mathlib"))
    for ordinal, (start, stop, declaration) in enumerate(ranges):
        con.execute("INSERT INTO commands VALUES(?,?,?,?,?,?,?,?)", (
            module, ordinal, start, stop, "Lean.Parser.Command.declaration",
            hashlib.sha256(declaration.encode("utf-8")).hexdigest(), declaration, "by simp"))
        con.execute("INSERT INTO simp_replacements VALUES(?,?,?,?,?)", (
            module, ordinal, "pending", None, None))
    con.commit()
    con.close()


def copy_database(source: Path, target: Path) -> None:
    src = sqlite3.connect(f"file:{source}?mode=ro", uri=True)
    dst = sqlite3.connect(target)
    try:
        src.backup(dst)
    finally:
        dst.close()
        src.close()


def update(path: Path, module: str, value: tuple[str, str | None, str | None]) -> None:
    con = sqlite3.connect(path)
    con.execute(
        "UPDATE simp_replacements SET status=?,replacement_text=?,error=? WHERE module_name=? AND ordinal=0",
        (*value, module),
    )
    con.commit()
    con.close()


def rows(path: Path) -> dict[str, tuple[str, str | None, str | None]]:
    con = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    result = {r[0]: (r[1], r[2], r[3]) for r in con.execute(
        "SELECT module_name,status,replacement_text,error FROM simp_replacements ORDER BY module_name")}
    con.close()
    return result


def write_job(
    parent: Path,
    index: int,
    base: Path,
    assigned: list[str],
    changes: dict[str, tuple[str, str | None, str | None]],
    *,
    auxiliary_outside: str | None = None,
) -> Path:
    directory = parent / f"job-{index:03d}"
    directory.mkdir(parents=True)
    copy_database(base, directory / t78.DB_NAME)
    (directory / t78.MANIFEST_NAME).write_text(
        "".join(f"{module}\n" for module in sorted(assigned)), encoding="utf-8")
    for module, value in changes.items():
        update(directory / t78.DB_NAME, module, value)
    if auxiliary_outside is not None:
        con = sqlite3.connect(directory / t78.DB_NAME)
        con.execute("CREATE TABLE isolated_trace_site_retry (module_name TEXT NOT NULL, ordinal INTEGER NOT NULL, status TEXT NOT NULL)")
        con.execute("INSERT INTO isolated_trace_site_retry VALUES(?,?,?)", (auxiliary_outside, 0, "recorded"))
        con.commit()
        con.close()
    return directory


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


class T78CheckpointPrepareTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.modules = [
            "Mathlib.Test.T78.P0", "Mathlib.Test.T78.P1", "Mathlib.Test.T78.P2",
            "Mathlib.Test.T78.P3", "Mathlib.Test.T78.U0", "Mathlib.Test.T78.U1",
            "Mathlib.Test.T78.StaleSuccess",
            "Mathlib.Test.T78.StaleZeta", "Mathlib.Test.T78.Zeta0",
            "Mathlib.Test.T78.Zeta1", "Mathlib.Test.T78.Max0", "Mathlib.Test.T78.Max1",
            "Mathlib.Test.T78.FailureOnly", "Mathlib.Test.T78.NoopOnly",
        ]
        self.t76_values = {module: ("pending", None, None) for module in self.modules}
        self.t76_values["Mathlib.Test.T78.StaleSuccess"] = ("success", "by exact True.intro", None)
        for module in ("Mathlib.Test.T78.StaleZeta", "Mathlib.Test.T78.Zeta0", "Mathlib.Test.T78.Zeta1"):
            self.t76_values[module] = ("render_failed", None, "zeta retry target")
        for module in ("Mathlib.Test.T78.Max0", "Mathlib.Test.T78.Max1"):
            self.t76_values[module] = ("record_failed", None, "record failure")
        self.t76_values["Mathlib.Test.T78.FailureOnly"] = ("compile_failed", None, "compile failure")
        self.t76_values["Mathlib.Test.T78.NoopOnly"] = ("noop", None, None)
        self.t76 = self.root / "t76.sqlite3"
        make_database(self.t76, self.t76_values)

        self.pending_base = self.root / "pending-base.sqlite3"
        pending_base_values = dict(self.t76_values)
        pending_base_values["Mathlib.Test.T78.StaleSuccess"] = ("pending", None, None)
        pending_base_values["Mathlib.Test.T78.StaleZeta"] = ("pending", None, None)
        make_database(self.pending_base, pending_base_values)

        self.named_base = self.t76
        self.max_base = self.root / "max-base.sqlite3"
        max_base_values = dict(self.t76_values)
        max_base_values["Mathlib.Test.T78.Zeta0"] = ("success", "by exact True.intro", None)
        max_base_values["Mathlib.Test.T78.StaleZeta"] = ("success", "by exact True.intro", None)
        make_database(self.max_base, max_base_values)

        pending_modules = [module for module, value in pending_base_values.items() if value[0] == "pending"]
        self.pending_root = self.root / "pending-jobs"
        self.pending_root.mkdir()
        pending_assignments = [pending_modules[i::4] for i in range(4)]
        self.pending_jobs = []
        for index, assigned in enumerate(pending_assignments):
            changes = {}
            if "Mathlib.Test.T78.P0" in assigned:
                changes["Mathlib.Test.T78.P0"] = ("success", "by exact True.intro", None)
            if "Mathlib.Test.T78.StaleSuccess" in assigned:
                changes["Mathlib.Test.T78.StaleSuccess"] = ("success", "by exact True.intro -- stale", None)
            if "Mathlib.Test.T78.StaleZeta" in assigned:
                changes["Mathlib.Test.T78.StaleZeta"] = ("success", "by exact True.intro -- pending", None)
            self.pending_jobs.append(write_job(self.pending_root, index, self.pending_base, assigned, changes))

        self.zeta_root = self.root / "zeta-jobs"
        self.zeta_root.mkdir()
        self.zeta_expected = self.root / "zeta-expected.txt"
        zeta_modules = ["Mathlib.Test.T78.StaleZeta", "Mathlib.Test.T78.Zeta0", "Mathlib.Test.T78.Zeta1"]
        self.zeta_expected.write_text("".join(f"{m}\n" for m in zeta_modules), encoding="utf-8")
        self.zeta_jobs = [
            write_job(self.zeta_root, 0, self.named_base, zeta_modules[:2], {
                "Mathlib.Test.T78.StaleZeta": ("success", "by exact True.intro -- zeta", None),
                "Mathlib.Test.T78.Zeta0": ("success", "by exact True.intro", None),
            }),
            write_job(self.zeta_root, 1, self.named_base, zeta_modules[2:], {
                "Mathlib.Test.T78.Zeta1": ("success", "INVALID direct simp", None),
            }),
        ]

        self.max_root = self.root / "max-jobs"
        self.max_root.mkdir()
        max_modules = ["Mathlib.Test.T78.Max0", "Mathlib.Test.T78.Max1"]
        self.max_jobs = [
            write_job(self.max_root, 0, self.max_base, max_modules[:1], {
                "Mathlib.Test.T78.Max0": ("success", "by exact True.intro", None),
            }),
            write_job(self.max_root, 1, self.max_base, max_modules[1:], {
                "Mathlib.Test.T78.Max1": ("compile_failed", None, "fresh compile error"),
            }),
        ]
        self.receipt_path = self.root / "input-receipt.json"
        self.refresh_receipt()

    def tearDown(self) -> None:
        self.temp.cleanup()

    def _receipt_entry(self, path: Path) -> dict[str, str]:
        return {"path": str(path.resolve()), "sha256": file_hash(path)}

    def refresh_receipt(self) -> None:
        def jobs(directories: list[Path]) -> list[dict]:
            return [{
                "job": directory.name,
                "database": self._receipt_entry(directory / t78.DB_NAME),
                "manifest": self._receipt_entry(directory / t78.MANIFEST_NAME),
            } for directory in directories]

        value = {
            "schema": t78.INPUT_RECEIPT_SCHEMA,
            "campaign": t78.INPUT_RECEIPT_CAMPAIGN,
            "maxretry_statuses": ["record_failed"],
            "inputs": {
                "t76_database": self._receipt_entry(self.t76),
                "pending_base": self._receipt_entry(self.pending_base),
                "zeta_base": self._receipt_entry(self.named_base),
                "maxretry_base": self._receipt_entry(self.max_base),
                "zeta_expected_manifest": self._receipt_entry(self.zeta_expected),
                "pending_jobs": jobs(self.pending_jobs),
                "zeta_jobs": jobs(self.zeta_jobs),
                "maxretry_jobs": jobs(self.max_jobs),
            },
        }
        self.receipt_path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")

    def create(self, output: Path, **overrides) -> dict:
        arguments = dict(
            input_receipt=self.receipt_path,
            expected_input_receipt_sha256=file_hash(self.receipt_path),
            t76_database=self.t76,
            pending_base=self.pending_base,
            pending_jobs=self.pending_jobs,
            zeta_base=self.named_base,
            zeta_jobs=self.zeta_jobs,
            zeta_expected_manifest=self.zeta_expected,
            maxretry_base=self.max_base,
            maxretry_jobs=self.max_jobs,
            maxretry_statuses=("record_failed",),
            output_root=output,
            repo_root=self.root,
        )
        arguments.update(overrides)
        # Unit fixtures have synthetic baseline files; the production code is
        # pinned to the published campaign artifact digests.
        fixture_pins = {
            "t76_database": file_hash(self.t76),
            "pending_base": file_hash(self.pending_base),
            "zeta_base": file_hash(self.named_base),
            "maxretry_base": file_hash(self.max_base),
        }
        with patch.object(t78, "PINNED_BASELINE_SHA256", fixture_pins):
            return t78.create_checkpoint(**arguments)

    def fake_tsa(self, calls: list[tuple[str, tuple[int, ...], tuple[str, ...]]]):
        def validate(**kwargs):
            module = kwargs["module"]
            ordinals = tuple(sorted(kwargs["success_ordinals"]))
            replacements = kwargs["candidate_replacements"]
            calls.append((module, ordinals, tuple(sorted(replacements.values()))))
            invalid = [ordinal for ordinal in ordinals if "INVALID" in replacements[ordinal]]
            if invalid:
                raise t78.TSA.SyntaxExtractionError(
                    f"success command {invalid[0]} still owns executable simp tactic node(s): []")
        return validate

    def test_checkpoint_merges_in_order_preserves_inputs_and_quarantines_ast_failure(self) -> None:
        inputs = [self.t76, self.pending_base, self.max_base]
        inputs.extend(job / t78.DB_NAME for job in self.pending_jobs + self.zeta_jobs + self.max_jobs)
        before = {path: file_hash(path) for path in inputs}
        calls: list[tuple[str, tuple[int, ...], tuple[str, ...]]] = []
        output = self.root / "checkpoint"
        with patch.object(t78.TSA, "assert_success_commands_have_no_simp", self.fake_tsa(calls)):
            report = self.create(output)

        resulting = rows(output / t78.CHECKPOINT_DB_NAME)
        self.assertEqual(resulting["Mathlib.Test.T78.P0"], ("success", "by exact True.intro", None))
        self.assertEqual(resulting["Mathlib.Test.T78.StaleSuccess"], self.t76_values["Mathlib.Test.T78.StaleSuccess"])
        self.assertEqual(resulting["Mathlib.Test.T78.StaleZeta"], (
            "success", "by exact True.intro -- pending", None))
        self.assertEqual(resulting["Mathlib.Test.T78.Zeta0"], ("success", "by exact True.intro", None))
        self.assertEqual(resulting["Mathlib.Test.T78.Zeta1"], self.t76_values["Mathlib.Test.T78.Zeta1"])
        self.assertEqual(resulting["Mathlib.Test.T78.Max0"], ("success", "by exact True.intro", None))
        self.assertEqual(resulting["Mathlib.Test.T78.Max1"], ("compile_failed", None, "fresh compile error"))
        self.assertGreaterEqual(len(calls), 6)
        self.assertTrue(any(item[0] == "Mathlib.Test.T78.Zeta1" for item in calls))
        self.assertEqual(report["summary"]["quarantinedInvalidSuccesses"], 1)
        self.assertEqual(report["inputReceipt"]["expectedSha256"], file_hash(self.receipt_path))
        self.assertEqual(report["inputReceipt"]["actualSha256"], file_hash(self.receipt_path))
        self.assertEqual(report["verifiedInputs"]["pending_base"]["sha256"], file_hash(self.pending_base))
        self.assertEqual(len(report["verifiedInputs"]["pending_jobs"]), 4)
        self.assertEqual(len(report["verifiedInputs"]["zeta_jobs"]), 2)
        self.assertEqual(len(report["verifiedInputs"]["maxretry_jobs"]), 2)
        self.assertTrue(any(
            item["module"] == "Mathlib.Test.T78.Zeta1"
            and item["ordinal"] == 0
            and item["action"] == "quarantined_invalid_success"
            and "still owns executable simp tactic" in item["reason"]
            for item in report["audit"]
        ))
        self.assertTrue(any(
            item["module"] == "Mathlib.Test.T78.StaleSuccess"
            and item["action"] == "preserved_current_success"
            for item in report["audit"]
        ))
        self.assertEqual(before, {path: file_hash(path) for path in inputs})
        self.assertEqual((output / t78.CHECKPOINT_REPORT_NAME).read_text(),
                         json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
        repeated_calls: list[tuple[str, tuple[int, ...], tuple[str, ...]]] = []
        with patch.object(t78.TSA, "assert_success_commands_have_no_simp", self.fake_tsa(repeated_calls)):
            repeated = self.create(self.root / "checkpoint-repeat")
        self.assertEqual(repeated, report)
        self.assertEqual(
            (self.root / "checkpoint-repeat" / t78.CHECKPOINT_REPORT_NAME).read_bytes(),
            (output / t78.CHECKPOINT_REPORT_NAME).read_bytes(),
        )

    def test_checkpoint_requires_exact_expected_manifest_coverage(self) -> None:
        manifest = self.pending_root / "job-000" / t78.MANIFEST_NAME
        modules = manifest.read_text().splitlines()
        self.assertIn("Mathlib.Test.T78.U0", modules)
        modules.remove("Mathlib.Test.T78.U0")
        manifest.write_text("".join(f"{module}\n" for module in modules), encoding="utf-8")
        self.refresh_receipt()
        with patch.object(t78.TSA, "assert_success_commands_have_no_simp", lambda **_kwargs: None):
            with self.assertRaisesRegex(t78.CheckpointError, "manifest union does not exactly match"):
                self.create(self.root / "bad-coverage")

    def test_checkpoint_rejects_unassigned_row_mutation(self) -> None:
        job = self.pending_jobs[0]
        assigned = (job / t78.MANIFEST_NAME).read_text().splitlines()
        unassigned = next(m for m in self.modules if m not in assigned)
        update(job / t78.DB_NAME, unassigned, ("record_failed", None, "bad mutation"))
        self.refresh_receipt()
        with patch.object(t78.TSA, "assert_success_commands_have_no_simp", lambda **_kwargs: None):
            with self.assertRaisesRegex(t78.CheckpointError, "unassigned simp_replacements mutation"):
                self.create(self.root / "bad-unassigned")

    def test_checkpoint_rejects_unassigned_auxiliary_mutation(self) -> None:
        job = self.pending_jobs[0]
        assigned = (job / t78.MANIFEST_NAME).read_text().splitlines()
        unassigned = next(m for m in self.modules if m not in assigned)
        con = sqlite3.connect(job / t78.DB_NAME)
        con.execute("CREATE TABLE isolated_trace_site_retry (module_name TEXT NOT NULL, ordinal INTEGER NOT NULL, status TEXT NOT NULL)")
        con.execute("INSERT INTO isolated_trace_site_retry VALUES(?,?,?)", (unassigned, 0, "recorded"))
        con.commit()
        con.close()
        self.refresh_receipt()
        with patch.object(t78.TSA, "assert_success_commands_have_no_simp", lambda **_kwargs: None):
            with self.assertRaisesRegex(t78.CheckpointError, "unassigned auxiliary row"):
                self.create(self.root / "bad-aux")

    def test_checkpoint_rejects_source_table_and_schema_drift(self) -> None:
        job = self.pending_jobs[0]
        con = sqlite3.connect(job / t78.DB_NAME)
        con.execute("UPDATE commands SET kind='untrusted.command' WHERE module_name=?", (
            (job / t78.MANIFEST_NAME).read_text().splitlines()[0],))
        con.commit()
        con.close()
        self.refresh_receipt()
        with patch.object(t78.TSA, "assert_success_commands_have_no_simp", lambda **_kwargs: None):
            with self.assertRaisesRegex(t78.CheckpointError, "source table differs"):
                self.create(self.root / "bad-source")

        # Restore the worker copy from its baseline, then introduce a core
        # schema change. Both failures must occur before output is written.
        shutil.copyfile(self.pending_base, job / t78.DB_NAME)
        con = sqlite3.connect(job / t78.DB_NAME)
        con.execute("ALTER TABLE simp_replacements ADD COLUMN unreviewed TEXT")
        con.commit()
        con.close()
        self.refresh_receipt()
        with patch.object(t78.TSA, "assert_success_commands_have_no_simp", lambda **_kwargs: None):
            with self.assertRaisesRegex(t78.CheckpointError, "core schema drift"):
                self.create(self.root / "bad-schema")

    def test_input_receipt_rejects_swapped_queue_baseline_before_open_or_output(self) -> None:
        output = self.root / "wrong-baseline"
        with self.assertRaisesRegex(t78.CheckpointError, "input receipt path mismatch for pending_base"):
            self.create(output, pending_base=self.max_base)
        self.assertFalse(output.exists())

    def test_expected_receipt_digest_is_checked_before_any_database_or_tsa(self) -> None:
        output = self.root / "wrong-receipt-digest"
        with patch.object(t78, "open_ro", side_effect=AssertionError("SQLite opened before receipt digest")):
            with self.assertRaisesRegex(t78.CheckpointError, "input receipt SHA-256 mismatch before database access"):
                self.create(output, expected_input_receipt_sha256="0" * 64)
        self.assertFalse(output.exists())

    def test_cli_symlink_is_rejected_and_postreceipt_retarget_cannot_create_output(self) -> None:
        with self.assertRaisesRegex(argparse.ArgumentTypeError, "absolute and lexically canonical"):
            t78._canonical_cli_argument(f"{self.root}/./t76.sqlite3")
        alias = self.root / "pending-base-alias.sqlite3"
        alias.symlink_to(self.pending_base)
        with self.assertRaisesRegex(
            t78.CheckpointError,
            "supplied CLI input path must be canonical and non-symlink for pending_base",
        ):
            self.create(self.root / "symlink-cli", pending_base=alias)
        alias.unlink()

        # Retarget a path immediately after its receipt was authenticated. The
        # run must fail during the snapshot recheck, before opening any SQLite
        # file or creating an output directory.
        displaced = self.root / "pending-base-original.sqlite3"
        original_validator = t78.validate_input_receipt

        def validate_then_retarget(**kwargs):
            receipt = original_validator(**kwargs)
            os.replace(self.pending_base, displaced)
            self.pending_base.symlink_to(self.max_base)
            return receipt

        output = self.root / "retargeted-input"
        try:
            with patch.object(t78, "validate_input_receipt", validate_then_retarget):
                with patch.object(t78, "open_ro", side_effect=AssertionError("SQLite opened after path retarget")):
                    with self.assertRaisesRegex(t78.CheckpointError, "not a regular non-symlink file"):
                        self.create(output)
            self.assertFalse(output.exists())
        finally:
            if self.pending_base.is_symlink():
                self.pending_base.unlink()
            if displaced.exists():
                os.replace(displaced, self.pending_base)

    def test_input_receipt_rejects_tampered_worker_database_and_manifest(self) -> None:
        job = self.pending_jobs[0]
        update(job / t78.DB_NAME, "Mathlib.Test.T78.P0", ("compile_failed", None, "tampered worker"))
        output = self.root / "tampered-worker-db"
        with self.assertRaisesRegex(
            t78.CheckpointError,
            "input receipt SHA-256 mismatch for pending_jobs.job-000.database",
        ):
            self.create(output)
        self.assertFalse(output.exists())

        # Restore the pinned job image; a manifest edit is independently
        # caught before the SQLite database can be opened.
        shutil.copyfile(self.pending_base, job / t78.DB_NAME)
        self.refresh_receipt()
        manifest = job / t78.MANIFEST_NAME
        manifest.write_text(manifest.read_text(encoding="utf-8") + "Mathlib.Test.T78.Unowned\n", encoding="utf-8")
        output = self.root / "tampered-worker-manifest"
        with self.assertRaisesRegex(
            t78.CheckpointError,
            "input receipt SHA-256 mismatch for pending_jobs.job-000.manifest",
        ):
            self.create(output)
        self.assertFalse(output.exists())

    def test_current_success_is_not_replaced_by_a_stale_failure(self) -> None:
        job = next(job for job in self.pending_jobs
                   if "Mathlib.Test.T78.StaleSuccess" in (job / t78.MANIFEST_NAME).read_text().splitlines())
        update(job / t78.DB_NAME, "Mathlib.Test.T78.StaleSuccess",
               ("record_failed", None, "stale worker failure"))
        self.refresh_receipt()
        with patch.object(t78.TSA, "assert_success_commands_have_no_simp", lambda **_kwargs: None):
            report = self.create(self.root / "stale-failure")
        self.assertEqual(rows(self.root / "stale-failure" / t78.CHECKPOINT_DB_NAME)[
            "Mathlib.Test.T78.StaleSuccess"], self.t76_values["Mathlib.Test.T78.StaleSuccess"])
        self.assertTrue(any(
            entry["module"] == "Mathlib.Test.T78.StaleSuccess"
            and entry["action"] == "preserved_current_success"
            for entry in report["audit"]
        ))

    def test_direct_simp_failure_isolated_to_its_ordinal(self) -> None:
        module = "Mathlib.Test.T78.Multi"
        database = self.root / "multi.sqlite3"
        make_two_command_database(database, module)
        current = {(module, 0): ("pending", None, None),
                   (module, 1): ("pending", None, None)}
        incoming = {0: "by exact True.intro", 1: "INVALID direct simp"}
        calls: list[tuple[str, tuple[int, ...], tuple[str, ...]]] = []
        with closing(t78.open_ro(database)) as source:
            with patch.object(t78.TSA, "assert_success_commands_have_no_simp", self.fake_tsa(calls)):
                accepted, quarantined = t78.validate_incoming_successes(
                    module=module,
                    current_rows=current,
                    incoming_successes=incoming,
                    source_db=source,
                    repo_root=self.root,
                )
        self.assertEqual(accepted, {0})
        self.assertEqual(set(quarantined), {1})
        self.assertEqual([call[1] for call in calls], [(0, 1), (0,)])

    def test_partition_uses_only_explicit_statuses_and_is_deterministic(self) -> None:
        selected = ("pending", "record_failed")
        con = sqlite3.connect(self.t76)
        con.execute("CREATE TABLE isolated_trace_site_retry_history (attempt_id INTEGER PRIMARY KEY AUTOINCREMENT, module_name TEXT NOT NULL)")
        con.execute("INSERT INTO isolated_trace_site_retry_history(module_name) VALUES(?)", ("Mathlib.Test.T78.P0",))
        con.commit()
        con.close()
        with closing(t78.open_ro(self.t76)) as source:
            rows_by_status = t78._status_rows_by_module(source, selected)
        first = t78.deterministic_partition(rows_by_status, 4)
        second = t78.deterministic_partition(rows_by_status, 4)
        self.assertEqual(first, second)
        output = self.root / "partitions"
        report = t78.create_partitions(
            database=self.t76,
            output_root=output,
            jobs=4,
            statuses=selected,
        )
        self.assertEqual(report["selectedStatuses"], ["pending", "record_failed"])
        assigned = []
        for job in report["jobs"]:
            manifest = (output / job["job"] / t78.MANIFEST_NAME).read_text().splitlines()
            self.assertEqual(manifest, first[int(job["job"].split("-")[-1])])
            assigned.extend(manifest)
            self.assertEqual(rows(output / job["job"] / t78.DB_NAME), self.t76_values)
        self.assertEqual(len(assigned), len(set(assigned)))
        self.assertEqual(set(assigned), {module for module, _, _ in rows_by_status})
        with self.assertRaisesRegex(t78.CheckpointError, "non-success queue statuses"):
            t78.create_partitions(
                database=self.t76, output_root=self.root / "success-selection", jobs=1,
                statuses=("success",),
            )
        with self.assertRaisesRegex(t78.CheckpointError, "between 1 and 8"):
            t78.deterministic_partition(rows_by_status, 9)


if __name__ == "__main__":
    unittest.main(verbosity=2)
