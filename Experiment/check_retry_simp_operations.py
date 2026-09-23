#!/usr/bin/env python3
"""Focused selection, residual, and module replay checks for T79/T80."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sqlite3
import tempfile

import retry_simp_operations as retry
import render_simp_operations as operation_renderer


ROOT = pathlib.Path(__file__).resolve().parents[1]


def make_database(db: sqlite3.Connection, module: str, module_path: str,
                  source: str) -> None:
    raw = source.encode("utf-8")
    db.executescript("""
      CREATE TABLE modules(name TEXT PRIMARY KEY,path TEXT NOT NULL,source BLOB NOT NULL,
                           source_sha256 TEXT NOT NULL);
      CREATE TABLE commands(module_name TEXT NOT NULL,ordinal INTEGER NOT NULL,
          start_byte INTEGER NOT NULL,end_byte INTEGER NOT NULL,kind TEXT NOT NULL,
          source_sha256 TEXT NOT NULL,source TEXT,body TEXT,
          PRIMARY KEY(module_name,ordinal));
      CREATE TABLE simp_replacements(module_name TEXT NOT NULL,ordinal INTEGER NOT NULL,
          status TEXT NOT NULL,replacement_text TEXT,error TEXT,
          PRIMARY KEY(module_name,ordinal));
    """)
    db.execute("INSERT INTO modules VALUES(?,?,?,?)",
               (module, module_path, raw, hashlib.sha256(raw).hexdigest()))
    theorem_ranges: list[tuple[int, int]] = []
    cursor = 0
    while True:
        start = source.find("theorem ", cursor)
        if start < 0:
            break
        end = source.find("\ntheorem ", start + 1)
        if end < 0:
            end = len(source)
        segment_end = end
        while segment_end > start and source[segment_end - 1].isspace():
            segment_end -= 1
        theorem_ranges.append((start, segment_end))
        cursor = end
    for ordinal, (start, end) in enumerate(theorem_ranges):
        command_raw = raw[start:end]
        command_text = command_raw.decode("utf-8")
        status = ("compile_failed" if ordinal == 0 else
                  "success" if ordinal == 1 else "pending")
        replacement = command_text if status == "success" else None
        error = "old isolated compile failure" if status == "compile_failed" else None
        db.execute(
            "INSERT INTO commands VALUES(?,?,?,?,?,?,?,NULL)",
            (module, ordinal, len(raw[:start]), len(raw[:end]), "theorem",
             hashlib.sha256(command_raw).hexdigest(), command_text),
        )
        db.execute("INSERT INTO simp_replacements VALUES(?,?,?,?,?)",
                   (module, ordinal, status, replacement, error))
    db.commit()


def check_selection() -> None:
    db = sqlite3.connect(":memory:")
    db.execute("CREATE TABLE simp_replacements(module_name TEXT,ordinal INTEGER,status TEXT,error TEXT)")
    for ordinal, status in enumerate(("record_failed", "render_failed", "compile_failed",
                                      "pending", "success", "noop", "resource_failed")):
        db.execute("INSERT INTO simp_replacements VALUES('Mathlib.Test',?,?,?)",
                   (ordinal, status, f"diagnostic {status}"))
    got = retry.select_failed_rows(db)
    assert [(row[1], row[2]) for row in got] == [
        (0, "record_failed"), (1, "render_failed"), (2, "compile_failed")
    ], got
    assert retry.select_failed_rows(db, "Mathlib.Other") == []
    db.close()


def check_closed_boundaries() -> None:
    assert retry._has_top_level_location("simp only [Nat.add_zero] at h")
    assert not retry._has_top_level_location("simp only [Nat.add_zero]")
    assert not retry._has_top_level_location("simp only [show x at h from h]")
    trace = {"events": [], "terminal": "open"}
    labelled = f"{retry.OPERATION_MARKER}17 {json.dumps(trace)}"
    assert retry._parse_observations("log prefix " + labelled, {17}) == {}
    assert retry._parse_observations("  " + labelled + "  ", {17}) == {17: [trace]}
    simproc_trace = {
        "events": [{"position": [], "action": {"simproc": {"declarations": ["fixture"]}}}],
        "terminal": "open",
    }
    try:
        operation_renderer.render_trace(simproc_trace)
    except operation_renderer.UnsupportedOperation as error:
        assert "simproc" in str(error)
    else:
        raise AssertionError("simproc operation must stay an explicit residual")


def check_canonical_module_path_refusal() -> None:
    source = """import Mathlib.Data.Nat.Basic

theorem retryDemo (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]
"""
    module = "Mathlib.T79OperationalRetry"
    module_path = "Mathlib/T79OperationalRetry.lean"
    with tempfile.TemporaryDirectory(prefix="retry-canonical-path-") as temp:
        temp_root = pathlib.Path(temp)
        db = sqlite3.connect(":memory:")
        make_database(db, module, module_path, source)
        db.execute("UPDATE modules SET path=? WHERE name=?",
                   ("Mathlib/Other.lean", module))
        db.commit()
        artifacts = temp_root / "artifacts"
        artifacts.mkdir()
        called = False
        old_module_rows = retry.worker.module_rows

        def forbidden_module_read(*args, **kwargs):
            nonlocal called
            called = True
            raise AssertionError("module source read before canonical path validation")

        retry.worker.module_rows = forbidden_module_read
        try:
            report = retry.process_module(
                db, module, artifacts, pathlib.Path("unused"),
                source_root=temp_root / "missing-source",
            )
        finally:
            retry.worker.module_rows = old_module_rows
        assert called is False
        assert report["counts"] == {"record_failed": 1}, report
        row = db.execute(
            "SELECT status,error FROM simp_replacements WHERE module_name=? AND ordinal=0",
            (module,),
        ).fetchone()
        assert row[0] == "record_failed" and "canonical_module_path_mismatch" in row[1], row
        assert list(artifacts.iterdir()) == []
        db.close()


def check_reserved_marker_refusal() -> None:
    source = """import Mathlib.Data.Nat.Basic
-- SIMP_OPERATIONS_SITE is reserved for recorder output

theorem retryDemo (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]
"""
    module = "Mathlib.T79OperationalRetry"
    module_path = "Mathlib/T79OperationalRetry.lean"
    with tempfile.TemporaryDirectory(prefix="retry-marker-collision-") as temp:
        temp_root = pathlib.Path(temp)
        source_root = temp_root / "source"
        source_path = source_root / module_path
        source_path.parent.mkdir(parents=True)
        source_path.write_text(source, encoding="utf-8")
        db = sqlite3.connect(":memory:")
        make_database(db, module, module_path, source)
        artifacts = temp_root / "artifacts"
        artifacts.mkdir()

        def unexpected_call(*args, **kwargs):
            raise AssertionError("marker collision must be rejected before instrumentation/compile")

        report = retry.process_module(
            db, module, artifacts, pathlib.Path("unused"), source_root=source_root,
            recorder=unexpected_call, compiler=unexpected_call,
        )
        assert report["counts"] == {"record_failed": 1}, report
        row = db.execute(
            "SELECT status,error FROM simp_replacements WHERE module_name=? AND ordinal=0",
            (module,),
        ).fetchone()
        assert row[0] == "record_failed" and "reserved_operation_marker_collision" in row[1], row
        assert list(artifacts.iterdir()) == []
        db.close()


def check_end_to_end() -> None:
    source = """import Mathlib.Data.Nat.Basic

theorem retryDemo (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]

theorem alreadyHandled : True := by
  trivial

theorem untouched (n : Nat) : n = n := by
  rfl
"""
    module = "Mathlib.T79OperationalRetry"
    module_path = "Mathlib/T79OperationalRetry.lean"
    with tempfile.TemporaryDirectory(prefix="retry-simp-operations-") as temp:
        temp_root = pathlib.Path(temp)
        source_root = temp_root / "source"
        source_path = source_root / module_path
        source_path.parent.mkdir(parents=True)
        source_path.write_text(source, encoding="utf-8")
        database = temp_root / "mathlib-db.sqlite3"
        db = sqlite3.connect(database)
        make_database(db, module, module_path, source)
        artifacts = temp_root / "artifacts"
        artifacts.mkdir()
        dylib = retry.ensure_prerequisites()
        report = retry.process_module(
            db, module, artifacts, dylib, source_root=source_root,
        )
        assert report["status"] == "committed", report
        assert report["scratchCleaned"] is True, report
        assert list(artifacts.iterdir()) == [], list(artifacts.iterdir())
        assert report["counts"] == {"success": 1}, report
        rows = db.execute(
            "SELECT ordinal,status,replacement_text,error FROM simp_replacements "
            "ORDER BY ordinal"
        ).fetchall()
        assert rows[0][1] == "success" and rows[0][3] is None, rows[0]
        assert "explicit_rw_v2" in rows[0][2], rows[0][2]
        assert "-- Original simp:" in rows[0][2], rows[0][2]
        assert "simp only [Nat.add_zero]" in rows[0][2], rows[0][2]
        assert rows[1][1:] == ("success", "theorem alreadyHandled : True := by\n  trivial", None), rows[1]
        assert rows[2][1:] == ("pending", None, None), rows[2]
        db.close()


def main() -> None:
    check_selection()
    check_closed_boundaries()
    check_canonical_module_path_refusal()
    check_reserved_marker_refusal()
    check_end_to_end()
    print("operational DB retry: selection, residuals, module replay, and selected-row updates passed")


if __name__ == "__main__":
    main()
