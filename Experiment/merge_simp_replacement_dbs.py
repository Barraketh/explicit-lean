#!/usr/bin/env python3
"""Validate and transactionally merge per-job simp replacement databases."""

from __future__ import annotations

import argparse
import hashlib
import json
import sqlite3
import sys
from pathlib import Path
from typing import Any


DB_NAME = "mathlib-db.sqlite3"
MANIFEST_NAME = "modules.txt"
VALID_STATUSES = {
    "pending", "noop", "record_failed", "render_failed", "compile_failed",
    "success", "resource_failed", "worker_failed",
}
BASE_TABLES = ("modules", "imports", "commands")
REQUIRED_TABLES = (*BASE_TABLES, "simp_replacements")


class MergeError(ValueError):
    pass


def open_rw(path: Path) -> sqlite3.Connection:
    con = sqlite3.connect(path)
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA foreign_keys=ON")
    return con


def open_ro(path: Path) -> sqlite3.Connection:
    con = sqlite3.connect(f"file:{path.resolve().as_posix()}?mode=ro", uri=True)
    con.row_factory = sqlite3.Row
    return con


def table_schema(con: sqlite3.Connection) -> dict[str, tuple[str | None, tuple[tuple[Any, ...], ...]]]:
    names = {r[0] for r in con.execute("SELECT name FROM sqlite_master WHERE type='table' AND name NOT LIKE 'sqlite_%'")}
    missing = set(REQUIRED_TABLES) - names
    if missing:
        raise MergeError(f"database missing required tables: {sorted(missing)}")
    result = {}
    for table in REQUIRED_TABLES:
        rows = con.execute(f"PRAGMA table_info({table})").fetchall()
        create_sql = con.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name=?", (table,)).fetchone()[0]
        result[table] = (create_sql, tuple(tuple(row) for row in rows))
    return result


def check_schemas(primary: sqlite3.Connection, worker: sqlite3.Connection, label: str) -> None:
    if table_schema(primary) != table_schema(worker):
        raise MergeError(f"schema drift in {label}")
    for con in (primary, worker):
        result = con.execute("PRAGMA integrity_check").fetchone()[0]
        if result != "ok":
            raise MergeError(f"integrity_check failed for {label}: {result}")


def row_digest(con: sqlite3.Connection, table: str) -> str:
    info = con.execute(f"PRAGMA table_info({table})").fetchall()
    columns = [r[1] for r in info]
    pk_cols = [r[1] for r in sorted((r for r in info if r[5]), key=lambda r: r[5])]
    order = pk_cols or columns
    sql = f"SELECT {', '.join(columns)} FROM {table} ORDER BY {', '.join(order)}"
    digest = hashlib.sha256()
    digest.update(json.dumps(columns, separators=(",", ":")).encode())
    for row in con.execute(sql):
        encoded = []
        for value in row:
            if isinstance(value, bytes):
                encoded.append({"blob": value.hex()})
            else:
                encoded.append(value)
        digest.update(json.dumps(encoded, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


def validate_originals(primary: sqlite3.Connection, worker: sqlite3.Connection, label: str) -> None:
    for table in BASE_TABLES:
        if row_digest(primary, table) != row_digest(worker, table):
            raise MergeError(f"original {table} content differs in {label}")


def read_manifest(path: Path) -> list[str]:
    try:
        content = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise MergeError(f"cannot read UTF-8 manifest {path}: {exc}") from exc
    names: list[str] = []
    for line_number, raw in enumerate(content.splitlines(), 1):
        if not raw.strip():
            continue
        name = raw.strip()
        if raw != name:
            raise MergeError(f"manifest {path}:{line_number}: module line has surrounding whitespace")
        if any(ch.isspace() for ch in name):
            raise MergeError(f"manifest {path}:{line_number}: module names cannot contain whitespace")
        names.append(name)
    if len(names) != len(set(names)):
        raise MergeError(f"manifest contains duplicate module names: {path}")
    return names


def worker_rows(con: sqlite3.Connection, module: str) -> dict[tuple[str, int], tuple[str, str | None, str | None]]:
    rows = con.execute(
        "SELECT module_name, ordinal, status, replacement_text, error FROM simp_replacements WHERE module_name=? ORDER BY ordinal",
        (module,),
    ).fetchall()
    return {(row[0], int(row[1])): (row[2], row[3], row[4]) for row in rows}


def validate_result(status: str, replacement: str | None, error: str | None, key: tuple[str, int], label: str) -> None:
    if status not in VALID_STATUSES:
        raise MergeError(f"{label}: invalid status {status!r} for {key}")
    if status == "success":
        if replacement is None or not replacement.strip() or error is not None:
            raise MergeError(f"{label}: success row must have nonempty replacement_text and NULL error: {key}")
    elif status == "noop":
        if replacement is not None or error is not None:
            raise MergeError(f"{label}: noop row must have NULL replacement_text and error: {key}")
    elif replacement is not None:
        raise MergeError(f"{label}: non-success row must have NULL replacement_text: {key}")
    if status == "pending" and error is not None:
        raise MergeError(f"{label}: pending row must have NULL error: {key}")


def prepare_job(primary: sqlite3.Connection, job_dir: Path, seen_modules: set[str]) -> list[tuple[tuple[str, int], tuple[str, str | None, str | None], str]]:
    manifest = job_dir / MANIFEST_NAME
    db_path = job_dir / DB_NAME
    if not manifest.is_file() or not db_path.is_file():
        raise MergeError(f"job directory must contain {MANIFEST_NAME} and {DB_NAME}: {job_dir}")
    modules = read_manifest(manifest)
    duplicates = seen_modules.intersection(modules)
    if duplicates:
        raise MergeError(f"job manifests overlap: {sorted(duplicates)[:5]}")
    seen_modules.update(modules)
    worker = open_ro(db_path)
    try:
        check_schemas(primary, worker, str(job_dir))
        validate_originals(primary, worker, str(job_dir))
        expected_modules = {row[0] for row in primary.execute("SELECT DISTINCT module_name FROM simp_replacements")}
        if not set(modules) <= expected_modules:
            raise MergeError(f"manifest lists modules absent from primary queue: {sorted(set(modules) - expected_modules)[:5]}")
        for module in modules:
            primary_rows = worker_rows(primary, module)
            incoming_rows = worker_rows(worker, module)
            if set(primary_rows) != set(incoming_rows):
                raise MergeError(f"queue row set differs for assigned module {module} in {job_dir}")
            for key, result in incoming_rows.items():
                validate_result(*result, key, str(job_dir))
        # The copy may differ only in simp_replacements rows assigned by this job.
        assigned = set(modules)
        primary_keys = {
            (row[0], int(row[1]))
            for row in primary.execute("SELECT module_name, ordinal FROM simp_replacements")
        }
        worker_keys = {
            (row[0], int(row[1]))
            for row in worker.execute("SELECT module_name, ordinal FROM simp_replacements")
        }
        if primary_keys != worker_keys:
            raise MergeError(f"simp_replacements key set drift in {job_dir}")
        for row in worker.execute("SELECT module_name, ordinal, status, replacement_text, error FROM simp_replacements"):
            key = (row[0], int(row[1]))
            if row[0] not in assigned:
                base = primary.execute(
                    "SELECT status, replacement_text, error FROM simp_replacements WHERE module_name=? AND ordinal=?", key
                ).fetchone()
                worker_value = tuple(row[2:])
                # A fresh retry database can predate completed results merged
                # by another job. Its unchanged pending row is valid input; a
                # different terminal result is an unassigned mutation.
                stale_pending = base is not None and tuple(base)[0] != "pending" and worker_value == ("pending", None, None)
                if base is None or (worker_value != tuple(base) and not stale_pending):
                    raise MergeError(f"unassigned simp_replacements mutation in {job_dir}: {key}")
        staged = []
        for module in modules:
            staged.extend((key, value, str(job_dir)) for key, value in worker_rows(worker, module).items())
        return staged
    finally:
        worker.close()


def merge(database: Path, job_dirs: list[Path]) -> dict[str, int]:
    if not job_dirs:
        raise MergeError("at least one job directory is required")
    primary = open_rw(database)
    merged = idempotent = pending = 0
    try:
        # BEGIN IMMEDIATE makes the read/validate/update sequence one atomic
        # operation. A failure rolls back every update, so the primary file is
        # the safe output and no partially merged state is exposed.
        primary.execute("BEGIN IMMEDIATE")
        table_schema(primary)
        if primary.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
            raise MergeError("primary integrity_check failed")
        seen: set[str] = set()
        staged = []
        for job_dir in job_dirs:
            staged.extend(prepare_job(primary, job_dir, seen))
        for key, incoming, label in staged:
            status, replacement, error = incoming
            current = primary.execute(
                "SELECT status, replacement_text, error FROM simp_replacements WHERE module_name=? AND ordinal=?", key
            ).fetchone()
            if current is None:
                raise MergeError(f"primary queue row disappeared: {key}")
            current = tuple(current)
            if status == "pending":
                pending += 1
                continue
            if current[0] == "pending":
                primary.execute(
                    "UPDATE simp_replacements SET status=?, replacement_text=?, error=? WHERE module_name=? AND ordinal=?",
                    (status, replacement, error, *key),
                )
                merged += 1
            elif current == incoming:
                idempotent += 1
            else:
                raise MergeError(f"conflicting terminal result for {key}: primary={current!r}, {label}={incoming!r}")
        primary.commit()
        return {"merged": merged, "identical_existing": idempotent, "returned_pending": pending, "modules": len(seen)}
    except BaseException:
        primary.rollback()
        raise
    finally:
        primary.close()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", type=Path, required=True)
    parser.add_argument("job_dirs", type=Path, nargs="+")
    args = parser.parse_args(argv)
    try:
        result = merge(args.database, args.job_dirs)
    except (OSError, sqlite3.Error, MergeError) as exc:
        print(f"merge failed: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
