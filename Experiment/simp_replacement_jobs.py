#!/usr/bin/env python3
"""Prepare independent SQLite-backed simp replacement jobs.

The module manifest is intentionally plain UTF-8: one exact module name per
line.  Each job receives its own SQLite backup and can resume by rerunning its
worker against that database.
"""

from __future__ import annotations

import argparse
from contextlib import closing
import json
import sqlite3
import sys
from pathlib import Path
from typing import Iterable


DB_NAME = "mathlib-db.sqlite3"
MANIFEST_NAME = "modules.txt"
RETRYABLE = ("pending", "record_failed", "render_failed", "compile_failed", "resource_failed", "worker_failed")


def connect_readonly(path: Path) -> sqlite3.Connection:
    uri = f"file:{path.resolve().as_posix()}?mode=ro"
    con = sqlite3.connect(uri, uri=True)
    con.row_factory = sqlite3.Row
    return con


def pending_modules(con: sqlite3.Connection, statuses: Iterable[str] = ("pending",)) -> list[tuple[str, int, int]]:
    """Return (module, candidate count, source bytes), ordered canonically."""
    statuses = tuple(statuses)
    if not statuses:
        return []
    placeholders = ",".join("?" for _ in statuses)
    rows = con.execute(
        f"""SELECT r.module_name, COUNT(*) AS candidates, length(m.source) AS source_bytes
            FROM simp_replacements AS r
            JOIN modules AS m ON m.name = r.module_name
            WHERE r.status IN ({placeholders})
            GROUP BY r.module_name
            ORDER BY r.module_name""",
        statuses,
    )
    return [(row[0], int(row[1]), int(row[2])) for row in rows]


def partition_modules(modules: list[tuple[str, int, int]], jobs: int) -> list[list[str]]:
    """Greedy LPT assignment using candidate count and source size weights."""
    if jobs < 1:
        raise ValueError("jobs must be positive")
    if jobs > len(modules):
        raise ValueError(f"jobs ({jobs}) exceeds eligible module count ({len(modules)})")
    bins: list[list[str]] = [[] for _ in range(jobs)]
    weights = [0] * jobs
    # Candidate count dominates; source size breaks ties and accounts for module
    # loading/compilation work even when the coarse SQL queue is sparse.
    weighted = sorted(
        modules,
        key=lambda item: (item[1] * 1_000_000 + item[2], item[1], item[2], item[0]),
        reverse=True,
    )
    for module, candidates, source_bytes in weighted:
        index = min(range(jobs), key=lambda i: (weights[i], i))
        bins[index].append(module)
        weights[index] += candidates * 1_000_000 + source_bytes
    for bucket in bins:
        bucket.sort()
    flattened = [name for bucket in bins for name in bucket]
    if len(flattened) != len(set(flattened)) or set(flattened) != {item[0] for item in modules}:
        raise AssertionError("partition failed exact once-only coverage")
    return bins


def sqlite_backup(source: Path, destination: Path) -> None:
    src = sqlite3.connect(f"file:{source.resolve().as_posix()}?mode=ro", uri=True)
    dst = sqlite3.connect(destination)
    try:
        src.backup(dst)
        dst.commit()
    finally:
        dst.close()
        src.close()


def prepare(database: Path, output: Path, jobs: int, statuses: Iterable[str] = ("pending",)) -> list[list[str]]:
    if output.exists():
        raise FileExistsError(f"output already exists: {output}")
    with closing(connect_readonly(database)) as con:
        modules = pending_modules(con, statuses)
    if not modules:
        raise ValueError("no eligible simp replacement modules")
    partitions = partition_modules(modules, jobs)
    output.mkdir(parents=True)
    try:
        for index, assigned in enumerate(partitions):
            job_dir = output / f"job-{index:03d}"
            job_dir.mkdir()
            (job_dir / MANIFEST_NAME).write_text("".join(f"{name}\n" for name in assigned), encoding="utf-8", newline="\n")
            sqlite_backup(database, job_dir / DB_NAME)
    except BaseException:
        # Keep partial artifacts visible for diagnosis; never remove user data.
        raise
    return partitions


def render_status(database: Path) -> dict[str, object]:
    with closing(connect_readonly(database)) as con:
        counts = {row[0]: int(row[1]) for row in con.execute("SELECT status, COUNT(*) FROM simp_replacements GROUP BY status")}
        modules = int(con.execute("SELECT COUNT(DISTINCT module_name) FROM simp_replacements").fetchone()[0])
        rows = int(con.execute("SELECT COUNT(*) FROM simp_replacements").fetchone()[0])
        by_status = {
            row[0]: int(row[1])
            for row in con.execute("SELECT status, COUNT(DISTINCT module_name) FROM simp_replacements GROUP BY status")
        }
    return {"database": str(database), "rows": rows, "modules": modules, "statuses": counts, "modules_by_status": by_status}


def write_retry_manifest(database: Path, output: Path, statuses: Iterable[str] = RETRYABLE) -> list[str]:
    if output.exists():
        raise FileExistsError(f"output already exists: {output}")
    with closing(connect_readonly(database)) as con:
        statuses = tuple(statuses)
        placeholders = ",".join("?" for _ in statuses)
        names = [row[0] for row in con.execute(
            f"SELECT DISTINCT module_name FROM simp_replacements WHERE status IN ({placeholders}) ORDER BY module_name", statuses
        )]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(f"{name}\n" for name in names), encoding="utf-8", newline="\n")
    return names


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare", help="partition eligible modules and make per-job database copies")
    prep.add_argument("--database", type=Path, required=True)
    prep.add_argument("--jobs", type=int, required=True)
    prep.add_argument("--output", type=Path, required=True)
    prep.add_argument("--statuses", default="pending", help="comma-separated queue statuses (default: pending)")
    status = sub.add_parser("status", help="report queue progress from a worker database")
    status.add_argument("--database", type=Path, required=True)
    retry = sub.add_parser("retry", help="write sorted one-module-per-line retry manifest")
    retry.add_argument("--database", type=Path, required=True)
    retry.add_argument("--output", type=Path, required=True)
    retry.add_argument("--statuses", default=",".join(RETRYABLE))
    args = parser.parse_args(argv)
    try:
        if args.command == "prepare":
            statuses = tuple(x.strip() for x in args.statuses.split(",") if x.strip())
            assignments = prepare(args.database, args.output, args.jobs, statuses)
            with closing(connect_readonly(args.database)) as con:
                weights = {name: (count, size) for name, count, size in pending_modules(con, statuses)}
            report = [{"job": i, "modules": len(names), "candidates": sum(weights[n][0] for n in names), "source_bytes": sum(weights[n][1] for n in names)} for i, names in enumerate(assignments)]
            print(json.dumps({"output": str(args.output), "jobs": report}, indent=2))
        elif args.command == "status":
            print(json.dumps(render_status(args.database), indent=2))
        else:
            names = write_retry_manifest(args.database, args.output, (x.strip() for x in args.statuses.split(",") if x.strip()))
            print(json.dumps({"output": str(args.output), "modules": len(names)}, indent=2))
    except (OSError, sqlite3.Error, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
