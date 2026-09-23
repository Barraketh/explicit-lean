#!/usr/bin/env python3
"""Checkpoint stopped simp-replacement jobs and prepare status-owned shards.

The checkpoint command starts from an immutable T76 database copy and applies
three authenticated layers in provenance order: pending, named-zeta, then
max-retry. Each worker is compared with its own source database. Only queue
rows in its exact module manifest can differ. Every incoming changed success is
checked again by the current Lean AST direct-simp postcondition. Invalid
successes are quarantined in the deterministic report and do not change the
checkpoint row.

The partition command selects modules solely from an explicit list of queue
statuses. It does not inspect theorem names or error text.
"""

from __future__ import annotations

import argparse
from collections import Counter
from contextlib import closing
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import sqlite3
import stat
import sys
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Experiment"))
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))

import merge_simp_replacement_dbs as merger  # noqa: E402
import tactic_syntax_ast as TSA  # noqa: E402


DB_NAME = "mathlib-db.sqlite3"
MANIFEST_NAME = "modules.txt"
CHECKPOINT_DB_NAME = "mathlib-db-checkpoint.sqlite3"
CHECKPOINT_REPORT_NAME = "checkpoint-audit.json"
PARTITION_REPORT_NAME = "partition.json"
REQUIRED_TABLES = ("modules", "imports", "commands", "simp_replacements")
SOURCE_TABLES = ("modules", "imports", "commands")
ALLOWED_AUXILIARY_TABLES = {
    "isolated_trace_audit",
    "isolated_trace_site_retry",
    "isolated_trace_site_retry_history",
    "isolated_trace_command_retry",
}
PARTITIONABLE_STATUSES = {
    "pending",
    "record_failed",
    "render_failed",
    "compile_failed",
    "resource_failed",
    "worker_failed",
}
SUCCESS_ORDINAL_RE = re.compile(r"success command (\d+) still owns executable simp tactic")
INPUT_RECEIPT_SCHEMA = 1
INPUT_RECEIPT_CAMPAIGN = "T78-scaleway-full-20260923"
INPUT_RECEIPT_ROLES = (
    "t76_database",
    "pending_base",
    "zeta_base",
    "maxretry_base",
    "zeta_expected_manifest",
    "pending_jobs",
    "zeta_jobs",
    "maxretry_jobs",
)
# Published artifact pins from tracking/campaign.json. These root inputs
# establish the T76 -> T65 pending / named-zeta -> max-retry lineage; the
# required receipt additionally pins each exact worker database and manifest.
PINNED_BASELINE_SHA256 = {
    "t76_database": "2c87114f971b9e7d17237fd8ed61ba3f307a502e6d379d732f017ec169202c04",
    "pending_base": "6956d43570b0d16ce8a4c4a0dedcc8595a741c2d79c2cd862b6e8256c545b01d",
    "zeta_base": "2c87114f971b9e7d17237fd8ed61ba3f307a502e6d379d732f017ec169202c04",
    "maxretry_base": "e2ee5cc13e5073e8f96c3c2a086e0f3c57aec556bd8e97d9c15ba623d2c54312",
}


class CheckpointError(ValueError):
    """A worker, manifest, database, or output-boundary invariant failed."""


@dataclass(frozen=True)
class VerifiedJobInput:
    job: str
    directory: Path
    database: Path
    manifest: Path


def _sqlite_uri(path: Path) -> str:
    # URI escaping matters when a private run root contains spaces or '#'.
    from urllib.parse import quote

    return f"file:{quote(str(path.resolve()), safe='/')}?mode=ro"


def open_ro(path: Path) -> sqlite3.Connection:
    path = _require_canonical_cli_path(path, "SQLite input", kind="file")
    require_no_sidecars(path, "SQLite input")
    con = sqlite3.connect(_sqlite_uri(path), uri=True)
    con.row_factory = sqlite3.Row
    return con


def sidecars(path: Path) -> list[Path]:
    return [Path(str(path) + suffix) for suffix in ("-wal", "-shm", "-journal")]


def require_no_sidecars(path: Path, label: str) -> None:
    present = [str(candidate) for candidate in sidecars(path) if os.path.lexists(candidate)]
    if present:
        raise CheckpointError(f"{label} has SQLite sidecars; snapshot is not closed: {present}")


def _stat_signature(value: os.stat_result) -> tuple[int, int, int, int, int]:
    return (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns)


def _hash_regular_file(path: Path, label: str) -> tuple[str, tuple[int, int, int, int, int]]:
    """Hash a stable, non-symlink regular file without following replacement races."""
    try:
        before = path.lstat()
    except OSError as error:
        raise CheckpointError(f"{label} is unavailable: {path}: {error}") from error
    if not stat.S_ISREG(before.st_mode):
        raise CheckpointError(f"{label} is not a regular non-symlink file: {path}")
    digest = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            opened = os.fstat(stream.fileno())
            if not stat.S_ISREG(opened.st_mode) or _stat_signature(opened) != _stat_signature(before):
                raise CheckpointError(f"{label} changed while being opened: {path}")
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
            after_open = os.fstat(stream.fileno())
    except OSError as error:
        raise CheckpointError(f"cannot hash {label} {path}: {error}") from error
    try:
        after_path = path.lstat()
    except OSError as error:
        raise CheckpointError(f"{label} disappeared while hashing: {path}") from error
    signature = _stat_signature(before)
    if _stat_signature(after_open) != signature or _stat_signature(after_path) != signature:
        raise CheckpointError(f"{label} changed while being hashed: {path}")
    return digest.hexdigest(), signature


def _require_canonical_cli_path(path: Path, label: str, *, kind: str) -> Path:
    """Reject relative, symlinked, or noncanonical caller-supplied paths."""
    if not isinstance(path, Path) or not path.is_absolute():
        raise CheckpointError(f"supplied CLI input path must be absolute for {label}: {path}")
    try:
        resolved = path.resolve(strict=True)
        value = path.lstat()
    except OSError as error:
        raise CheckpointError(f"supplied CLI input path is unavailable for {label}: {path}: {error}") from error
    expected_mode = stat.S_ISREG(value.st_mode) if kind == "file" else stat.S_ISDIR(value.st_mode)
    if not expected_mode or resolved != path:
        raise CheckpointError(
            f"supplied CLI input path must be canonical and non-symlink for {label}: {path}")
    return resolved


def _canonical_input_path(raw_path: Any, label: str) -> Path:
    if not isinstance(raw_path, str) or not raw_path:
        raise CheckpointError(f"input receipt has an invalid path for {label}")
    path = Path(raw_path)
    resolved = _require_canonical_cli_path(path, label, kind="file")
    if str(resolved) != raw_path:
        raise CheckpointError(f"input receipt path must name a canonical regular file for {label}: {path}")
    return resolved


def _receipt_file_entry(
    value: Any,
    *,
    label: str,
    expected_path: Path,
    is_database: bool,
    kind: str,
    snapshots: dict[str, tuple[Path, str, tuple[int, int, int, int, int]]],
) -> dict[str, str]:
    if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
        raise CheckpointError(f"input receipt entry must contain only path and sha256: {label}")
    path = _canonical_input_path(value["path"], label)
    expected = _require_canonical_cli_path(expected_path, label, kind=kind)
    if path != expected:
        raise CheckpointError(
            f"input receipt path mismatch for {label}: pinned {path}, supplied {expected}")
    expected_hash = value["sha256"]
    if not isinstance(expected_hash, str) or not re.fullmatch(r"[0-9a-f]{64}", expected_hash):
        raise CheckpointError(f"input receipt has an invalid SHA-256 for {label}")
    if is_database:
        require_no_sidecars(path, label)
    actual_hash, signature = _hash_regular_file(path, label)
    if actual_hash != expected_hash:
        raise CheckpointError(
            f"input receipt SHA-256 mismatch for {label}: expected {expected_hash}, got {actual_hash}")
    pinned_hash = PINNED_BASELINE_SHA256.get(label)
    if pinned_hash is not None and actual_hash != pinned_hash:
        raise CheckpointError(
            f"recorded campaign baseline SHA-256 mismatch for {label}: "
            f"expected {pinned_hash}, got {actual_hash}")
    snapshots[label] = (path, actual_hash, signature)
    return {"path": str(path), "sha256": actual_hash}


def validate_input_receipt(
    *,
    input_receipt: Path,
    expected_input_receipt_sha256: str,
    t76_database: Path,
    pending_base: Path,
    pending_jobs: Sequence[Path],
    zeta_base: Path,
    zeta_jobs: Sequence[Path],
    zeta_expected_manifest: Path,
    maxretry_base: Path,
    maxretry_jobs: Sequence[Path],
    maxretry_statuses: Sequence[str],
) -> dict[str, Any]:
    """Authenticate every checkpoint input before opening any SQLite file."""
    receipt_path = _require_canonical_cli_path(input_receipt, "input receipt", kind="file")
    if not isinstance(expected_input_receipt_sha256, str) or not re.fullmatch(
        r"[0-9a-f]{64}", expected_input_receipt_sha256
    ):
        raise CheckpointError("expected input-receipt SHA-256 must be 64 lowercase hexadecimal characters")
    receipt_hash, receipt_signature = _hash_regular_file(receipt_path, "input receipt")
    if receipt_hash != expected_input_receipt_sha256:
        raise CheckpointError(
            "input receipt SHA-256 mismatch before database access: "
            f"expected {expected_input_receipt_sha256}, got {receipt_hash}")
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise CheckpointError(f"cannot read input receipt {receipt_path}: {error}") from error
    if _stat_signature(receipt_path.stat()) != receipt_signature:
        raise CheckpointError("input receipt changed while being parsed")
    if not isinstance(receipt, dict) or set(receipt) != {"schema", "campaign", "maxretry_statuses", "inputs"}:
        raise CheckpointError("input receipt has an unsupported shape")
    if receipt["schema"] != INPUT_RECEIPT_SCHEMA or receipt["campaign"] != INPUT_RECEIPT_CAMPAIGN:
        raise CheckpointError("input receipt schema or campaign does not match this checkpoint")
    if receipt["maxretry_statuses"] != list(maxretry_statuses):
        raise CheckpointError("input receipt max-retry statuses differ from the explicit selection")
    inputs = receipt["inputs"]
    if not isinstance(inputs, dict) or set(inputs) != set(INPUT_RECEIPT_ROLES):
        raise CheckpointError("input receipt must pin all required baseline, worker, and manifest inputs")

    # Inspect every caller-supplied path before hashing/opening any database.
    # This includes the directories themselves and each expected file beneath
    # them; later access is through the receipt-resolved paths below.
    singular_cli_paths = (
        ("t76_database", t76_database),
        ("pending_base", pending_base),
        ("zeta_base", zeta_base),
        ("maxretry_base", maxretry_base),
        ("zeta_expected_manifest", zeta_expected_manifest),
    )
    for role, path in singular_cli_paths:
        _require_canonical_cli_path(path, role, kind="file")
    for role, supplied_jobs, expected_count in (
        ("pending_jobs", pending_jobs, 4),
        ("zeta_jobs", zeta_jobs, 2),
        ("maxretry_jobs", maxretry_jobs, 2),
    ):
        if len(supplied_jobs) != expected_count:
            raise CheckpointError(f"{role} requires exactly {expected_count} jobs, got {len(supplied_jobs)}")
        for index, supplied_job in enumerate(supplied_jobs):
            job_dir = _require_canonical_cli_path(supplied_job, f"{role}.job-{index:03d}", kind="directory")
            if job_dir.name != f"job-{index:03d}":
                raise CheckpointError(f"input receipt/job order mismatch for {role} job-{index:03d}")
            _require_canonical_cli_path(job_dir / DB_NAME, f"{role}.job-{index:03d}.database", kind="file")
            _require_canonical_cli_path(job_dir / MANIFEST_NAME, f"{role}.job-{index:03d}.manifest", kind="file")

    snapshots: dict[str, tuple[Path, str, tuple[int, int, int, int, int]]] = {
        "input_receipt": (receipt_path, receipt_hash, receipt_signature)
    }
    resolved_inputs: dict[str, Any] = {}
    singulars = (
        ("t76_database", t76_database, True, "file"),
        ("pending_base", pending_base, True, "file"),
        ("zeta_base", zeta_base, True, "file"),
        ("maxretry_base", maxretry_base, True, "file"),
        ("zeta_expected_manifest", zeta_expected_manifest, False, "file"),
    )
    for role, supplied_path, is_database, kind in singulars:
        supplied_path = _require_canonical_cli_path(supplied_path, role, kind=kind)
        resolved_inputs[role] = _receipt_file_entry(
            inputs[role], label=role, expected_path=supplied_path,
            is_database=is_database, kind=kind, snapshots=snapshots)
    verified_job_inputs: dict[str, list[VerifiedJobInput]] = {}

    for role, supplied_jobs, expected_count in (
        ("pending_jobs", pending_jobs, 4),
        ("zeta_jobs", zeta_jobs, 2),
        ("maxretry_jobs", maxretry_jobs, 2),
    ):
        entries = inputs[role]
        if len(supplied_jobs) != expected_count or not isinstance(entries, list) or len(entries) != expected_count:
            raise CheckpointError(f"input receipt must pin exactly {expected_count} {role}")
        verified_jobs = []
        verified_paths_for_jobs = []
        for index, (job_dir, entry) in enumerate(zip(supplied_jobs, entries)):
            job_dir = _require_canonical_cli_path(job_dir, f"{role}.job-{index:03d}", kind="directory")
            job_name = f"job-{index:03d}"
            if job_dir.name != job_name or not isinstance(entry, dict) or set(entry) != {
                "job", "database", "manifest"
            } or entry["job"] != job_name:
                raise CheckpointError(f"input receipt/job order mismatch for {role} {job_name}")
            verified_database = _receipt_file_entry(
                entry["database"], label=f"{role}.{job_name}.database",
                expected_path=job_dir / DB_NAME, is_database=True, kind="file", snapshots=snapshots)
            verified_manifest = _receipt_file_entry(
                entry["manifest"], label=f"{role}.{job_name}.manifest",
                expected_path=job_dir / MANIFEST_NAME, is_database=False, kind="file", snapshots=snapshots)
            verified_jobs.append({
                "job": job_name,
                "database": verified_database,
                "manifest": verified_manifest,
            })
            verified_paths_for_jobs.append(VerifiedJobInput(
                job=job_name,
                directory=job_dir,
                database=Path(verified_database["path"]),
                manifest=Path(verified_manifest["path"]),
            ))
        verified_job_inputs[role] = verified_paths_for_jobs
        resolved_inputs[role] = verified_jobs
    # Duplicate worker paths would make a receipt look complete while pinning
    # fewer independent job artifacts than the contract requires.
    worker_paths = [
        item[field]["path"]
        for role in ("pending_jobs", "zeta_jobs", "maxretry_jobs")
        for item in resolved_inputs[role]
        for field in ("database", "manifest")
    ]
    if len(worker_paths) != len(set(worker_paths)):
        raise CheckpointError("input receipt reuses a worker database or manifest path")
    singleton_paths = {
        resolved_inputs[role]["path"]
        for role in INPUT_RECEIPT_ROLES[:5]
    }
    if singleton_paths.intersection(worker_paths):
        raise CheckpointError("input receipt reuses a baseline or expected manifest as a worker input")
    return {
        "receipt": {
            "path": str(receipt_path),
            "expectedSha256": expected_input_receipt_sha256,
            "actualSha256": receipt_hash,
        },
        "inputs": resolved_inputs,
        "_paths": {
            "t76_database": Path(resolved_inputs["t76_database"]["path"]),
            "pending_base": Path(resolved_inputs["pending_base"]["path"]),
            "zeta_base": Path(resolved_inputs["zeta_base"]["path"]),
            "maxretry_base": Path(resolved_inputs["maxretry_base"]["path"]),
            "zeta_expected_manifest": Path(resolved_inputs["zeta_expected_manifest"]["path"]),
            **verified_job_inputs,
        },
        "_snapshots": snapshots,
    }


def verify_receipt_snapshot(verified: dict[str, Any]) -> None:
    """Fail if any receipt-pinned file moved or changed during validation."""
    snapshots = verified["_snapshots"]
    for label, (path, expected_hash, signature) in snapshots.items():
        actual_hash, actual_signature = _hash_regular_file(path, label)
        if actual_signature != signature or actual_hash != expected_hash:
            raise CheckpointError(f"receipt-pinned input changed during checkpoint validation: {label}")
        if label.endswith("database") or label in {
            "t76_database", "pending_base", "zeta_base", "maxretry_base"
        }:
            require_no_sidecars(path, label)


def integrity_check(con: sqlite3.Connection, label: str) -> None:
    rows = [str(row[0]) for row in con.execute("PRAGMA integrity_check")]
    if rows != ["ok"]:
        raise CheckpointError(f"PRAGMA integrity_check failed for {label}: {rows[:8]}")


def table_names(con: sqlite3.Connection) -> set[str]:
    return {
        str(row[0])
        for row in con.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name NOT LIKE 'sqlite_%'"
        )
    }


def schema_signature(con: sqlite3.Connection, table: str) -> tuple[Any, ...]:
    create = con.execute(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name=?", (table,)
    ).fetchone()
    if create is None:
        raise CheckpointError(f"required table is missing: {table}")
    columns = tuple(tuple(row) for row in con.execute(f"PRAGMA table_info({table})"))
    attached = tuple(tuple(row) for row in con.execute(
        "SELECT type,name,tbl_name,sql FROM sqlite_master "
        "WHERE tbl_name=? AND type IN ('index','trigger') "
        "AND name NOT LIKE 'sqlite_%' ORDER BY type,name", (table,)))
    return create[0], columns, attached


def database_schema_signature(con: sqlite3.Connection) -> tuple[tuple[Any, ...], ...]:
    objects = tuple(tuple(row) for row in con.execute(
        "SELECT type,name,tbl_name,sql FROM sqlite_master "
        "WHERE name NOT LIKE 'sqlite_%' ORDER BY type,name"))
    has_sequence = con.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='sqlite_sequence'"
    ).fetchone() is not None
    sequence_schema = tuple(tuple(row) for row in con.execute("PRAGMA table_info(sqlite_sequence)")) if has_sequence else ()
    return objects, sequence_schema


def database_table_digests(con: sqlite3.Connection) -> dict[str, str]:
    names = table_names(con)
    if con.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='sqlite_sequence'"
    ).fetchone() is not None:
        names.add("sqlite_sequence")
    return {table: row_digest(con, table) for table in sorted(names)}


def validate_schema(base: sqlite3.Connection, worker: sqlite3.Connection, label: str) -> None:
    for con, con_label in ((base, "baseline"), (worker, "worker")):
        missing = set(REQUIRED_TABLES) - table_names(con)
        if missing:
            raise CheckpointError(f"{con_label} database missing required tables in {label}: {sorted(missing)}")
    for table in REQUIRED_TABLES:
        if schema_signature(base, table) != schema_signature(worker, table):
            raise CheckpointError(f"core schema drift in {label}: {table}")
    for con, con_label in ((base, "baseline"), (worker, "worker")):
        unknown = table_names(con) - set(REQUIRED_TABLES) - ALLOWED_AUXILIARY_TABLES
        if unknown:
            raise CheckpointError(f"unsupported auxiliary schema in {label} ({con_label}): {sorted(unknown)}")
    base_aux = table_names(base) - set(REQUIRED_TABLES)
    worker_aux = table_names(worker) - set(REQUIRED_TABLES)
    if not base_aux <= worker_aux:
        raise CheckpointError(f"worker dropped baseline auxiliary tables in {label}: {sorted(base_aux - worker_aux)}")
    for table in worker_aux:
        columns = [row[1] for row in worker.execute(f"PRAGMA table_info({table})")]
        if "module_name" not in columns:
            raise CheckpointError(f"auxiliary table is not module-owned in {label}: {table}")
        if table in base_aux and schema_signature(base, table) != schema_signature(worker, table):
            raise CheckpointError(f"auxiliary schema drift in {label}: {table}")


def _json_value(value: Any) -> Any:
    return {"blob": value.hex()} if isinstance(value, bytes) else value


def row_digest(con: sqlite3.Connection, table: str) -> str:
    info = con.execute(f"PRAGMA table_info({table})").fetchall()
    columns = [row[1] for row in info]
    primary = [row[1] for row in sorted((row for row in info if row[5]), key=lambda row: row[5])]
    order = primary or columns
    digest = hashlib.sha256()
    digest.update(json.dumps(columns, separators=(",", ":")).encode())
    for row in con.execute(f"SELECT {', '.join(columns)} FROM {table} ORDER BY {', '.join(order)}"):
        payload = [_json_value(value) for value in row]
        digest.update(json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


def source_identity_for_path(
    path: Path, cache: dict[str, dict[str, str]], label: str,
) -> dict[str, str]:
    key = str(path.resolve())
    if key not in cache:
        require_no_sidecars(path, label)
        with closing(open_ro(path)) as con:
            integrity_check(con, label)
            cache[key] = {table: row_digest(con, table) for table in SOURCE_TABLES}
    return cache[key]


def row_map(con: sqlite3.Connection, module: str | None = None) -> dict[tuple[str, int], tuple[str, str | None, str | None]]:
    sql = "SELECT module_name, ordinal, status, replacement_text, error FROM simp_replacements"
    args: tuple[Any, ...] = ()
    if module is not None:
        sql += " WHERE module_name=?"
        args = (module,)
    sql += " ORDER BY module_name, ordinal"
    return {
        (str(row[0]), int(row[1])): (str(row[2]), row[3], row[4])
        for row in con.execute(sql, args)
    }


def validate_result(value: tuple[str, str | None, str | None], key: tuple[str, int], label: str) -> None:
    merger.validate_result(*value, key, label)


def canonical_manifest(path: Path, *, allow_empty: bool = False) -> list[str]:
    path = _require_canonical_cli_path(path, "module manifest", kind="file")
    modules = merger.read_manifest(path)
    if not modules and not allow_empty:
        raise CheckpointError(f"manifest must not be empty: {path}")
    if modules != sorted(modules):
        raise CheckpointError(f"manifest must be in canonical sorted order: {path}")
    return modules


def write_manifest(path: Path, modules: Sequence[str]) -> None:
    path.write_text("".join(f"{name}\n" for name in modules), encoding="utf-8", newline="\n")


def _rows_by_module_digest(con: sqlite3.Connection, table: str, excluded: set[str]) -> str:
    info = con.execute(f"PRAGMA table_info({table})").fetchall()
    columns = [row[1] for row in info]
    pk = [row[1] for row in sorted((row for row in info if row[5]), key=lambda row: row[5])]
    order = ["module_name", *(column for column in pk if column != "module_name")]
    if len(order) == 1:
        order = ["module_name", *(column for column in columns if column != "module_name")]
    digest = hashlib.sha256()
    digest.update(json.dumps(columns, separators=(",", ":")).encode())
    for row in con.execute(f"SELECT {', '.join(columns)} FROM {table} ORDER BY {', '.join(order)}"):
        if row[columns.index("module_name")] in excluded:
            continue
        digest.update(json.dumps([_json_value(v) for v in row], ensure_ascii=False,
                                 separators=(",", ":")).encode("utf-8"))
        digest.update(b"\n")
    return digest.hexdigest()


def status_modules(con: sqlite3.Connection, statuses: Sequence[str]) -> list[str]:
    placeholders = ",".join("?" for _ in statuses)
    return [str(row[0]) for row in con.execute(
        f"SELECT DISTINCT module_name FROM simp_replacements WHERE status IN ({placeholders}) ORDER BY module_name",
        tuple(statuses),
    )]


def _status_rows_by_module(con: sqlite3.Connection, statuses: Sequence[str]) -> list[tuple[str, int, int]]:
    placeholders = ",".join("?" for _ in statuses)
    return [
        (str(row[0]), int(row[1]), int(row[2]))
        for row in con.execute(
            f"""SELECT r.module_name, COUNT(*), length(m.source)
                FROM simp_replacements AS r JOIN modules AS m ON m.name=r.module_name
                WHERE r.status IN ({placeholders})
                GROUP BY r.module_name ORDER BY r.module_name""",
            tuple(statuses),
        )
    ]


def deterministic_partition(rows: Sequence[tuple[str, int, int]], jobs: int) -> list[list[str]]:
    if type(jobs) is not int or jobs < 1 or jobs > 8:
        raise CheckpointError("jobs must be between 1 and 8")
    if jobs > len(rows):
        raise CheckpointError(f"jobs ({jobs}) exceeds eligible module count ({len(rows)})")
    bins: list[list[str]] = [[] for _ in range(jobs)]
    weights = [0] * jobs
    # LPT scheduling. All ties have a canonical module and bin order.
    ordered = sorted(rows, key=lambda item: (-(item[1] * 1_000_000 + item[2]), -item[1], -item[2], item[0]))
    for module, count, source_bytes in ordered:
        slot = min(range(jobs), key=lambda index: (weights[index], index))
        bins[slot].append(module)
        weights[slot] += count * 1_000_000 + source_bytes
    for names in bins:
        names.sort()
    flattened = [module for names in bins for module in names]
    if len(flattened) != len(set(flattened)) or set(flattened) != {row[0] for row in rows}:
        raise AssertionError("partition failed exact disjoint coverage")
    return bins


def _group_job_count(label: str, jobs: Sequence[VerifiedJobInput], expected: int) -> None:
    if len(jobs) != expected:
        raise CheckpointError(f"{label} requires exactly {expected} jobs, got {len(jobs)}")


def _check_auxiliary_outside_ownership(
    baseline: sqlite3.Connection,
    worker: sqlite3.Connection,
    assigned: set[str],
    label: str,
) -> None:
    base_aux = table_names(baseline) - set(REQUIRED_TABLES)
    worker_aux = table_names(worker) - set(REQUIRED_TABLES)
    for table in sorted(worker_aux):
        if table not in base_aux:
            # New retry tables are allowed, but each inserted row must name a
            # module owned by this job.
            row = worker.execute(
                f"SELECT module_name FROM {table} WHERE module_name IS NULL "
                f"OR module_name NOT IN ({','.join('?' for _ in assigned)}) LIMIT 1",
                tuple(sorted(assigned)),
            ).fetchone() if assigned else worker.execute(f"SELECT module_name FROM {table} LIMIT 1").fetchone()
            if row is not None:
                raise CheckpointError(f"unassigned auxiliary row in {label}: {table}:{row[0]}")
            continue
        if _rows_by_module_digest(baseline, table, assigned) != _rows_by_module_digest(worker, table, assigned):
            raise CheckpointError(f"unassigned auxiliary mutation in {label}: {table}")


def validate_job_group(
    *,
    label: str,
    baseline_path: Path,
    job_dirs: Sequence[VerifiedJobInput],
    expected_modules: Sequence[str],
    source_base_identity: dict[str, str],
    identity_cache: dict[str, dict[str, str]],
    table_digest_cache: dict[str, dict[str, str]],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    expected = set(expected_modules)
    manifest_union: set[str] = set()
    mutations: list[dict[str, Any]] = []
    baseline_identity = source_identity_for_path(baseline_path, identity_cache, f"{label} baseline")
    if baseline_identity != source_base_identity:
        changed_tables = [table for table in SOURCE_TABLES
                          if baseline_identity[table] != source_base_identity[table]]
        raise CheckpointError(f"{label} baseline source identity differs from T76: {changed_tables}")

    with closing(open_ro(baseline_path)) as baseline:
        integrity_check(baseline, f"{label} baseline")
        base_queue = row_map(baseline)
        base_keys = set(base_queue)
        known_modules = {module for module, _ordinal in base_keys}
        baseline_key = str(baseline_path.resolve())
        if baseline_key not in table_digest_cache:
            table_digest_cache[baseline_key] = {
                table: row_digest(baseline, table) for table in SOURCE_TABLES
            }
        for job_index, job in enumerate(job_dirs):
            job_dir = job.directory
            manifest_path = job.manifest
            database_path = job.database
            if not manifest_path.is_file() or not database_path.is_file():
                raise CheckpointError(f"{label} {job.job} lacks {MANIFEST_NAME} or {DB_NAME}: {job_dir}")
            require_no_sidecars(database_path, f"{label} job {job_index:03d}")
            modules = canonical_manifest(manifest_path)
            overlap = manifest_union.intersection(modules)
            if overlap:
                raise CheckpointError(f"{label} manifests overlap: {sorted(overlap)[:8]}")
            assigned = set(modules)
            missing_modules = assigned - known_modules
            if missing_modules:
                raise CheckpointError(
                    f"{label} manifest names modules absent from its baseline: {sorted(missing_modules)[:8]}")
            manifest_union.update(modules)
            with closing(open_ro(database_path)) as worker:
                integrity_check(worker, f"{label} {job.job}")
                validate_schema(baseline, worker, f"{label} {job.job}")
                worker_key = str(database_path.resolve())
                if worker_key not in table_digest_cache:
                    table_digest_cache[worker_key] = {
                        table: row_digest(worker, table) for table in SOURCE_TABLES
                    }
                for table in SOURCE_TABLES:
                    if table_digest_cache[baseline_key][table] != table_digest_cache[worker_key][table]:
                        raise CheckpointError(f"source table differs in {label} {job.job}: {table}")
                worker_queue = row_map(worker)
                if set(worker_queue) != base_keys:
                    raise CheckpointError(f"simp_replacements key set differs in {label} {job.job}")
                _check_auxiliary_outside_ownership(
                    baseline, worker, assigned, f"{label} {job.job}")
                for key, worker_value in worker_queue.items():
                    base_value = base_queue[key]
                    validate_result(worker_value, key, f"{label} {job.job}")
                    if key[0] not in assigned:
                        if worker_value != base_value:
                            raise CheckpointError(
                                f"unassigned simp_replacements mutation in {label} {job.job}: {key}")
                    elif worker_value != base_value:
                        mutations.append({
                            "layer": label,
                            "job": job.job,
                            "module": key[0],
                            "ordinal": key[1],
                            "baseline": base_value,
                            "incoming": worker_value,
                        })
    if manifest_union != expected:
        missing = sorted(expected - manifest_union)
        extra = sorted(manifest_union - expected)
        raise CheckpointError(
            f"{label} manifest union does not exactly match expected modules: "
            f"missing={missing[:8]} ({len(missing)}), extra={extra[:8]} ({len(extra)})")
    return mutations, {
        "jobs": len(job_dirs),
        "modules": len(manifest_union),
        "changedRows": len(mutations),
        "manifestSha256": hashlib.sha256(
            "".join(f"{module}\n" for module in sorted(manifest_union)).encode("utf-8")
        ).hexdigest(),
    }


def _normalized_reason(error: BaseException) -> str:
    message = " ".join(str(error).split())
    message = re.sub(r"(?:/tmp|/private/var/folders)/[^\s]*/lean-tactic-syntax-[^\s/]+", "<temporary>", message)
    return f"{type(error).__name__}: {message}"[:2000]


def _load_module_source(
    con: sqlite3.Connection,
    module: str,
) -> tuple[bytes, str, list[dict[str, Any]]]:
    record = con.execute("SELECT source, source_sha256 FROM modules WHERE name=?", (module,)).fetchone()
    if record is None:
        raise CheckpointError(f"module source is missing: {module}")
    raw = bytes(record[0])
    try:
        source = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise CheckpointError(f"module source is not UTF-8: {module}") from error
    source_hash = str(record[1])
    commands = [
        {"ordinal": int(row[0]), "start": int(row[1]), "end": int(row[2]),
         "kind": str(row[3]), "source_sha256": str(row[4])}
        for row in con.execute(
            "SELECT ordinal,start_byte,end_byte,kind,source_sha256 FROM commands "
            "WHERE module_name=? ORDER BY ordinal", (module,)
        )
    ]
    return raw, source, commands


def validate_incoming_successes(
    *,
    module: str,
    current_rows: dict[tuple[str, int], tuple[str, str | None, str | None]],
    incoming_successes: dict[int, str],
    source_db: sqlite3.Connection,
    repo_root: Path,
) -> tuple[set[int], dict[int, str]]:
    """Return accepted and quarantined ordinals, isolating a bad AST owner."""
    if not incoming_successes:
        return set(), {}
    raw, original, commands = _load_module_source(source_db, module)
    source_record = source_db.execute("SELECT source_sha256 FROM modules WHERE name=?", (module,)).fetchone()
    expected_sha = str(source_record[0])
    active = dict(incoming_successes)
    quarantined: dict[int, str] = {}
    while active:
        replacements = {
            ordinal: str(value[1])
            for (name, ordinal), value in current_rows.items()
            if name == module and value[0] == "success" and value[1] is not None
        }
        replacements.update(active)
        try:
            candidate = merger._candidate_with_replacements(raw, commands, replacements)
            TSA.assert_success_commands_have_no_simp(
                module=module,
                original_source=original,
                candidate_source=candidate,
                expected_source_sha256=expected_sha,
                command_rows=commands,
                success_ordinals=set(active),
                candidate_replacements=replacements,
                repo_root=repo_root,
            )
            return set(active), quarantined
        except (OSError, RuntimeError, UnicodeError, ValueError) as error:
            reason = _normalized_reason(error)
            match = SUCCESS_ORDINAL_RE.search(str(error))
            if match is not None and int(match.group(1)) in active:
                rejected = int(match.group(1))
                quarantined[rejected] = reason
                del active[rejected]
                continue
            # A parser/context/source refusal cannot be localized to one site.
            # Quarantine each affected incoming success with the same exact cause.
            for ordinal in sorted(active):
                quarantined[ordinal] = reason
            return set(), quarantined
    return set(), quarantined


def _safe_apply_layer(
    *,
    label: str,
    mutations: Sequence[dict[str, Any]],
    state: dict[tuple[str, int], tuple[str, str | None, str | None]],
    source_db: sqlite3.Connection,
    repo_root: Path,
    reparse_incoming_successes: bool,
) -> tuple[list[dict[str, Any]], Counter[str]]:
    by_module: dict[str, list[dict[str, Any]]] = {}
    for mutation in mutations:
        by_module.setdefault(str(mutation["module"]), []).append(mutation)
    audit: list[dict[str, Any]] = []
    stats: Counter[str] = Counter()
    for module in sorted(by_module):
        module_changes = sorted(by_module[module], key=lambda item: (item["job"], item["ordinal"]))
        incoming_successes = {
            int(item["ordinal"]): str(item["incoming"][1])
            for item in module_changes
            if item["incoming"][0] == "success" and item["incoming"] != item["baseline"]
        }
        if reparse_incoming_successes:
            accepted, quarantined = validate_incoming_successes(
                module=module,
                current_rows=state,
                incoming_successes=incoming_successes,
                source_db=source_db,
                repo_root=repo_root,
            )
        else:
            accepted, quarantined = set(incoming_successes), {}
        for ordinal, reason in sorted(quarantined.items()):
            related = next(item for item in module_changes if int(item["ordinal"]) == ordinal)
            audit.append({
                "layer": label,
                "job": related["job"],
                "module": module,
                "ordinal": ordinal,
                "action": "quarantined_invalid_success",
                "reason": reason,
            })
            stats["quarantined_invalid_successes"] += 1
        for ordinal in sorted(accepted):
            related = next(item for item in module_changes if int(item["ordinal"]) == ordinal)
            audit.append({
                "layer": label,
                "job": related["job"],
                "module": module,
                "ordinal": ordinal,
                "action": ("validated_incoming_success" if reparse_incoming_successes
                           else "trusted_recorded_success"),
                "reason": ("current TSA direct-simp postcondition passed" if reparse_incoming_successes
                           else "success reparse explicitly skipped for fast checkpointing"),
            })
            stats[("validated_incoming_successes" if reparse_incoming_successes
                   else "trusted_recorded_successes")] += 1

        for mutation in module_changes:
            ordinal = int(mutation["ordinal"])
            key = (module, ordinal)
            baseline = tuple(mutation["baseline"])
            incoming = tuple(mutation["incoming"])
            current = state[key]
            if incoming[0] == "success" and ordinal not in accepted:
                continue
            if current[0] == "success" and current != incoming:
                if baseline != current:
                    audit.append({
                        "layer": label,
                        "job": mutation["job"],
                        "module": module,
                        "ordinal": ordinal,
                        "action": "preserved_current_success",
                        "reason": "incoming result was computed from a baseline row different from the current success",
                    })
                    stats["preserved_current_successes"] += 1
                    continue
                if incoming[0] != "success":
                    audit.append({
                        "layer": label,
                        "job": mutation["job"],
                        "module": module,
                        "ordinal": ordinal,
                        "action": "preserved_current_success",
                        "reason": "incoming non-success cannot replace a current success",
                    })
                    stats["preserved_current_successes"] += 1
                    continue
            if incoming[0] == "pending":
                stats["pending_results_ignored"] += 1
                continue
            if current == incoming:
                stats["identical_rows"] += 1
            else:
                state[key] = incoming  # type: ignore[assignment]
                stats[f"applied_{incoming[0]}"] += 1
    return audit, stats


def _sqlite_backup(source: Path, destination: Path) -> None:
    source = _require_canonical_cli_path(source, "database copy source", kind="file")
    require_no_sidecars(source, "database copy source")
    src = sqlite3.connect(_sqlite_uri(source), uri=True)
    dst = sqlite3.connect(destination)
    try:
        src.backup(dst)
        dst.commit()
        integrity_check(dst, f"new copy {destination}")
    finally:
        dst.close()
        src.close()


def _checkpoint_group_inputs(
    *,
    t76_database: Path,
    pending_base: Path,
    pending_jobs: Sequence[VerifiedJobInput],
    zeta_base: Path,
    zeta_jobs: Sequence[VerifiedJobInput],
    zeta_expected_manifest: Path,
    maxretry_base: Path,
    maxretry_jobs: Sequence[VerifiedJobInput],
    maxretry_statuses: Sequence[str],
    identity_cache: dict[str, dict[str, str]],
) -> tuple[list[tuple[str, list[dict[str, Any]], Path]], dict[str, Any]]:
    _group_job_count("pending layer", pending_jobs, 4)
    _group_job_count("named-zeta layer", zeta_jobs, 2)
    _group_job_count("max-retry layer", maxretry_jobs, 2)
    if not maxretry_statuses or len(maxretry_statuses) != len(set(maxretry_statuses)):
        raise CheckpointError("max-retry expected statuses must be explicit, nonempty, and unique")
    if not set(maxretry_statuses) <= PARTITIONABLE_STATUSES:
        raise CheckpointError(f"invalid max-retry selection statuses: {sorted(set(maxretry_statuses) - PARTITIONABLE_STATUSES)}")
    if not zeta_expected_manifest.is_file():
        raise CheckpointError("named-zeta requires a pre-run expected-module manifest")
    t76_identity = source_identity_for_path(t76_database, identity_cache, "T76 base")
    with closing(open_ro(t76_database)) as t76:
        integrity_check(t76, "T76 base")
        t76_rows = row_map(t76)
        t76_keys = set(t76_rows)
        t76_core_schema = {table: schema_signature(t76, table) for table in REQUIRED_TABLES}
    group_specs = [
        ("pending", pending_base, pending_jobs),
        ("named_zeta", zeta_base, zeta_jobs),
        ("max_retry", maxretry_base, maxretry_jobs),
    ]
    staged_groups: list[tuple[str, list[dict[str, Any]], Path]] = []
    layer_reports: dict[str, Any] = {}
    table_digest_cache: dict[str, dict[str, str]] = {}
    for label, base, jobs in group_specs:
        with closing(open_ro(base)) as group_base:
            integrity_check(group_base, f"{label} baseline")
            for table in REQUIRED_TABLES:
                if schema_signature(group_base, table) != t76_core_schema[table]:
                    raise CheckpointError(f"{label} baseline schema differs from T76: {table}")
            if set(row_map(group_base)) != t76_keys:
                raise CheckpointError(f"simp_replacements key set differs from T76 in {label} baseline")
            if label == "pending":
                expected = status_modules(group_base, ("pending",))
            elif label == "named_zeta":
                expected = canonical_manifest(zeta_expected_manifest)
            else:
                expected = status_modules(group_base, maxretry_statuses)
        mutations, report = validate_job_group(
            label=label,
            baseline_path=base,
            job_dirs=jobs,
            expected_modules=expected,
            source_base_identity=t76_identity,
            identity_cache=identity_cache,
            table_digest_cache=table_digest_cache,
        )
        report["expectedModules"] = len(expected)
        report["selectedStatuses"] = list(maxretry_statuses) if label == "max_retry" else (
            ["pending"] if label == "pending" else None)
        layer_reports[label] = report
        staged_groups.append((label, mutations, base))
    return staged_groups, {
        "schema": 1,
        "tool": "Experiment/t78_checkpoint_prepare.py",
        "baseSourceTables": t76_identity,
        "layers": layer_reports,
    }


def create_checkpoint(
    *,
    input_receipt: Path,
    expected_input_receipt_sha256: str,
    t76_database: Path,
    pending_base: Path,
    pending_jobs: Sequence[Path],
    zeta_base: Path,
    zeta_jobs: Sequence[Path],
    zeta_expected_manifest: Path,
    maxretry_base: Path,
    maxretry_jobs: Sequence[Path],
    maxretry_statuses: Sequence[str],
    output_root: Path,
    repo_root: Path = ROOT,
    reparse_incoming_successes: bool = True,
) -> dict[str, Any]:
    verified_inputs = validate_input_receipt(
        input_receipt=input_receipt,
        expected_input_receipt_sha256=expected_input_receipt_sha256,
        t76_database=t76_database,
        pending_base=pending_base,
        pending_jobs=pending_jobs,
        zeta_base=zeta_base,
        zeta_jobs=zeta_jobs,
        zeta_expected_manifest=zeta_expected_manifest,
        maxretry_base=maxretry_base,
        maxretry_jobs=maxretry_jobs,
        maxretry_statuses=maxretry_statuses,
    )
    # Detect replacement between receipt hashing and the first database or
    # manifest read. All subsequent input paths come from this receipt.
    verify_receipt_snapshot(verified_inputs)
    if output_root.exists():
        raise FileExistsError(f"output root already exists: {output_root}")
    verified_paths = verified_inputs["_paths"]
    identity_cache: dict[str, dict[str, str]] = {}
    staged_groups, report = _checkpoint_group_inputs(
        t76_database=verified_paths["t76_database"],
        pending_base=verified_paths["pending_base"],
        pending_jobs=verified_paths["pending_jobs"],
        zeta_base=verified_paths["zeta_base"],
        zeta_jobs=verified_paths["zeta_jobs"],
        zeta_expected_manifest=verified_paths["zeta_expected_manifest"],
        maxretry_base=verified_paths["maxretry_base"],
        maxretry_jobs=verified_paths["maxretry_jobs"],
        maxretry_statuses=maxretry_statuses,
        identity_cache=identity_cache,
    )
    verify_receipt_snapshot(verified_inputs)
    with closing(open_ro(verified_paths["t76_database"])) as base:
        state = row_map(base)
    audit_entries: list[dict[str, Any]] = []
    transition_counts: Counter[str] = Counter()
    for label, mutations, baseline_path in staged_groups:
        with closing(open_ro(baseline_path)) as baseline:
            layer_audit, stats = _safe_apply_layer(
                label=label,
                mutations=mutations,
                state=state,
                source_db=baseline,
                repo_root=repo_root,
                reparse_incoming_successes=reparse_incoming_successes,
            )
        audit_entries.extend(layer_audit)
        transition_counts.update(stats)
        report["layers"][label]["applied"] = dict(sorted(stats.items()))
    report["audit"] = sorted(
        audit_entries,
        key=lambda item: (item["layer"], item["module"], item["ordinal"], item["job"], item["action"], item["reason"]),
    )
    report["summary"] = {
        "incomingChangedRows": sum(layer["changedRows"] for layer in report["layers"].values()),
        "successReparse": "performed" if reparse_incoming_successes else "skipped",
        "quarantinedInvalidSuccesses": transition_counts["quarantined_invalid_successes"],
        "preservedCurrentSuccesses": transition_counts["preserved_current_successes"],
    }
    report["inputReceipt"] = verified_inputs["receipt"]
    report["verifiedInputs"] = verified_inputs["inputs"]

    # The same immutable artifacts are opened read-only throughout validation;
    # rehash immediately before creating the output copy to close the gap
    # between preflight and use.
    verify_receipt_snapshot(verified_inputs)
    output_root.parent.mkdir(parents=True, exist_ok=True)
    output_root.mkdir()
    output_database = output_root / CHECKPOINT_DB_NAME
    try:
        _sqlite_backup(verified_paths["t76_database"], output_database)
        output = sqlite3.connect(output_database)
        try:
            output.execute("PRAGMA foreign_keys=ON")
            output.execute("BEGIN IMMEDIATE")
            for (module, ordinal), value in sorted(state.items()):
                # The root copy already contains the original row. Update only
                # rows whose final state differs; all source and audit tables
                # stay as they were in the T76 database.
                current = output.execute(
                    "SELECT status,replacement_text,error FROM simp_replacements WHERE module_name=? AND ordinal=?",
                    (module, ordinal),
                ).fetchone()
                if current is None:
                    raise CheckpointError(f"T76 output row disappeared: {module}:{ordinal}")
                if tuple(current) != value:
                    output.execute(
                        "UPDATE simp_replacements SET status=?,replacement_text=?,error=? "
                        "WHERE module_name=? AND ordinal=?",
                        (*value, module, ordinal),
                    )
            output.commit()
            integrity_check(output, "checkpoint output")
        except BaseException:
            output.rollback()
            raise
        finally:
            output.close()
        verify_receipt_snapshot(verified_inputs)
        report["outputDatabase"] = CHECKPOINT_DB_NAME
        report["outputIntegrity"] = "ok"
        (output_root / CHECKPOINT_REPORT_NAME).write_text(
            json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
            encoding="utf-8",
            newline="\n",
        )
    except BaseException:
        # The directory was created by this invocation and is retained with
        # partial evidence for diagnosis; no input path is ever modified.
        raise
    return report


def create_partitions(
    *,
    database: Path,
    output_root: Path,
    jobs: int,
    statuses: Sequence[str],
) -> dict[str, Any]:
    if output_root.exists():
        raise FileExistsError(f"output root already exists: {output_root}")
    if not statuses or len(statuses) != len(set(statuses)):
        raise CheckpointError("partition statuses must be explicitly supplied, nonempty, and unique")
    if not set(statuses) <= PARTITIONABLE_STATUSES:
        raise CheckpointError(
            "partition statuses may name only non-success queue statuses; invalid: "
            f"{sorted(set(statuses) - PARTITIONABLE_STATUSES)}")
    require_no_sidecars(database, "partition source database")
    with closing(open_ro(database)) as source:
        integrity_check(source, "partition source")
        weighted_modules = _status_rows_by_module(source, statuses)
        if not weighted_modules:
            raise CheckpointError(f"no modules have selected statuses: {list(statuses)}")
        assignments = deterministic_partition(weighted_modules, jobs)
        source_tables = {table: row_digest(source, table) for table in REQUIRED_TABLES}
        source_schema = database_schema_signature(source)
        source_digests = database_table_digests(source)
        selected_rows = sum(row_count for _, row_count, _ in weighted_modules)
    output_root.parent.mkdir(parents=True, exist_ok=True)
    output_root.mkdir()
    report: dict[str, Any] = {
        "schema": 1,
        "tool": "Experiment/t78_checkpoint_prepare.py",
        "sourceQueueTableDigests": source_tables,
        "selectedStatuses": list(statuses),
        "selectedModules": len(weighted_modules),
        "selectedRows": selected_rows,
        "jobs": [],
    }
    weights = {module: (count, size) for module, count, size in weighted_modules}
    for index, modules in enumerate(assignments):
        job_root = output_root / f"job-{index:03d}"
        job_root.mkdir()
        write_manifest(job_root / MANIFEST_NAME, modules)
        db_path = job_root / DB_NAME
        _sqlite_backup(database, db_path)
        with closing(open_ro(db_path)) as copied:
            if database_schema_signature(copied) != source_schema:
                raise CheckpointError(f"partition copy schema differs from source in {job_root}")
            if database_table_digests(copied) != source_digests:
                raise CheckpointError(f"partition copy data differs from source in {job_root}")
        report["jobs"].append({
            "job": f"job-{index:03d}",
            "modules": len(modules),
            "selectedRows": sum(weights[module][0] for module in modules),
            "sourceBytes": sum(weights[module][1] for module in modules),
            "manifestSha256": hashlib.sha256(
                "".join(f"{module}\n" for module in modules).encode("utf-8")
            ).hexdigest(),
        })
    report["outputRoot"] = output_root.name
    report["exactCoverage"] = True
    (output_root / PARTITION_REPORT_NAME).write_text(
        json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return report


def _csv_statuses(value: str) -> tuple[str, ...]:
    return tuple(part.strip() for part in value.split(",") if part.strip())


def _canonical_cli_argument(raw: str) -> Path:
    """Preserve and reject lexical aliases before argparse normalizes them."""
    path = Path(raw)
    if not path.is_absolute() or str(path) != raw:
        raise argparse.ArgumentTypeError("input paths must be absolute and lexically canonical")
    return path


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    checkpoint = subparsers.add_parser("checkpoint", help="validate and merge the eight stopped jobs")
    checkpoint.add_argument("--t76-database", type=_canonical_cli_argument, required=True)
    checkpoint.add_argument(
        "--input-receipt", type=_canonical_cli_argument, required=True,
        help="immutable SHA-256 receipt pinning every baseline, worker DB, and manifest")
    checkpoint.add_argument(
        "--input-receipt-sha256", required=True,
        help="expected SHA-256 of the preserved input receipt; checked before database access")
    checkpoint.add_argument("--pending-base", type=_canonical_cli_argument, required=True)
    checkpoint.add_argument("--pending-job", type=_canonical_cli_argument, action="append", required=True)
    checkpoint.add_argument("--zeta-base", type=_canonical_cli_argument, required=True)
    checkpoint.add_argument("--zeta-job", type=_canonical_cli_argument, action="append", required=True)
    checkpoint.add_argument("--zeta-expected-manifest", type=_canonical_cli_argument, required=True,
                             help="pre-run canonical union of exact named-zeta target modules")
    checkpoint.add_argument("--maxretry-base", type=_canonical_cli_argument, required=True)
    checkpoint.add_argument("--maxretry-job", type=_canonical_cli_argument, action="append", required=True)
    checkpoint.add_argument("--maxretry-statuses", required=True,
                             help="explicit comma-separated queue statuses defining the manifest union")
    checkpoint.add_argument("--repo-root", type=_canonical_cli_argument, default=ROOT,
                             help="Lean/Lake root used by current TSA parser validation")
    checkpoint.add_argument("--skip-success-reparse", action="store_true",
                             help="merge recorded successes without the Lean AST reparse audit")
    checkpoint.add_argument("--output-root", type=Path, required=True)

    partition = subparsers.add_parser("partition", help="make status-selected disjoint cloud job copies")
    partition.add_argument("--database", type=_canonical_cli_argument, required=True)
    partition.add_argument("--jobs", type=int, required=True, choices=range(1, 9))
    partition.add_argument("--statuses", required=True,
                           help="explicit comma-separated non-success statuses; no error-text selection")
    partition.add_argument("--output-root", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        if args.command == "checkpoint":
            report = create_checkpoint(
                input_receipt=args.input_receipt,
                expected_input_receipt_sha256=args.input_receipt_sha256,
                t76_database=args.t76_database,
                pending_base=args.pending_base,
                pending_jobs=args.pending_job,
                zeta_base=args.zeta_base,
                zeta_jobs=args.zeta_job,
                zeta_expected_manifest=args.zeta_expected_manifest,
                maxretry_base=args.maxretry_base,
                maxretry_jobs=args.maxretry_job,
                maxretry_statuses=_csv_statuses(args.maxretry_statuses),
                output_root=args.output_root,
                repo_root=args.repo_root,
                reparse_incoming_successes=not args.skip_success_reparse,
            )
        else:
            report = create_partitions(
                database=args.database,
                output_root=args.output_root,
                jobs=args.jobs,
                statuses=_csv_statuses(args.statuses),
            )
    except (OSError, sqlite3.Error, CheckpointError, ValueError) as error:
        print(f"T78 preparation failed: {error}", file=sys.stderr)
        return 2
    print(json.dumps(report.get("summary", report), ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
