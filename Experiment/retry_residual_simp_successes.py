#!/usr/bin/env python3
"""Retry a small explicit batch of successful rows with AST-confirmed direct simp.

The source is the terminal, validated T77 named-zeta merge. This command first
selects targets against that source database read-only, creates a new
single-link SQLite backup in its own run directory, repeats the authenticated
selection against the copy, and only then invokes fresh source-site recording
and isolated stock compilation. Parser refusals produce no targets.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import pathlib
import re
import sqlite3
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
RUN_ROOT = ROOT / ".lake" / "private" / "T77-residual-success-retry-20260923"
RUNS_ROOT = RUN_ROOT / "runs"
SOURCE_DATABASE = (
    ROOT / ".lake" / "private" / "T77-error-fix-20260923"
    / "named-zeta-retry-20260923" / "mathlib-db-named-zeta-merged.sqlite3"
)
SOURCE_DATABASE_SHA256 = "e2ee5cc13e5073e8f96c3c2a086e0f3c57aec556bd8e97d9c15ba623d2c54312"
MAX_MODULES = 8
MAX_COMMANDS = 32
RUN_ID_RE = re.compile(r"[0-9]{8}T[0-9]{6}Z-[0-9a-f]{8}\Z")
sys.path.insert(0, str(ROOT / "Experiment"))
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))

import retry_missing_traces as retry  # noqa: E402
import simp_replacement_worker as worker  # noqa: E402
import tactic_syntax_ast as TSA  # noqa: E402


class ResidualRetryError(RuntimeError):
    """Input identity, bounded selection, or copy lifecycle failure."""


def _sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _read_only_uri(path: pathlib.Path) -> str:
    return path.as_uri() + "?mode=ro"


def _run_directory(run_id: str) -> pathlib.Path:
    if not RUN_ID_RE.fullmatch(run_id):
        raise ResidualRetryError("run id must be UTC timestamp plus eight lowercase hex digits")
    return RUNS_ROOT / run_id


def _check_run_root(*, create: bool = False) -> None:
    expected_root = ROOT.resolve(strict=True) / ".lake" / "private" / \
        "T77-residual-success-retry-20260923"
    if RUN_ROOT != expected_root or RUNS_ROOT != expected_root / "runs":
        raise ResidualRetryError("private retry root is not the assigned exact path")
    for directory in (ROOT / ".lake", ROOT / ".lake" / "private", RUN_ROOT, RUNS_ROOT):
        if directory.is_symlink():
            raise ResidualRetryError(f"private retry directory cannot be a symlink: {directory}")
        if directory.exists():
            if not directory.is_dir() or directory.resolve(strict=True) != directory:
                raise ResidualRetryError(f"private retry directory is not canonical: {directory}")
        elif create:
            directory.mkdir()
        else:
            raise ResidualRetryError(f"private retry directory is missing: {directory}")


def _checked_integrity(db: sqlite3.Connection, label: str) -> None:
    result = db.execute("PRAGMA integrity_check").fetchall()
    if result != [("ok",)]:
        raise ResidualRetryError(f"{label} SQLite integrity_check failed: {result[:8]!r}")


def _validate_source_database() -> pathlib.Path:
    source = SOURCE_DATABASE
    expected = (ROOT / ".lake" / "private" / "T77-error-fix-20260923"
                / "named-zeta-retry-20260923" / "mathlib-db-named-zeta-merged.sqlite3")
    if source != expected or source.is_symlink() or not source.is_file():
        raise ResidualRetryError(f"validated T77 source database is missing or indirect: {source}")
    for ancestor in (ROOT / ".lake", ROOT / ".lake" / "private",
                     ROOT / ".lake" / "private" / "T77-error-fix-20260923",
                     source.parent):
        if ancestor.is_symlink() or not ancestor.is_dir() or ancestor.resolve() != ancestor:
            raise ResidualRetryError(f"validated T77 source directory is indirect: {ancestor}")
    if _sha256_file(source) != SOURCE_DATABASE_SHA256:
        raise ResidualRetryError("validated T77 source database SHA-256 changed")
    return source


def _create_database_copy(run_id: str) -> tuple[pathlib.Path, pathlib.Path]:
    """Create the sole accepted writable DB shape from the fixed read-only base."""
    source = _validate_source_database()
    run_dir = _run_directory(run_id)
    _check_run_root(create=True)
    if run_dir.exists() or run_dir.is_symlink():
        raise ResidualRetryError(f"retry run directory already exists: {run_dir}")
    RUNS_ROOT.mkdir(parents=True, exist_ok=True)
    run_dir.mkdir(exist_ok=False)
    database = run_dir / "mathlib-db-copy.sqlite3"
    temporary_database = run_dir / ".mathlib-db-copy.tmp.sqlite3"
    provenance = run_dir / "database-copy.json"
    temporary_provenance = run_dir / ".database-copy.tmp.json"
    try:
        source_db = sqlite3.connect(_read_only_uri(source), uri=True, timeout=30)
        target_db = sqlite3.connect(temporary_database, timeout=30)
        try:
            _checked_integrity(source_db, "source")
            source_db.backup(target_db)
            target_db.commit()
            _checked_integrity(target_db, "new copy")
        finally:
            target_db.close()
            source_db.close()
        if _sha256_file(source) != SOURCE_DATABASE_SHA256:
            raise ResidualRetryError("source database changed during read-only backup")
        copied_hash = _sha256_file(temporary_database)
        os.link(temporary_database, database)
        temporary_database.unlink()
        if database.stat().st_nlink != 1:
            raise ResidualRetryError("new database copy does not have exactly one hard link")
        receipt = {
            "schema": 1,
            "sourceDatabase": str(source),
            "sourceSha256": SOURCE_DATABASE_SHA256,
            "databaseSha256": copied_hash,
            "createdAt": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        }
        temporary_provenance.write_text(
            json.dumps(receipt, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
            encoding="utf-8",
        )
        os.link(temporary_provenance, provenance)
        temporary_provenance.unlink()
        return run_dir, database
    except Exception:
        temporary_database.unlink(missing_ok=True)
        temporary_provenance.unlink(missing_ok=True)
        database.unlink(missing_ok=True)
        provenance.unlink(missing_ok=True)
        try:
            run_dir.rmdir()
        except OSError:
            pass
        raise


def _validate_writable_copy(database: pathlib.Path, run_dir: pathlib.Path) -> pathlib.Path:
    _check_run_root()
    expected_path = _run_directory(run_dir.name)
    expected_dir = expected_path.resolve(strict=True)
    if (run_dir != expected_path or run_dir.is_symlink()
            or run_dir.resolve(strict=True) != expected_dir
            or not database.is_file() or database.is_symlink()):
        raise ResidualRetryError("writable database copy path is not the exact private run copy")
    resolved = database.resolve(strict=True)
    if (database != expected_path / "mathlib-db-copy.sqlite3"
            or resolved != expected_dir / "mathlib-db-copy.sqlite3"
            or resolved.stat().st_nlink != 1):
        raise ResidualRetryError("database must be the single-link copy created in this run")
    receipt_path = expected_dir / "database-copy.json"
    if receipt_path.is_symlink() or not receipt_path.is_file():
        raise ResidualRetryError("new database copy provenance path is indirect or missing")
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ResidualRetryError("new database copy has no valid provenance receipt") from error
    if (not isinstance(receipt, dict) or receipt.get("schema") != 1
            or receipt.get("sourceDatabase") != str(SOURCE_DATABASE)
            or receipt.get("sourceSha256") != SOURCE_DATABASE_SHA256
            or receipt.get("databaseSha256") != _sha256_file(resolved)):
        raise ResidualRetryError("new database copy provenance does not match its bytes")
    return resolved


def select_residual_successes(
    db: sqlite3.Connection,
    module: str,
    *,
    repo_root: pathlib.Path = ROOT,
) -> tuple[list[tuple[str, int, str, str | None]], dict[int, dict[str, Any]]]:
    """Select only successful replacements that Lean's AST owns direct simp nodes."""
    module_path, source_bytes, source, command_rows = worker.module_rows(db, module)
    expected_path = "Mathlib/" + module.removeprefix("Mathlib.").replace(".", "/") + ".lean"
    if module_path != expected_path:
        raise ResidualRetryError(f"database module path does not match module identity: {module}")
    pinned_path = (repo_root / ".lake" / "packages" / "mathlib" / module_path).resolve()
    if not pinned_path.is_file() or pinned_path.read_bytes() != source_bytes:
        raise ResidualRetryError(f"pinned source mismatch for {module}")
    module_row = db.execute(
        "SELECT source_sha256 FROM modules WHERE name=?", (module,)
    ).fetchone()
    if module_row is None:
        raise ResidualRetryError(f"module source digest is absent: {module}")
    source_hash = str(module_row[0])
    rows = worker.candidate_rows(db, module)
    success_rows = [row for row in rows if row["status"] == "success"]
    for row in success_rows:
        if (type(row["ordinal"]) is not int or row["ordinal"] < 0
                or not isinstance(row["replacement"], str)
                or not row["replacement"].strip()):
            raise ResidualRetryError(f"malformed successful replacement identity in {module}")
    replacements = {row["ordinal"]: row["replacement"] for row in success_rows}
    if not replacements:
        return [], {}

    candidate_source = worker.module_with_replacements(source, command_rows, replacements)
    candidate_hash = hashlib.sha256(candidate_source.encode("utf-8", errors="strict")).hexdigest()
    inventory = TSA.authenticated_candidate_simp_inventory(
        module=module,
        original_source=source,
        candidate_source=candidate_source,
        expected_source_sha256=source_hash,
        command_rows=command_rows,
        candidate_replacements=replacements,
        repo_root=repo_root,
    )
    if (inventory.get("status") != "ok"
            or inventory.get("moduleSourceSha256") != candidate_hash
            or not isinstance(inventory.get("commands"), list)
            or len(inventory["commands"]) != len(command_rows)):
        raise ResidualRetryError(f"candidate AST inventory identity is incomplete for {module}")

    target_rows: list[tuple[str, int, str, str | None]] = []
    evidence: dict[int, dict[str, Any]] = {}
    for row in success_rows:
        ordinal = row["ordinal"]
        if (type(ordinal) is not int or ordinal < 0 or ordinal >= len(inventory["commands"])
                or inventory["commands"][ordinal].get("commandOrdinal") != ordinal):
            raise ResidualRetryError(f"successful row has no exact AST command owner: {module}:{ordinal}")
        parsed_command = inventory["commands"][ordinal]
        sites = parsed_command.get("simpSites")
        if not isinstance(sites, list):
            raise ResidualRetryError(f"AST command has no direct simp-site array: {module}:{ordinal}")
        if not sites:
            continue
        normalized_sites = []
        for site in sites:
            if (not isinstance(site, dict)
                    or site.get("kind") != "Lean.Parser.Tactic.simp"):
                raise ResidualRetryError(f"AST success command has an unexpected node: {module}:{ordinal}")
            normalized_sites.append({
                key: site[key]
                for key in ("kind", "startByte", "endByte", "startChar", "endChar")
            })
        replacement = row["replacement"]
        evidence[ordinal] = {
            "ordinal": ordinal,
            "source_sha256": source_hash,
            "command_sha256": row["sha256"],
            "prior_replacement": replacement,
            "prior_replacement_sha256": hashlib.sha256(
                replacement.encode("utf-8", errors="strict")
            ).hexdigest(),
            "candidate_source_sha256": candidate_hash,
            "command_range": {
                key: parsed_command[key]
                for key in ("startByte", "endByte", "startChar", "endChar")
            },
            "simp_sites": normalized_sites,
        }
        target_rows.append((module, ordinal, "success", row["error"]))
    return target_rows, evidence


def _open_database(database: pathlib.Path, *, writable: bool) -> sqlite3.Connection:
    uri = database.as_uri() + ("?mode=rw" if writable else "?mode=ro")
    return sqlite3.connect(uri, uri=True, timeout=30)


def _module_selection(args: argparse.Namespace) -> list[str]:
    if args.manifest is not None:
        modules = worker.read_manifest(args.manifest)
        if args.module and not set(args.module) <= set(modules):
            raise ResidualRetryError("--module selection includes a module outside --manifest")
        selected = args.module or modules
    else:
        selected = args.module
    if not selected:
        raise ResidualRetryError("provide --manifest or at least one exact --module")
    if len(selected) > MAX_MODULES:
        raise ResidualRetryError(f"retry is capped at {MAX_MODULES} modules per invocation")
    if len(set(selected)) != len(selected):
        raise ResidualRetryError("module selection contains duplicates")
    module_pattern = re.compile(r"Mathlib(?:\.[A-Za-z0-9_']+)+\Z")
    if any(not module_pattern.fullmatch(module) for module in selected):
        raise ResidualRetryError("module selection requires exact Mathlib module names")
    return list(selected)


def _selection_for_modules(
    db: sqlite3.Connection,
    modules: list[str],
    *,
    repo_root: pathlib.Path = ROOT,
) -> tuple[dict[str, list[tuple[str, int, str, str | None]]],
           dict[str, dict[int, dict[str, Any]]]]:
    by_module: dict[str, list[tuple[str, int, str, str | None]]] = {}
    evidence_by_module: dict[str, dict[int, dict[str, Any]]] = {}
    for module in modules:
        rows, evidence = select_residual_successes(db, module, repo_root=repo_root)
        if rows:
            by_module[module] = rows
            evidence_by_module[module] = evidence
    count = sum(map(len, by_module.values()))
    if count > MAX_COMMANDS:
        raise ResidualRetryError(
            f"AST-selected residual success count {count} exceeds per-run cap {MAX_COMMANDS}"
        )
    return by_module, evidence_by_module


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", required=True,
                        help="new UTC id: YYYYMMDDTHHMMSSZ- plus eight lowercase hex digits")
    parser.add_argument("--module", action="append", default=[],
                        help="exact Mathlib module name; repeat for at most eight modules")
    parser.add_argument("--manifest", type=pathlib.Path,
                        help="optional exact module manifest, capped at eight modules")
    args = parser.parse_args(argv)
    try:
        run_dir = _run_directory(args.run_id)
        modules = _module_selection(args)
        source_path = _validate_source_database()
        source_db = _open_database(source_path, writable=False)
        try:
            _checked_integrity(source_db, "read-only source")
            selected, evidence = _selection_for_modules(source_db, modules)
        finally:
            source_db.close()
        if not selected:
            print(json.dumps({"status": "no_ast_confirmed_residual_successes",
                              "modulesExamined": len(modules), "databaseCopyCreated": False}))
            return 0

        run_dir, database = _create_database_copy(args.run_id)
        if run_dir != _run_directory(args.run_id):
            raise ResidualRetryError("created database copy is outside the requested run directory")
        database = _validate_writable_copy(database, run_dir)
        db = _open_database(database, writable=True)
        try:
            _checked_integrity(db, "new writable copy")
            copied_selection, copied_evidence = _selection_for_modules(db, modules)
            if copied_selection != selected or copied_evidence != evidence:
                raise ResidualRetryError("AST-selected success identities changed during database copy")
            db.execute(retry.RETRY_SCHEMA)
            db.execute(retry.RETRY_HISTORY_SCHEMA)
            db.execute(retry.COMMAND_SCHEMA)
            db.execute(retry.RESIDUAL_SUCCESS_HISTORY_SCHEMA)
            db.commit()
            scratch = run_dir / "scratch"
            scratch.mkdir(exist_ok=False)
            results = []
            for module in sorted(selected):
                result = retry.process_module(
                    db, module, selected[module], {}, scratch,
                    retry_failed=True,
                    refresh_recorded=True,
                    residual_success_evidence=copied_evidence[module],
                )
                results.append(result)
            _checked_integrity(db, "retried database copy")
        finally:
            db.close()
        print(json.dumps({"status": "retry_attempt_finished", "runDirectory": str(run_dir),
                          "databaseCopy": str(database), "selectedRows": sum(map(len, selected.values())),
                          "modules": results}, ensure_ascii=False, sort_keys=True))
        return 0
    except (OSError, sqlite3.Error, retry.RetryError, ResidualRetryError,
            worker.WorkerError, RuntimeError, ValueError, KeyError, TypeError,
            json.JSONDecodeError) as error:
        print(f"FAIL {type(error).__name__}: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
