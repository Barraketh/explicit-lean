#!/usr/bin/env python3
"""Retry only exact source sites for selected simp command rows.

The input database must be a writable copy of a T76 job snapshot. Frozen
snapshots and the original T65 databases are rejected. By default this retries
only audited record_failed rows; pending rows require explicit opt-in. An
unbounded module retry first records multiple missing source sites together
through the authenticated recorder, falling back to independent per-site runs
if the batch is incomplete or rejected. Each source-site result is committed as
one auxiliary SQLite row, so a failure at one site cannot erase another site's
trace. Fully traced commands are rendered together and stock-compiled against
a passing unchanged baseline; a failed batch is isolated command by command,
and only passing commands are persisted as replacements.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import pathlib
import re
import sqlite3
import sys
import tempfile
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
PRIVATE_ROOT = ROOT / ".lake" / "private"
SNAPSHOT_ROOT = (PRIVATE_ROOT / "T77-error-fix-20260923" / "snapshot").resolve()
RUN_ROOT = (PRIVATE_ROOT / "T77-error-fix-20260923").resolve()
sys.path.insert(0, str(ROOT / "Experiment"))
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))
sys.path.insert(0, str(ROOT / "test" / "SimpTrace"))

import isolated_trace_compile as isolated  # noqa: E402
import simp_replacement_worker as worker  # noqa: E402
import tactic_syntax_ast as TSA  # noqa: E402


PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")
RETRY_SCHEMA = """
CREATE TABLE IF NOT EXISTS isolated_trace_site_retry (
  module_name TEXT NOT NULL,
  ordinal INTEGER NOT NULL,
  site_ordinal INTEGER NOT NULL,
  source_sha256 TEXT NOT NULL,
  call_text TEXT NOT NULL,
  status TEXT NOT NULL,
  trace_json TEXT,
  error TEXT,
  updated_at TEXT NOT NULL,
  PRIMARY KEY(module_name, ordinal, site_ordinal, source_sha256)
)
"""
RETRY_HISTORY_SCHEMA = """
CREATE TABLE IF NOT EXISTS isolated_trace_site_retry_history (
  attempt_id INTEGER PRIMARY KEY AUTOINCREMENT,
  module_name TEXT NOT NULL,
  ordinal INTEGER NOT NULL,
  site_ordinal INTEGER NOT NULL,
  source_sha256 TEXT NOT NULL,
  call_text TEXT NOT NULL,
  status TEXT NOT NULL,
  trace_json TEXT,
  error TEXT,
  updated_at TEXT NOT NULL
)
"""
COMMAND_SCHEMA = """
CREATE TABLE IF NOT EXISTS isolated_trace_command_retry (
  module_name TEXT NOT NULL,
  ordinal INTEGER NOT NULL,
  source_sha256 TEXT NOT NULL,
  original_status TEXT NOT NULL,
  result_status TEXT NOT NULL,
  replacement_sha256 TEXT,
  render_error TEXT,
  compile_error TEXT,
  updated_at TEXT NOT NULL,
  PRIMARY KEY(module_name, ordinal, source_sha256)
)
"""


class RetryError(RuntimeError):
    """Input, identity, or recorder failure."""


def read_only_snapshot_guard(database: pathlib.Path) -> pathlib.Path:
    resolved = database.resolve(strict=True)
    try:
        resolved.relative_to(SNAPSHOT_ROOT)
    except ValueError:
        pass
    else:
        raise RetryError(f"refusing to write frozen snapshot database: {resolved}")
    try:
        relative = resolved.relative_to(RUN_ROOT)
    except ValueError:
        raise RetryError(f"database must be a private T77 writable copy: {resolved}")
    if not relative.parts or relative.parts[0] == "snapshot":
        raise RetryError(f"refusing to write frozen snapshot database: {resolved}")
    if resolved.stat().st_nlink != 1:
        raise RetryError(f"database path must have exactly one hard link: {resolved}")
    return resolved


def placeholder_token(text: str) -> bool:
    return PLACEHOLDER_RE.search(text) is not None


def missing_site_ordinals(expected: list[int], authenticated: set[int],
                          already_retried: set[int]) -> list[int]:
    if len(expected) != len(set(expected)) or expected != sorted(expected):
        raise RetryError("expected site ordinals must be unique and source ordered")
    if not authenticated <= set(expected) or not already_retried <= set(expected):
        raise RetryError("trace evidence contains a site outside this command")
    return [ordinal for ordinal in expected
            if ordinal not in authenticated and ordinal not in already_retried]


def parse_statuses(raw: str) -> tuple[str, ...]:
    statuses = tuple(dict.fromkeys(part.strip() for part in raw.split(",") if part.strip()))
    allowed = {"pending", "record_failed", "render_failed", "compile_failed"}
    if not statuses or set(statuses) - allowed:
        raise RetryError("--statuses accepts pending, record_failed, render_failed, and/or compile_failed")
    return statuses


def resolve_module_selection(manifest: set[str] | None,
                             requested: set[str]) -> set[str]:
    if manifest is None and not requested:
        raise RetryError("provide either --manifest or at least one exact --module")
    if manifest is not None and not manifest:
        raise RetryError("--manifest contains no modules")
    if manifest is not None and requested and not requested <= manifest:
        raise RetryError("--module selection contains modules outside --manifest")
    return requested if requested else (manifest if manifest is not None else set())


def partition_source_site_rows(
    target_rows: list[tuple[str, int, str, str | None]],
    by_command: dict[int, list[int]],
) -> tuple[list[tuple[str, int, str, str | None]],
           list[tuple[str, int, str, str | None]]]:
    """Treat only pending false-positive candidates as no-ops; fail closed otherwise."""
    with_sites: list[tuple[str, int, str, str | None]] = []
    no_sites: list[tuple[str, int, str, str | None]] = []
    for target in target_rows:
        _, ordinal, state, _ = target
        if by_command.get(ordinal):
            with_sites.append(target)
        elif state == "pending":
            no_sites.append(target)
        else:
            raise RetryError(f"{state} command has no detected simp source sites: {ordinal}")
    return with_sites, no_sites


def _candidate_rows(
    db: sqlite3.Connection,
    module: str | None,
    statuses: tuple[str, ...],
) -> list[tuple[str, int, str, str | None]]:
    """Return only explicitly selected row states, with failed rows still audit-gated."""
    branches: list[str] = []
    args: list[Any] = []
    if "record_failed" in statuses:
        branches.append(
            "SELECT r.module_name,r.ordinal,r.status,r.error "
            "FROM simp_replacements r JOIN isolated_trace_audit a USING(module_name,ordinal) "
            "WHERE r.status='record_failed' AND a.result_status='record_failed' "
            "AND a.trace_state IN ('no_trace','trace_authenticated','trace_authentication_failed')"
        )
        branches.append(
            "SELECT r.module_name,r.ordinal,r.status,r.error "
            "FROM simp_replacements r JOIN isolated_trace_command_retry cr "
            "USING(module_name,ordinal) JOIN modules m ON m.name=r.module_name "
            "AND cr.source_sha256=m.source_sha256 WHERE r.status='record_failed' "
            "AND cr.result_status='trace_failed'"
        )
    for status in ("render_failed", "compile_failed"):
        if status in statuses:
            authenticated_state = {
                "render_failed": "render_failed",
                "compile_failed": "rendered",
            }[status]
            branches.append(
                "SELECT r.module_name,r.ordinal,r.status,r.error "
                "FROM simp_replacements r JOIN isolated_trace_audit a "
                "USING(module_name,ordinal) "
                "WHERE r.status=? AND a.result_status=? AND a.trace_state=?"
            )
            args.extend((status, status, authenticated_state))
            branches.append(
                "SELECT r.module_name,r.ordinal,r.status,r.error "
                "FROM simp_replacements r JOIN isolated_trace_command_retry cr "
                "USING(module_name,ordinal) JOIN modules m ON m.name=r.module_name "
                "AND cr.source_sha256=m.source_sha256 "
                "WHERE r.status=? AND cr.result_status IN (?, 'baseline_failed')"
            )
            args.extend((status, status))
    if "pending" in statuses:
        branches.append(
            "SELECT r.module_name,r.ordinal,'pending',r.error FROM simp_replacements r "
            "WHERE r.status='pending'"
        )
    sql = " UNION ".join(branches)
    if module is not None:
        sql = f"SELECT * FROM ({sql}) WHERE module_name=?"
        args.append(module)
    sql += " ORDER BY module_name,ordinal"
    result: dict[tuple[str, int], tuple[str, int, str, str | None]] = {}
    for row in db.execute(sql, args):
        value = (str(row[0]), int(row[1]), str(row[2]), row[3])
        key = (value[0], value[1])
        if key not in result or value[2] in {"trace_failed", "render_failed", "compile_failed"}:
            result[key] = value
    return [result[key] for key in sorted(result)]


def _renderer_pairs(source: str, commands: list[dict[str, Any]]) -> tuple[list[tuple[Any, Any]], dict[int, int]]:
    renderer_sites, trace_sites = worker.align_sites(source)
    by_span = {(site.start, site.end, site.text): site for site in renderer_sites}
    pairs: list[tuple[Any, Any]] = []
    owner_by_site: dict[int, int] = {}
    for site in trace_sites:
        if not worker.TARGET.match(site.callText):
            continue
        if site.siteOrdinal in owner_by_site:
            raise RetryError(f"duplicate target source-site ordinal {site.siteOrdinal}")
        owner = worker.command_for_site(source, commands, site)
        if owner is None:
            raise RetryError(
                f"target source site has no command owner at ordinal {site.siteOrdinal}"
            )
        if (site.startChar, site.endChar, site.callText) not in by_span:
            raise RetryError(f"renderer identity missing for site {site.siteOrdinal}")
        pairs.append((site, by_span[(site.startChar, site.endChar, site.callText)]))
        owner_by_site[site.siteOrdinal] = owner
    return pairs, owner_by_site


def _authenticated_old_traces(
    bundle_index: dict[str, list[pathlib.Path]],
    module_path: str,
    source_path: pathlib.Path,
    source: str,
    scratch: pathlib.Path,
) -> tuple[dict[int, list[dict]], set[int], str | None]:
    bundles = bundle_index.get(module_path, [])
    if not bundles:
        return {}, set(), "no existing trace bundle"
    if len(bundles) != 1:
        return {}, set(), f"ambiguous existing trace bundle count: {len(bundles)}"
    try:
        pairs, traces = isolated._read_bundle(bundles[0], source_path, source, scratch)
        available = {site.siteOrdinal for site, _ in pairs if site.siteOrdinal in traces}
        return traces, available, None
    except Exception as exc:
        return {}, set(), f"existing bundle authentication failed: {type(exc).__name__}: {exc}"[:2000]


def _safe_detail(value: object, limit: int = 2000) -> str:
    text = " ".join(str(value).split())[:limit]
    # Error diagnostics are metadata too. Keep them useful without ever
    # persisting a Lean proof-hole token.
    return PLACEHOLDER_RE.sub("[filtered-token]", text)


def _persist_sites(db: sqlite3.Connection,
                   rows: list[tuple[Any, ...]]) -> None:
    """Archive and replace one or more site rows in one transaction.

    Refresh uses this for its complete selected-site shadow set.  No observer
    may see only a prefix of that set: an interruption rolls the whole intent
    back, while a commit durably excludes every selected stale bundle trace.
    """
    if not rows:
        return
    for values in rows:
        if len(values) != 9:
            raise RetryError("site retry row has the wrong arity")
        for value in values[4:8]:
            if value is not None and placeholder_token(str(value)):
                raise RetryError("refusing to persist a Lean proof-hole token")
    db.execute("BEGIN IMMEDIATE")
    try:
        for values in rows:
            prior = db.execute(
                "SELECT module_name,ordinal,site_ordinal,source_sha256,call_text,status,"
                "trace_json,error,updated_at FROM isolated_trace_site_retry "
                "WHERE module_name=? AND ordinal=? AND site_ordinal=? AND source_sha256=?",
                values[:4],
            ).fetchone()
            if prior is not None:
                db.execute(
                    "INSERT INTO isolated_trace_site_retry_history "
                    "(module_name,ordinal,site_ordinal,source_sha256,call_text,status,"
                    "trace_json,error,updated_at) VALUES(?,?,?,?,?,?,?,?,?)",
                    prior,
                )
            db.execute(
                "INSERT INTO isolated_trace_site_retry "
                "(module_name,ordinal,site_ordinal,source_sha256,call_text,status,trace_json,error,updated_at) "
                "VALUES(?,?,?,?,?,?,?,?,?) ON CONFLICT(module_name,ordinal,site_ordinal,source_sha256) "
                "DO UPDATE SET call_text=excluded.call_text,status=excluded.status,"
                "trace_json=excluded.trace_json,error=excluded.error,"
                "updated_at=excluded.updated_at",
                values,
            )
        db.commit()
    except Exception:
        db.rollback()
        raise


def _persist_site(db: sqlite3.Connection, values: tuple[Any, ...]) -> None:
    _persist_sites(db, [values])


def _load_retried_traces(
    db: sqlite3.Connection,
    module: str,
    source_hash: str,
    module_path: str,
    source: str,
    owner_by_site: dict[int, int],
    sites_by_ordinal: dict[int, Any],
) -> dict[int, list[dict]]:
    result: dict[int, list[dict]] = {}
    seen_sites: set[int] = set()
    for site_ordinal, command_ordinal, call_text, text in db.execute(
        "SELECT site_ordinal,ordinal,call_text,trace_json FROM isolated_trace_site_retry "
        "WHERE module_name=? AND source_sha256=? AND status='recorded' AND trace_json IS NOT NULL",
        (module, source_hash),
    ):
        site_ordinal = int(site_ordinal)
        if site_ordinal in seen_sites:
            raise RetryError(f"duplicate persisted retry site ordinal {site_ordinal}")
        seen_sites.add(site_ordinal)
        site = sites_by_ordinal.get(site_ordinal)
        if site is None:
            raise RetryError(f"persisted retry site is absent from current source: {site_ordinal}")
        if owner_by_site.get(site_ordinal) != int(command_ordinal):
            raise RetryError(f"persisted retry command owner mismatch at site {site_ordinal}")
        if call_text != site.callText:
            raise RetryError(f"persisted retry call text mismatch at site {site_ordinal}")
        if placeholder_token(str(text)):
            raise RetryError(f"persisted trace contains a sorry/admit token at site {site_ordinal}")
        value = json.loads(text)
        if not isinstance(value, list) or not value or any(not isinstance(item, dict) for item in value):
            raise RetryError(f"persisted retry trace has invalid record list at site {site_ordinal}")
        identity, grouped = worker.replay.validate_identity(
            module_path, source, [site], value)
        if identity.get("identity") != "accepted" or set(grouped) != {site_ordinal}:
            raise RetryError(
                f"persisted retry trace identity rejected at site {site_ordinal}: "
                + json.dumps(identity, ensure_ascii=False)[:1200]
            )
        result[site_ordinal] = grouped[site_ordinal]
    return result


def _load_retry_site_statuses(
    db: sqlite3.Connection,
    module: str,
    source_hash: str,
    owner_by_site: dict[int, int],
    sites_by_ordinal: dict[int, Any],
) -> dict[int, tuple[str, str | None]]:
    """Load exact-source retry markers, including durable stale-trace shadows."""
    result: dict[int, tuple[str, str | None]] = {}
    for site_ordinal, command_ordinal, call_text, status, trace_json, error in db.execute(
        "SELECT site_ordinal,ordinal,call_text,status,trace_json,error "
        "FROM isolated_trace_site_retry "
        "WHERE module_name=? AND source_sha256=?",
        (module, source_hash),
    ):
        if type(site_ordinal) is not int or type(command_ordinal) is not int:
            raise RetryError("persisted retry site key is not an integer source identity")
        site = sites_by_ordinal.get(site_ordinal)
        if site is None:
            raise RetryError(f"persisted retry site is absent from current source: {site_ordinal}")
        if owner_by_site.get(site_ordinal) != command_ordinal:
            raise RetryError(f"persisted retry command owner mismatch at site {site_ordinal}")
        if call_text != site.callText:
            raise RetryError(f"persisted retry call text mismatch at site {site_ordinal}")
        if status not in {"recorded", "record_failed"}:
            raise RetryError(f"unknown persisted retry status at site {site_ordinal}: {status}")
        if ((status == "recorded" and
             (not isinstance(trace_json, str) or not trace_json.strip()))
                or (status == "record_failed" and trace_json is not None)):
            raise RetryError(f"persisted retry status/trace mismatch at site {site_ordinal}")
        result[site_ordinal] = (str(status), str(error) if error is not None else None)
    return result


def _exact_site_keys(value: object, expected: set[int]) -> bool:
    return (isinstance(value, dict)
            and all(type(key) is int for key in value)
            and set(value) == expected)


def _existing_success_replacements(
    db: sqlite3.Connection,
    module: str,
) -> dict[int, str]:
    replacements: dict[int, str] = {}
    for ordinal, text in db.execute(
        "SELECT ordinal,replacement_text FROM simp_replacements "
        "WHERE module_name=? AND status='success'", (module,)
    ):
        if not isinstance(text, str) or not text.strip():
            raise RetryError(f"success row has blank replacement: {module}:{ordinal}")
        replacements[int(ordinal)] = text
    return replacements


def _persist_command_result(
    db: sqlite3.Connection,
    module: str,
    ordinal: int,
    source_hash: str,
    original_status: str,
    result_status: str,
    replacement: str | None,
    render_error: str | None,
    compile_error: str | None,
    *,
    proof_hole_audited: bool = False,
    original_source: str | None = None,
    candidate_source: str | None = None,
    command_rows: list[dict[str, Any]] | None = None,
    candidate_replacements: dict[int, str] | None = None,
) -> None:
    if result_status == "compiled_success" and (replacement is None or not replacement.strip()):
        raise RetryError("compiled_success requires a nonblank replacement")
    if result_status == "compiled_success" and not proof_hole_audited:
        raise RetryError("compiled_success requires an authenticated executable proof-hole AST audit")
    if result_status == "compiled_success":
        if (original_source is None or candidate_source is None or command_rows is None
                or candidate_replacements is None):
            raise RetryError("compiled_success requires an authenticated direct simp AST postcondition")
        try:
            TSA.assert_success_commands_have_no_simp(
                module=module,
                original_source=original_source,
                candidate_source=candidate_source,
                expected_source_sha256=source_hash,
                command_rows=command_rows,
                success_ordinals={ordinal},
                candidate_replacements=candidate_replacements,
                repo_root=ROOT,
            )
        except (OSError, RuntimeError, ValueError) as error:
            raise RetryError(
                "direct simp command postcondition failed closed: "
                f"{type(error).__name__}: {error}"
            ) from error
    db.execute("BEGIN IMMEDIATE")
    try:
        if result_status == "compiled_success":
            cursor = db.execute(
                "UPDATE simp_replacements SET status='success',replacement_text=?,error=NULL "
                "WHERE module_name=? AND ordinal=? AND status=?",
                (replacement, module, ordinal, original_status),
            )
            if cursor.rowcount != 1:
                raise RetryError(
                    f"command status changed before commit: {module}:{ordinal}:{original_status}"
                )
        elif result_status == "noop" and original_status == "pending":
            cursor = db.execute(
                "UPDATE simp_replacements SET status='noop',replacement_text=NULL,error=NULL "
                "WHERE module_name=? AND ordinal=? AND status='pending'",
                (module, ordinal),
            )
            if cursor.rowcount != 1:
                raise RetryError(f"pending command changed before noop commit: {module}:{ordinal}")
        elif result_status in {"compile_failed", "render_failed", "trace_failed"} and original_status in {
            "pending", "record_failed", "render_failed", "compile_failed"
        }:
            if result_status == "compile_failed":
                primary_status, details = "compile_failed", compile_error
            elif result_status == "render_failed":
                primary_status, details = "render_failed", render_error
            else:
                primary_status, details = "record_failed", render_error
            cursor = db.execute(
                "UPDATE simp_replacements SET status=?,replacement_text=NULL,error=? "
                "WHERE module_name=? AND ordinal=? AND status=?",
                (primary_status, _safe_detail(details or result_status), module, ordinal, original_status),
            )
            if cursor.rowcount != 1:
                raise RetryError(
                    f"command status changed before commit: {module}:{ordinal}:{original_status}"
                )
        elif result_status == "baseline_failed" and original_status == "record_failed":
            # The prior module-fanout error is not command evidence. Preserve
            # the status for explicit follow-up but clear that stale diagnosis.
            cursor = db.execute(
                "UPDATE simp_replacements SET error=NULL WHERE module_name=? "
                "AND ordinal=? AND status=?",
                (module, ordinal, original_status),
            )
            if cursor.rowcount != 1:
                raise RetryError(
                    f"command status changed before commit: {module}:{ordinal}:{original_status}"
                )
        replacement_hash = (hashlib.sha256(replacement.encode("utf-8")).hexdigest()
                            if replacement is not None else None)
        db.execute(
            "INSERT INTO isolated_trace_command_retry "
            "(module_name,ordinal,source_sha256,original_status,result_status,"
            "replacement_sha256,render_error,compile_error,updated_at) "
            "VALUES(?,?,?,?,?,?,?,?,?) ON CONFLICT(module_name,ordinal,source_sha256) "
            "DO UPDATE SET original_status=excluded.original_status,"
            "result_status=excluded.result_status,replacement_sha256=excluded.replacement_sha256,"
            "render_error=excluded.render_error,compile_error=excluded.compile_error,"
            "updated_at=excluded.updated_at",
            (module, ordinal, source_hash, original_status, result_status,
             replacement_hash, _safe_detail(render_error) if render_error else None,
             _safe_detail(compile_error) if compile_error else None,
             datetime.now(timezone.utc).isoformat(timespec="seconds")),
        )
        db.commit()
    except Exception:
        db.rollback()
        raise


def _render_command(
    source: str,
    row: dict[str, Any],
    site_pairs: list[tuple[Any, Any]],
    traces: dict[int, list[dict]],
) -> tuple[str | None, str | None]:
    rendered, render_error = worker.render_command(source, row, site_pairs, traces)
    if rendered is None or render_error:
        return None, _safe_detail(render_error or "renderer returned no command")
    if not rendered.strip():
        return None, "renderer returned a blank command"
    return rendered, None


def _audit_executable_proof_holes(module: str, candidate: str) -> dict[str, Any]:
    """Parse candidate code for executable sorry/admit, ignoring comments/strings."""
    digest = hashlib.sha256(candidate.encode("utf-8")).hexdigest()
    try:
        inventory = TSA.audit_executable_proof_holes(
            module=module, source=candidate,
            expected_source_sha256=digest, repo_root=ROOT,
        )
    except (RuntimeError, ValueError) as error:
        raise RetryError(f"Lean executable proof-hole AST audit failed closed: {error}") from error
    return inventory


def process_module(
    db: sqlite3.Connection,
    module: str,
    target_rows: list[tuple[str, int, str, str | None]],
    bundle_index: dict[str, list[pathlib.Path]],
    scratch_root: pathlib.Path,
    *,
    retry_failed: bool,
    site_limit: int | None = None,
    refresh_recorded: bool = False,
) -> dict[str, Any]:
    module_path, source_bytes, source, commands = worker.module_rows(db, module)
    pinned_path = (ROOT / ".lake" / "packages" / "mathlib" / module_path).resolve()
    if not pinned_path.is_file() or pinned_path.read_bytes() != source_bytes:
        raise RetryError(f"pinned source mismatch for {module}")
    module_row = db.execute(
        "SELECT source_sha256 FROM modules WHERE name=?", (module,)
    ).fetchone()
    if module_row is None:
        raise RetryError(f"missing module row for {module}")
    source_hash = str(module_row[0])
    cmd_by_ord = {row["ordinal"]: row for row in commands}
    pairs, owner_by_site = _renderer_pairs(source, commands)
    pairs_by_site = {int(site.siteOrdinal): (site, render_site) for site, render_site in pairs}
    module_scratch = pathlib.Path(tempfile.mkdtemp(prefix=module.replace(".", "_") + "-", dir=scratch_root))
    old_traces, old_sites, old_error = _authenticated_old_traces(
        bundle_index, module_path, pinned_path, source, module_scratch / "old")
    old_traces = old_traces or {}
    trace_sites = worker.align_sites(source)[1]
    sites_by_ordinal = {int(site.siteOrdinal): site for site in trace_sites
                        if worker.TARGET.match(site.callText)}
    existing_retry = _load_retried_traces(
        db, module, source_hash, module_path, source,
        owner_by_site, sites_by_ordinal)
    persisted_site_statuses = _load_retry_site_statuses(
        db, module, source_hash, owner_by_site, sites_by_ordinal)
    shadowed_site_ids = {site for site, (status, _) in persisted_site_statuses.items()
                         if status == "record_failed"}
    selected_command_ordinals = {ordinal for _, ordinal, _, _ in target_rows}
    by_command: dict[int, list[int]] = {}
    for site_ordinal, command_ordinal in owner_by_site.items():
        if command_ordinal in selected_command_ordinals:
            by_command.setdefault(command_ordinal, []).append(site_ordinal)
    effective_target_rows, no_site_rows = partition_source_site_rows(target_rows, by_command)
    refresh_site_ids = ({site for _, ordinal, _, _ in effective_target_rows
                         for site in by_command.get(ordinal, [])}
                        if refresh_recorded else set())
    # Old bundle and retry-table traces remain immutable evidence, but selected
    # sites must be freshly recorded and must not participate in this attempt.
    combined_traces = {
        **{site: records for site, records in old_traces.items()
           if site not in refresh_site_ids and site not in shadowed_site_ids},
        **{site: records for site, records in existing_retry.items()
           if site not in refresh_site_ids and site not in shadowed_site_ids},
    }
    for _, ordinal, state, _ in no_site_rows:
        _persist_command_result(db, module, ordinal, source_hash, state,
                                "noop", None, None, None)
    if not effective_target_rows:
        return {"module": module, "status": "committed", "auditRows": len(target_rows),
                "targetSites": 0, "oldTraceSites": 0, "oldTraceError": None,
                "attempted": 0, "recorded": 0, "failed": 0, "skipped": 0,
                "deferred": 0, "noop": len(no_site_rows),
                "commandResults": {"noop": len(no_site_rows)}}
    # A source-local term syntax/elaboration hook can cause an apparently
    # ordinary generated term to run hidden Meta.Simp.  Refuse the entire
    # candidate module before recording, compiling, or persisting any
    # replacement; the authenticated Lean AST gate does not execute or strip
    # those declarations.
    try:
        extension_inventory = TSA.inspect_term_elaboration_boundary(
            module="Mathlib." + pathlib.PurePosixPath(module_path)
                .with_suffix("").as_posix().replace("/", ".").removeprefix("Mathlib."),
            source_path=pinned_path,
            expected_source_sha256=source_hash,
            mathlib_root=ROOT / ".lake" / "packages" / "mathlib" / "Mathlib",
        )
    except (OSError, RuntimeError, ValueError) as error:
        gate_error = "term-elaboration AST gate failed closed: " + str(error)
        for _, ordinal, state, _ in effective_target_rows:
            _persist_command_result(db, module, ordinal, source_hash, state,
                                    "render_failed", None, gate_error, None)
        return {"module": module, "status": "committed", "auditRows": len(target_rows),
                "targetSites": sum(len(by_command.get(ordinal, []))
                                   for _, ordinal, _, _ in effective_target_rows),
                "attempted": 0, "recorded": 0, "failed": 0, "skipped": 0,
                "deferred": 0, "noop": len(no_site_rows),
                "commandResults": {"noop": len(no_site_rows),
                                   "render_failed": len(effective_target_rows)},
                "termElaborationGate": "parse_failed_closed", "error": gate_error}
    if extension_inventory["status"] != "ok":
        gate_error = "term-elaboration AST gate refused source-local term extension: " + \
            json.dumps(extension_inventory["risks"], sort_keys=True)
        for _, ordinal, state, _ in effective_target_rows:
            _persist_command_result(db, module, ordinal, source_hash, state,
                                    "render_failed", None, gate_error, None)
        return {"module": module, "status": "committed", "auditRows": len(target_rows),
                "targetSites": sum(len(by_command.get(ordinal, []))
                                   for _, ordinal, _, _ in effective_target_rows),
                "attempted": 0, "recorded": 0, "failed": 0, "skipped": 0,
                "deferred": 0, "noop": len(no_site_rows),
                "commandResults": {"noop": len(no_site_rows),
                                   "render_failed": len(effective_target_rows)},
                "termElaborationGate": "refused", "risks": extension_inventory["risks"]}
    attempted = recorded = failed = skipped = 0
    pending_sites: list[tuple[int, int]] = []
    missing_before_limit = 0
    for _, ordinal, state, _old_error in effective_target_rows:
        row = cmd_by_ord.get(ordinal)
        if row is None:
            raise RetryError(f"audited command disappeared: {module}:{ordinal}")
        expected = sorted(by_command.get(ordinal, []))
        if not expected:
            raise RetryError(f"selected command lost its detected simp source sites: {module}:{ordinal}")
        retry_rows = db.execute(
            "SELECT site_ordinal,status FROM isolated_trace_site_retry "
            "WHERE module_name=? AND ordinal=? AND source_sha256=?",
            (module, ordinal, source_hash),
        ).fetchall()
        done = {int(site) for site, status in retry_rows
                if status == "recorded" or (status == "record_failed" and not retry_failed)}
        # Trust an old site trace only after the bundle has passed the full
        # source/manifest/raw authentication, regardless of the row-level T76
        # classification. A `no_trace` row may share a module bundle that does
        # contain a trace for this exact source site.
        trusted_for_command = (old_sites.intersection(expected)
                               if old_error is None else set())
        trusted_for_command -= shadowed_site_ids
        if refresh_recorded:
            trusted_for_command -= refresh_site_ids
        missing = missing_site_ordinals(expected, trusted_for_command, done)
        if refresh_recorded:
            missing = [site for site in expected if site in refresh_site_ids]
        skipped += len(expected) - len(missing)
        pending_sites.extend((ordinal, site_ordinal) for site_ordinal in missing)
        missing_before_limit += len(missing)
    all_candidate_pairs = set(pending_sites)
    if site_limit is not None:
        pending_sites = pending_sites[:site_limit]
    deferred = missing_before_limit - len(pending_sites)
    selected_pairs = set(pending_sites)
    deferred_site_ids = {site for _, site in all_candidate_pairs - selected_pairs}

    if refresh_recorded:
        # Persist a shadow before invoking the recorder. A crash or a site
        # limit must not let a later default retry silently reuse old bundle
        # evidence for any site explicitly selected for refresh.
        pending_ids = {site for _, site in pending_sites}
        now = datetime.now(timezone.utc).isoformat(timespec="seconds")
        shadow_rows: list[tuple[Any, ...]] = []
        for ordinal, site_ordinal in sorted(all_candidate_pairs):
            site = sites_by_ordinal.get(site_ordinal)
            if site is None or owner_by_site.get(site_ordinal) != ordinal:
                raise RetryError(f"refresh site/command identity mismatch: {module}:{ordinal}:{site_ordinal}")
            detail = ("recorded trace refresh pending" if site_ordinal in pending_ids
                      else "recorded trace refresh deferred by site limit")
            shadow_rows.append((module, ordinal, site_ordinal, source_hash,
                                site.callText, "record_failed", None, detail, now))
        _persist_sites(db, shadow_rows)
        for _, _, site_ordinal, *_ in shadow_rows:
            shadowed_site_ids.add(site_ordinal)
            combined_traces.pop(site_ordinal, None)

    selected_lookup = sites_by_ordinal
    selected_sites: list[Any] = []
    for ordinal, site_ordinal in pending_sites:
        site = selected_lookup.get(site_ordinal)
        if site is None or owner_by_site.get(site_ordinal) != ordinal:
            raise RetryError(f"site/command identity mismatch: {module}:{ordinal}:{site_ordinal}")
        if placeholder_token(site.callText):
            raise RetryError(f"refusing to persist placeholder token in source site {site_ordinal}")
        selected_sites.append(site)

    # record_sites authenticates invocation identity against its exact selected
    # source-site list. For an unbounded module retry, try that authenticated
    # batch once when multiple sites are missing. Any incomplete or malformed
    # batch is discarded wholesale and retried through the original one-site
    # path; partial recorder output is never persisted or salvaged.
    bulk_records: dict[int, list[dict]] | None = None
    if site_limit is None and len(pending_sites) > 1:
        requested_ordinals = [site_ordinal for _, site_ordinal in pending_sites]
        if len(requested_ordinals) != len(set(requested_ordinals)):
            raise RetryError("bulk recorder request contains duplicate source-site ordinals")
        try:
            bulk_dir = pathlib.Path(tempfile.mkdtemp(
                prefix=f"{module.replace('.', '_')}-sites-bulk-", dir=scratch_root))
            returned, _ = worker.record_sites(
                source, module_path, pinned_path, selected_sites, bulk_dir)
            if not _exact_site_keys(returned, set(requested_ordinals)):
                raise RetryError("bulk recorder returned missing or unexpected source sites")
            flattened: list[dict] = []
            for site_ordinal in requested_ordinals:
                records = returned[site_ordinal]
                if (not isinstance(records, list) or not records
                        or any(not isinstance(record, dict) for record in records)):
                    raise RetryError(
                        f"bulk recorder returned no valid invocation records for site {site_ordinal}")
                if placeholder_token(json.dumps(records, ensure_ascii=False)):
                    raise RetryError(
                        f"bulk recorder returned a sorry/admit token for site {site_ordinal}")
                flattened.extend(records)
            identity, authenticated = worker.replay.validate_identity(
                module_path, source, selected_sites, flattened)
            if (identity.get("identity") != "accepted"
                    or set(authenticated) != set(requested_ordinals)
                    or any(not authenticated[site] for site in requested_ordinals)):
                raise RetryError(
                    "bulk recorder trace identity rejected: "
                    + json.dumps(identity, ensure_ascii=False)[:1200])
            bulk_records = authenticated
        except Exception:
            # Fall back for every requested site. Never retain a valid-looking
            # subset from an unauthenticated or incomplete module batch.
            bulk_records = None

    def persist_recorded_site(ordinal: int, site: Any,
                              records: list[dict]) -> None:
        nonlocal attempted, recorded
        trace_json = json.dumps(records, ensure_ascii=False, sort_keys=True,
                                separators=(",", ":"))
        if placeholder_token(trace_json):
            raise RetryError("trace record contains a sorry/admit token")
        now = datetime.now(timezone.utc).isoformat(timespec="seconds")
        _persist_site(db, (module, ordinal, site.siteOrdinal, source_hash,
                           site.callText, "recorded", trace_json, None, now))
        attempted += 1
        recorded += 1
        combined_traces[site.siteOrdinal] = records

    if bulk_records is not None:
        for (ordinal, _site_ordinal), site in zip(pending_sites, selected_sites):
            persist_recorded_site(ordinal, site, bulk_records[site.siteOrdinal])
    else:
        for ordinal, site_ordinal in pending_sites:
            site = selected_lookup[site_ordinal]
            work_dir = pathlib.Path(tempfile.mkdtemp(
                prefix=f"{module.replace('.', '_')}-site-{site_ordinal:06}-", dir=scratch_root))
            status = "record_failed"
            trace_json = None
            error = None
            try:
                traces, _ = worker.record_sites(source, module_path, pinned_path, [site], work_dir)
                if not _exact_site_keys(traces, {site_ordinal}):
                    raise RetryError(
                        f"single-site recorder returned unexpected sites: "
                        f"{list(traces) if isinstance(traces, dict) else type(traces).__name__}"
                    )
                records = traces.get(site_ordinal)
                if (not isinstance(records, list) or not records
                        or any(not isinstance(record, dict) for record in records)):
                    raise RetryError("single-site recorder returned no invocation records")
                identity, authenticated = worker.replay.validate_identity(
                    module_path, source, [site], records)
                if (identity.get("identity") != "accepted"
                        or set(authenticated) != {site_ordinal}
                        or not authenticated[site_ordinal]):
                    raise RetryError(
                        "single-site recorder trace identity rejected: "
                        + json.dumps(identity, ensure_ascii=False)[:1200]
                    )
                records = authenticated[site_ordinal]
                trace_json = json.dumps(records, ensure_ascii=False, sort_keys=True,
                                        separators=(",", ":"))
                if placeholder_token(trace_json):
                    raise RetryError("trace record contains a sorry/admit token")
                status = "recorded"
                recorded += 1
                combined_traces[site_ordinal] = records
            except Exception as exc:
                trace_json = None
                error = _safe_detail(f"{type(exc).__name__}: {exc}")
                failed += 1
            attempted += 1
            now = datetime.now(timezone.utc).isoformat(timespec="seconds")
            _persist_site(db, (module, ordinal, site_ordinal, source_hash,
                               site.callText, status, trace_json, error, now))

    # First certify the unchanged module plus already-committed replacements.
    # Fully traced commands are all rendered before candidate compilation, so
    # the fast path can validate the exact module containing all of them.
    existing = _existing_success_replacements(db, module)
    baseline = worker.module_with_replacements(source, commands, existing)
    baseline_holes = _audit_executable_proof_holes(module, baseline)
    if baseline_holes["status"] == "ok":
        baseline_ok, baseline_error, _ = worker.compile_candidate(
            module_path, baseline, module_scratch, 0)
    else:
        baseline_ok = False
        baseline_error = "unchanged baseline contains executable sorry/admit syntax: " + \
            json.dumps(baseline_holes["proofHoles"], sort_keys=True)
    diagnostic_counts: dict[str, int] = {}
    rendered_candidates: list[tuple[int, str, str]] = []
    for _, ordinal, original_status, _old_error in effective_target_rows:
        expected = sorted(by_command.get(ordinal, []))
        if not expected:
            continue
        missing = [site for site in expected if site not in combined_traces]
        if missing and any(site in deferred_site_ids for site in missing):
            continue
        if missing:
            per_site = db.execute(
                "SELECT status,error FROM isolated_trace_site_retry WHERE module_name=? "
                "AND ordinal=? AND site_ordinal=? AND source_sha256=?",
                (module, ordinal, missing[0], source_hash),
            ).fetchone()
            result_status = "trace_failed"
            detail = (per_site[1] if per_site and per_site[1]
                      else "authenticated invocation trace unavailable for source site "
                           f"{missing[0]}")
            _persist_command_result(db, module, ordinal, source_hash, original_status,
                                    result_status, None, _safe_detail(detail), None)
            diagnostic_counts[result_status] = diagnostic_counts.get(result_status, 0) + 1
        elif not baseline_ok:
            result_status = "baseline_failed"
            _persist_command_result(db, module, ordinal, source_hash, original_status,
                                    result_status, None, None, baseline_error)
            diagnostic_counts[result_status] = diagnostic_counts.get(result_status, 0) + 1
        else:
            row = cmd_by_ord[ordinal]
            owned_pairs = [pairs_by_site[site] for site in expected]
            rendered, render_error = _render_command(
                source, row, owned_pairs, combined_traces)
            if rendered is None:
                result_status = "render_failed"
                _persist_command_result(db, module, ordinal, source_hash, original_status,
                                        result_status, None, render_error, None)
                diagnostic_counts[result_status] = diagnostic_counts.get(result_status, 0) + 1
            else:
                rendered_candidates.append((ordinal, original_status, rendered))

    if rendered_candidates:
        batch_replacements = {**existing,
                              **{ordinal: rendered
                                 for ordinal, _, rendered in rendered_candidates}}
        batch_candidate = worker.module_with_replacements(source, commands, batch_replacements)
        batch_holes = _audit_executable_proof_holes(module, batch_candidate)
        if batch_holes["status"] != "ok":
            # Attribute executable proof-hole syntax only after parser-based
            # isolation. Comments and strings never enter the AST inventory.
            # Affected commands become render_failed; clean siblings remain
            # eligible for the batch compile.
            clean_candidates: list[tuple[int, str, str]] = []
            for ordinal, original_status, rendered in rendered_candidates:
                isolated_candidate = worker.module_with_replacements(
                    source, commands, {**existing, ordinal: rendered})
                try:
                    isolated_holes = _audit_executable_proof_holes(module, isolated_candidate)
                except RetryError as error:
                    isolated_holes = {"status": "refused", "proofHoles": [],
                                      "auditError": str(error)}
                if isolated_holes["status"] == "ok":
                    clean_candidates.append((ordinal, original_status, rendered))
                else:
                    detail = "rendered command contains executable sorry/admit syntax: " + \
                        json.dumps(isolated_holes.get("proofHoles", []), sort_keys=True)
                    if isolated_holes.get("auditError"):
                        detail += "; " + isolated_holes["auditError"]
                    _persist_command_result(
                        db, module, ordinal, source_hash, original_status,
                        "render_failed", None, _safe_detail(detail), None)
                    diagnostic_counts["render_failed"] = diagnostic_counts.get("render_failed", 0) + 1
            rendered_candidates = clean_candidates
            if rendered_candidates:
                batch_replacements = {**existing,
                                      **{ordinal: rendered
                                         for ordinal, _, rendered in rendered_candidates}}
                batch_candidate = worker.module_with_replacements(
                    source, commands, batch_replacements)
                batch_holes = _audit_executable_proof_holes(module, batch_candidate)
                if batch_holes["status"] != "ok":
                    detail = "candidate module proof-hole audit remains ambiguous after isolation: " + \
                        json.dumps(batch_holes["proofHoles"], sort_keys=True)
                    for ordinal, original_status, _rendered in rendered_candidates:
                        _persist_command_result(
                            db, module, ordinal, source_hash, original_status,
                            "render_failed", None, _safe_detail(detail), None)
                        diagnostic_counts["render_failed"] = diagnostic_counts.get("render_failed", 0) + 1
                    rendered_candidates = []
        if rendered_candidates:
            # This exact AST audit covers every persisted candidate; the
            # compile result alone is not the proof-hole check.
            if batch_holes["status"] != "ok":
                raise RetryError("candidate reached compile without a clean executable proof-hole AST audit")
        else:
            batch_candidate = ""
    if rendered_candidates:
        batch_ok, batch_error, _ = worker.compile_candidate(
            module_path, batch_candidate, module_scratch, 1)
        if batch_ok:
            for ordinal, original_status, rendered in rendered_candidates:
                _persist_command_result(db, module, ordinal, source_hash, original_status,
                                        "compiled_success", rendered, None, None,
                                        proof_hole_audited=True,
                                        original_source=source,
                                        candidate_source=batch_candidate,
                                        command_rows=commands,
                                        candidate_replacements=batch_replacements)
                diagnostic_counts["compiled_success"] = diagnostic_counts.get(
                    "compiled_success", 0) + 1
        else:
            # The batch failure says nothing about any one command. Isolate
            # candidates sequentially from the passing unchanged baseline,
            # retaining only commands that compile with prior accepted ones.
            accepted = dict(existing)
            for serial, (ordinal, original_status, rendered) in enumerate(
                    rendered_candidates, 2):
                candidate_replacements = {**accepted, ordinal: rendered}
                candidate = worker.module_with_replacements(
                    source, commands, candidate_replacements)
                _audit_executable_proof_holes(module, candidate)
                okay, detail, _ = worker.compile_candidate(
                    module_path, candidate, module_scratch, serial)
                if okay:
                    _persist_command_result(db, module, ordinal, source_hash, original_status,
                                            "compiled_success", rendered, None, None,
                                            proof_hole_audited=True,
                                            original_source=source,
                                            candidate_source=candidate,
                                            command_rows=commands,
                                            candidate_replacements=candidate_replacements)
                    accepted[ordinal] = rendered
                    result_status = "compiled_success"
                else:
                    compile_error = _safe_detail(detail or batch_error)
                    _persist_command_result(db, module, ordinal, source_hash, original_status,
                                            "compile_failed", None, None, compile_error)
                    result_status = "compile_failed"
                diagnostic_counts[result_status] = diagnostic_counts.get(result_status, 0) + 1

    return {"module": module, "status": "committed", "auditRows": len(target_rows),
            "targetSites": sum(len(by_command.get(ordinal, []))
                               for _, ordinal, _, _ in target_rows),
            "oldTraceSites": len(old_sites), "oldTraceError": old_error,
            "attempted": attempted, "recorded": recorded, "failed": failed,
            "noop": len(no_site_rows),
            "skipped": skipped, "deferred": deferred,
            "commandResults": diagnostic_counts}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=pathlib.Path,
                        help="writable copy under the T77 private run root (never snapshot/)")
    parser.add_argument("--artifacts-root", required=True, type=pathlib.Path)
    parser.add_argument("--scratch", required=True, type=pathlib.Path)
    parser.add_argument("--module", action="append", help="limit to this exact module (repeatable)")
    parser.add_argument("--manifest", type=pathlib.Path,
                        help="restrict work to an exact worker module manifest")
    parser.add_argument("--statuses", default="record_failed",
                        help="comma-separated command states (default: record_failed; pending requires explicit opt-in)")
    parser.add_argument("--ordinal", action="append", type=int,
                        help="limit one --module to these audited command ordinals")
    parser.add_argument("--limit-sites", type=int,
                        help="bounded smoke: at most this many missing sites")
    parser.add_argument("--retry-failed", action="store_true",
                        help="retry prior per-site record_failed rows")
    parser.add_argument("--refresh-recorded", action="store_true",
                        help="freshly record every source site in selected commands, ignoring prior traces for this attempt")
    args = parser.parse_args(argv)
    if args.manifest is None and not args.module:
        parser.error("provide --manifest or at least one exact --module")
    module_pattern = re.compile(r"Mathlib(?:\.[A-Za-z0-9_']+)+\Z")
    if any(not module_pattern.fullmatch(module) for module in (args.module or [])):
        parser.error("--module requires exact fully-qualified Mathlib module names")
    try:
        statuses = parse_statuses(args.statuses)
    except RetryError as exc:
        parser.error(str(exc))
    if args.limit_sites is not None and args.limit_sites < 1:
        parser.error("--limit-sites must be positive")
    try:
        manifest_modules = set(worker.read_manifest(args.manifest)) if args.manifest else None
        selected_modules = resolve_module_selection(manifest_modules, set(args.module or []))
        database = read_only_snapshot_guard(args.database)
        if not args.artifacts_root.is_dir():
            raise RetryError(f"trace artifacts root not found: {args.artifacts_root}")
        args.scratch.mkdir(parents=True, exist_ok=True)
        bundle_index = isolated._build_bundle_index(args.artifacts_root.resolve())
        db = sqlite3.connect(database)
        try:
            db.execute("PRAGMA foreign_keys=ON")
            db.execute(RETRY_SCHEMA)
            db.execute(RETRY_HISTORY_SCHEMA)
            db.execute(COMMAND_SCHEMA)
            db.commit()
            selected_ordinals = set(args.ordinal or [])
            if selected_ordinals and len(selected_modules) != 1:
                raise RetryError("--ordinal requires a selection of exactly one module")
            rows = _candidate_rows(db, None, statuses)
            by_module: dict[str, list[tuple[str, int, str, str | None]]] = {}
            for row in rows:
                if (row[0] in selected_modules
                        and (not selected_ordinals or row[1] in selected_ordinals)):
                    by_module.setdefault(row[0], []).append(row)
            unknown = set(args.module or []) - set(by_module)
            if unknown:
                raise RetryError(f"requested modules have no audited missing-trace rows: {sorted(unknown)}")
            if selected_ordinals:
                selected_module = next(iter(selected_modules))
                present = {row[1] for row in by_module.get(selected_module, [])}
                missing_ordinals = selected_ordinals - present
                if missing_ordinals:
                    raise RetryError(f"requested ordinals are not audited missing-trace rows: {sorted(missing_ordinals)}")
            selected_rows = sum(len(module_rows) for module_rows in by_module.values())
            counts: dict[str, int] = {}
            for module_rows in by_module.values():
                for _, _, state, _ in module_rows:
                    counts[state] = counts.get(state, 0) + 1
            print(f"selected modules={len(by_module)} rows={selected_rows} states={counts}", flush=True)
            errors = 0
            site_budget = args.limit_sites
            for index, (module, module_rows) in enumerate(sorted(by_module.items()), 1):
                if site_budget is not None and site_budget <= 0:
                    break
                print(f"[{index}/{len(by_module)}] {module}", flush=True)
                try:
                    result = process_module(
                        db, module, module_rows, bundle_index,
                        args.scratch.resolve(), retry_failed=args.retry_failed,
                        site_limit=site_budget,
                        refresh_recorded=args.refresh_recorded)
                    print(json.dumps(result, ensure_ascii=False), flush=True)
                    if site_budget is not None:
                        site_budget -= result["attempted"]
                except Exception as exc:
                    errors += 1
                    print(json.dumps({"module": module, "status": "module_error",
                                      "error": _safe_detail(f"{type(exc).__name__}: {exc}")},
                                     ensure_ascii=False), flush=True)
            integrity = db.execute("PRAGMA integrity_check").fetchone()[0]
            if integrity != "ok":
                raise RetryError(f"writable retry database integrity check failed: {integrity}")
        finally:
            db.close()
        return 1 if errors else 0
    except (OSError, sqlite3.Error, RetryError, worker.WorkerError,
            ValueError, json.JSONDecodeError) as exc:
        print(f"FAIL {type(exc).__name__}: {_safe_detail(exc)}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
