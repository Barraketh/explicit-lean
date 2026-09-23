#!/usr/bin/env python3
"""Finalize stopped simp traces and stock-compile isolated module candidates.

This recovery harness consumes extracted Scaleway worker artifacts. It changes
only rows belonging to the supplied module manifest. By default it processes
unaudited ``record_failed`` rows; explicit ``--statuses`` retries selected
audited failures and archives their previous audit result. Traces and compile
diagnostics are preserved in auxiliary audit tables; ``sorry`` is used only in
ephemeral module copies to mask a verified theorem or lemma proof body.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import pathlib
import re
import shutil
import sqlite3
import sys
import tempfile
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
PRIVATE_ROOT = (ROOT / ".lake" / "private").resolve()
T76_JOB_ROOT = (PRIVATE_ROOT / "T76-isolated-trace-20260923" / "jobs").resolve()
T77_RUN_ROOT = (PRIVATE_ROOT / "T77-error-fix-20260923").resolve()
T77_SNAPSHOT_ROOT = (T77_RUN_ROOT / "snapshot").resolve()
sys.path.insert(0, str(ROOT / "Experiment"))
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))
sys.path.insert(0, str(ROOT / "test" / "SimpTrace"))

import replay_module as replay  # noqa: E402
import simp_replacement_worker as worker  # noqa: E402
import trace_identity as TI  # noqa: E402
import tactic_syntax_ast as TSA  # noqa: E402
from finalize_traces import finalize_paths  # noqa: E402


RAW_PATH_RE = re.compile(r'=>trace\s+"([^"\n]+)"')
RAW_NAME_RE = re.compile(r"^(?P<name>.+)_(?P<site>[0-9]+)(?:\.(?P<run>[0-9]+))?\.json$")
UNSOUND_REPLACEMENT_RE = re.compile(r"\b(?:sorry|admit)\b")
EMPTY_PATH_CLOSER_RE = re.compile(r"\bat\s+\[\s*\](?=\])")
RETRYABLE_STATUSES = frozenset({
    "record_failed", "render_failed", "compile_failed", "resource_failed",
})
AUDIT_SCHEMA = """
CREATE TABLE IF NOT EXISTS isolated_trace_audit (
  module_name TEXT NOT NULL,
  ordinal INTEGER NOT NULL,
  result_status TEXT NOT NULL,
  trace_state TEXT NOT NULL,
  compile_detail TEXT,
  updated_at TEXT NOT NULL,
  PRIMARY KEY(module_name, ordinal)
)
"""
AUDIT_HISTORY_SCHEMA = """
CREATE TABLE IF NOT EXISTS isolated_trace_audit_history (
  attempt_id INTEGER PRIMARY KEY AUTOINCREMENT,
  module_name TEXT NOT NULL,
  ordinal INTEGER NOT NULL,
  result_status TEXT NOT NULL,
  trace_state TEXT NOT NULL,
  compile_detail TEXT,
  updated_at TEXT NOT NULL
)
"""


class IsolatedError(RuntimeError):
    pass


def _read_manifest(path: pathlib.Path) -> list[str]:
    return worker.read_manifest(path)


def _writable_database(path: pathlib.Path) -> pathlib.Path:
    """Accept only a single-link worker copy in an explicit writable run root."""
    resolved = path.resolve(strict=True)
    if resolved.stat().st_nlink != 1:
        raise IsolatedError(f"database path must have exactly one hard link: {resolved}")
    try:
        resolved.relative_to(T77_SNAPSHOT_ROOT)
    except ValueError:
        pass
    else:
        raise IsolatedError(f"refusing to write frozen snapshot database: {resolved}")
    for allowed in (T76_JOB_ROOT, T77_RUN_ROOT):
        try:
            resolved.relative_to(allowed)
            return resolved
        except ValueError:
            continue
    raise IsolatedError(f"database is not an approved private writable copy: {resolved}")


def _load_rows(db: sqlite3.Connection, module: str) -> list[dict[str, Any]]:
    rows = db.execute(
        "SELECT r.ordinal,c.start_byte,c.end_byte,c.source_sha256,c.kind,c.source,c.body,"
        "r.status,r.replacement_text,r.error FROM simp_replacements r "
        "JOIN commands c USING(module_name,ordinal) WHERE r.module_name=? ORDER BY r.ordinal",
        (module,),
    ).fetchall()
    return [dict(zip(("ordinal", "start", "end", "sha", "kind", "command_source",
                      "body", "status", "replacement", "error"), row)) for row in rows]


def _select_target_rows(commands: list[dict[str, Any]], audited: set[int],
                        retry_statuses: set[str] | None = None) -> list[dict[str, Any]]:
    if retry_statuses is None:
        return [row for row in commands
                if row["status"] == "record_failed" and row["ordinal"] not in audited]
    # The manifest limits the module set. Non-record failures must also have
    # an isolated-trace audit row so old compile_failed rows from other stages
    # cannot be swept into an explicit retry by status alone.
    return [row for row in commands if row["status"] in retry_statuses and
            (row["status"] == "record_failed" or row["ordinal"] in audited)]


def _archive_prior_audit(db: sqlite3.Connection, module: str, ordinal: int) -> None:
    prior = db.execute(
        "SELECT result_status,trace_state,compile_detail,updated_at "
        "FROM isolated_trace_audit WHERE module_name=? AND ordinal=?",
        (module, ordinal),
    ).fetchone()
    if prior is not None:
        db.execute(
            "INSERT INTO isolated_trace_audit_history "
            "(module_name,ordinal,result_status,trace_state,compile_detail,updated_at) "
            "VALUES(?,?,?,?,?,?)",
            (module, ordinal, *prior),
        )


def _trace_root(raw_dir: pathlib.Path, name: str) -> str:
    roots: set[str] = set()
    for path in sorted(raw_dir.glob("*.json")):
        try:
            raw = json.loads(path.read_text(encoding="utf-8"))
            call = raw["call"]
            match = RAW_PATH_RE.search(call)
        except (OSError, UnicodeError, json.JSONDecodeError, KeyError, TypeError) as exc:
            raise IsolatedError(f"malformed raw trace {path.name}: {exc}") from exc
        if not match:
            raise IsolatedError(f"raw trace lacks a trace path: {path.name}")
        recorded = pathlib.PurePosixPath(match.group(1))
        actual_name = RAW_NAME_RE.fullmatch(path.name)
        recorded_name = RAW_NAME_RE.fullmatch(recorded.name)
        if (not actual_name or not recorded_name
                or actual_name.group("name") != name
                or recorded_name.group("name") != name
                or actual_name.group("site") != recorded_name.group("site")
                or recorded_name.group("run") is not None
                or recorded.parent.name != "raw"):
            raise IsolatedError(f"raw trace path/file identity mismatch: {path.name}")
        roots.add(str(recorded.parent))
    if len(roots) != 1:
        raise IsolatedError(f"raw trace directory has {len(roots)} embedded roots")
    return roots.pop()


def _manifest_sites(value: dict[str, Any], source: str) -> list[TI.Site]:
    sites = TI.find_sites(source)
    by_ordinal = {site.siteOrdinal: site for site in sites}
    chosen = value.get("sites")
    if not isinstance(chosen, list):
        raise IsolatedError("manifest sites must be an array")
    ordinals = [entry.get("siteOrdinal") for entry in chosen if isinstance(entry, dict)]
    if len(ordinals) != len(chosen) or ordinals != sorted(set(ordinals)):
        raise IsolatedError("manifest site ordinals are malformed")
    try:
        selected = [by_ordinal[int(ordinal)] for ordinal in ordinals]
    except (KeyError, TypeError, ValueError) as exc:
        raise IsolatedError("manifest refers to a missing source site") from exc
    module_path = value.get("modulePath")
    if not isinstance(module_path, str) or value != TI.manifest(module_path, source, selected):
        raise IsolatedError("trace manifest does not match the original source")
    TI.validate_source_args(value, source)
    return selected


def _read_bundle(trace_dir: pathlib.Path, source_path: pathlib.Path,
                 source: str, scratch: pathlib.Path) -> tuple[list[tuple[TI.Site, Any]], dict[int, list[dict]]]:
    stage = trace_dir / "stage"
    raw_dir = trace_dir / "raw"
    manifests = list(stage.glob("*.manifest.json"))
    if len(manifests) != 1:
        raise IsolatedError(f"expected one trace manifest in {stage}, found {len(manifests)}")
    manifest_path = manifests[0]
    name = manifest_path.name.removesuffix(".manifest.json")
    traced_path = stage / f"{name}.lean"
    value = json.loads(manifest_path.read_text(encoding="utf-8"))
    module_path = value.get("modulePath")
    if module_path != source_path.name and not str(source_path).endswith(str(module_path)):
        raise IsolatedError(f"trace source path mismatch: {module_path}")
    selected = _manifest_sites(value, source)
    remote_trace_root = _trace_root(raw_dir, name)
    # Verify the complete staged transform, then canonicalize the subset that
    # actually emitted records. Raw suffixes are keyed by global siteOrdinal.
    traced = traced_path.read_text(encoding="utf-8")
    TI.verify_transform(source, name, traced, selected, remote_trace_root)
    site_by_ordinal = {site.siteOrdinal: site for site in selected}
    emitted: set[int] = set()
    for raw_path in raw_dir.glob("*.json"):
        match = RAW_NAME_RE.fullmatch(raw_path.name)
        if not match or match.group("name") != name:
            raise IsolatedError(f"unrecognized raw trace output: {raw_path.name}")
        ordinal = int(match.group("site")) - 1
        if ordinal not in site_by_ordinal:
            raise IsolatedError(f"raw trace ordinal is not in manifest: {ordinal}")
        emitted.add(ordinal)
    if not emitted:
        raise IsolatedError("bundle contains no emitted raw trace records")
    subset_sites = [site_by_ordinal[ordinal] for ordinal in sorted(emitted)]
    subset_traced, _ = TI.transform_with_ledger(source, name, remote_trace_root, subset_sites)
    subset_root = scratch / "subset" / name
    subset_raw = subset_root / "raw"
    subset_stage = subset_root / "stage"
    subset_raw.mkdir(parents=True, exist_ok=True)
    subset_stage.mkdir(parents=True, exist_ok=True)
    subset_traced_path = subset_stage / f"{name}.lean"
    subset_manifest_path = subset_stage / f"{name}.manifest.json"
    subset_traced_path.write_text(subset_traced, encoding="utf-8")
    subset_manifest_path.write_text(
        json.dumps(TI.manifest(value["modulePath"], source, subset_sites),
                   ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8")
    for raw_path in raw_dir.glob("*.json"):
        match = RAW_NAME_RE.fullmatch(raw_path.name)
        if match and int(match.group("site")) - 1 in emitted:
            shutil.copyfile(raw_path, subset_raw / raw_path.name)
    finalized = scratch / "final" / name
    finalized.mkdir(parents=True, exist_ok=True)
    finalize_paths(subset_traced_path, subset_manifest_path, source_path,
                   subset_raw, finalized,
                   trace_root=remote_trace_root)
    records = [json.loads(path.read_text(encoding="utf-8"))
               for path in sorted(finalized.glob("*.json"))]
    identity, grouped = replay.validate_identity(module_path, source, subset_sites, records)
    if identity.get("identity") != "accepted":
        raise IsolatedError("trace identity rejected: " + json.dumps(identity, ensure_ascii=False))
    render_sites = worker.S.find_sites(source)
    by_span = {(s.start, s.end, s.text): s for s in render_sites}
    pairs = []
    for site in subset_sites:
        key = (site.startChar, site.endChar, site.callText)
        render_site = by_span.get(key)
        if render_site is None:
            raise IsolatedError(f"renderer source-site mismatch at ordinal {site.siteOrdinal}")
        pairs.append((site, render_site))
    return pairs, grouped


def _build_bundle_index(artifacts_root: pathlib.Path) -> dict[str, list[pathlib.Path]]:
    index: dict[str, list[pathlib.Path]] = {}
    for manifest in artifacts_root.rglob("*.manifest.json"):
        try:
            value = json.loads(manifest.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            raise IsolatedError(f"cannot parse trace manifest {manifest}: {exc}") from exc
        module_path = value.get("modulePath")
        if not isinstance(module_path, str) or not module_path.startswith("Mathlib/"):
            raise IsolatedError(f"invalid modulePath in trace manifest: {manifest}")
        index.setdefault(module_path, []).append(manifest.parent.parent)
    duplicates = [(module_path, bundles) for module_path, bundles in index.items()
                  if len(set(bundles)) != 1]
    if duplicates:
        module_path, bundles = duplicates[0]
        raise IsolatedError(f"multiple trace bundles for {module_path}: {bundles}")
    return {path: sorted(set(bundles)) for path, bundles in index.items()}


def _is_theorem_or_lemma(command: dict[str, Any]) -> bool:
    if command["kind"] == "lemma":
        return True
    text = worker.S.mask_attributes(
        worker.S.mask_comments_and_strings(command.get("command_source") or "")
    ).lstrip()
    text = re.sub(
        r"^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)+", "", text
    )
    return re.match(r"(?:theorem|lemma)\b", text) is not None


def _declaration_assignment_before_body(source: str, theorem_head_end: int,
                                        body_start: int) -> int | None:
    """Find the declaration's top-level ``:=`` immediately before the body.

    Command-parser body spans can start inside a named argument, for example
    at the final ``R`` in ``(R := R)``.  Treating any preceding ``:=`` as the
    theorem separator turns such a span into ``(R := by sorry`` and corrupts
    every later compile probe in the module. Require a top-level separator
    after the declaration head, with only whitespace/comments between it and
    the exact parser-provided body suffix. Scan the whole command too: a bad
    body span after a top-level ``let x := ...`` in the type could otherwise
    mistake that let assignment for the theorem separator. Any later
    top-level assignment makes the boundary ambiguous and is rejected.
    """
    if not (0 <= theorem_head_end <= body_start <= len(source)):
        return None
    masked = worker.S.mask_comments_and_strings(source)
    if len(masked) != len(source):
        return None
    openers: list[str] = []
    closing_to_opening = {")": "(", "]": "[", "}": "{", "⟩": "⟨"}
    assignments: list[int] = []
    index = theorem_head_end
    while index < len(masked):
        if masked[index] == "«":
            quoted_end = masked.find("»", index + 1)
            if quoted_end < 0:
                return None
            index = quoted_end + 1
            continue
        if not openers and masked.startswith(":=", index):
            assignments.append(index)
            index += 2
            continue
        char = masked[index]
        if char in "([{⟨":
            openers.append(char)
        elif char in ")]}⟩":
            if not openers or openers[-1] != closing_to_opening[char]:
                return None
            openers.pop()
        index += 1
    if openers or not assignments:
        return None
    preceding_assignments = [position for position in assignments
                              if position < body_start]
    if not preceding_assignments:
        return None
    assignment = preceding_assignments[-1]
    if any(position > assignment for position in assignments):
        return None
    if masked[assignment + 2:body_start].strip():
        return None
    return assignment


def _mask_body(source: str, command: dict[str, Any]) -> str | None:
    """Return a command with a theorem/lemma proof body replaced by sorry."""
    if not _is_theorem_or_lemma(command) or command["body"] is None:
        return None
    start, end = command["start"], command["end"]
    raw = source.encode("utf-8")
    segment = raw[start:end].decode("utf-8")
    body = command["body"]
    if not body or not segment.endswith(body):
        return None
    at = len(segment) - len(body)
    # Attribute arguments and named arguments can contain their own `:=`.
    # Only mask when the exact body suffix follows a top-level declaration
    # assignment; otherwise leave the source proof untouched in the scratch
    # candidate rather than risk changing theorem syntax.
    prefix = segment[:at]
    masked_prefix = worker.S.mask_attributes(worker.S.mask_comments_and_strings(prefix))
    head = re.search(r"\b(?:theorem|lemma)\b", masked_prefix)
    if head is None or _declaration_assignment_before_body(segment, head.end(), at) is None:
        return None
    return segment[:at] + "by sorry" + segment[at + len(body):]


def _space_explicit_rw_empty_path_closers(source: str) -> str:
    """Separate adjacent empty-path and argument-list closing brackets.

    The generated spelling ``at []]`` is tokenized by Lean as ``]]``.  A space
    is syntax-neutral and makes the empty path's close and the surrounding
    ``explicit_rw`` list close unambiguous.  Restrict edits to code inside an
    ``explicit_rw [...]`` list, ignoring comments and strings.
    """
    masked = worker.S.mask_comments_and_strings(source)
    edits: list[int] = []
    for match in re.finditer(r"\bexplicit_rw\b", masked):
        index = match.end()
        while index < len(masked) and masked[index].isspace():
            index += 1
        if index >= len(masked) or masked[index] != "[":
            continue
        list_start = index
        depth = 0
        list_end: int | None = None
        while index < len(masked):
            if masked[index] == "[":
                depth += 1
            elif masked[index] == "]":
                depth -= 1
                if depth == 0:
                    list_end = index
                    break
                if depth < 0:
                    break
            index += 1
        if list_end is None:
            continue
        for empty_path in EMPTY_PATH_CLOSER_RE.finditer(masked, list_start, list_end + 1):
            edits.append(empty_path.end())
    for offset in sorted(set(edits), reverse=True):
        source = source[:offset] + " " + source[offset:]
    return source


def _apply_edits(source: str, commands: list[dict[str, Any]],
                 replacements: dict[int, str], masks: dict[int, str]) -> str:
    raw = source.encode("utf-8")
    edits: list[tuple[int, int, bytes]] = []
    for command in commands:
        ordinal = command["ordinal"]
        value = masks.get(ordinal, replacements.get(ordinal))
        if value is not None:
            edits.append((command["start"], command["end"], value.encode("utf-8")))
    for start, end, value in sorted(edits, reverse=True):
        raw = raw[:start] + value + raw[end:]
    return worker.module_with_replacements(raw.decode("utf-8"), [], {})


def _check_persisted_replacement(replacement: str | None) -> None:
    """Reject scratch-only proof holes before a replacement reaches SQLite."""
    if replacement is not None and UNSOUND_REPLACEMENT_RE.search(replacement):
        raise IsolatedError("refusing to persist a replacement containing sorry/admit")


def _existing_success_replacements(commands: list[dict[str, Any]]) -> dict[int, str]:
    """Validate every stored success before it can enter a compile baseline."""
    existing: dict[int, str] = {}
    for row in commands:
        if row["status"] != "success":
            continue
        replacement = row["replacement"]
        if not isinstance(replacement, str) or not replacement.strip():
            raise IsolatedError(
                f"stored success has empty replacement text at ordinal {row['ordinal']}"
            )
        _check_persisted_replacement(replacement)
        existing[row["ordinal"]] = replacement
    return existing


def _compile(module_path: str, text: str, scratch: pathlib.Path, serial: int) -> tuple[bool, str]:
    okay, detail, _ = worker.compile_candidate(module_path, text, scratch, serial)
    return okay, detail


def _persist_term_elaboration_gate_refusal(
    db: sqlite3.Connection, module: str, commands: list[dict[str, Any]],
    target_rows: list[dict[str, Any]], detail: str,
) -> dict[str, Any]:
    """Record a source-identity-bound, fail-closed module-level refusal."""
    command_by_ordinal = {row["ordinal"]: row for row in commands}
    updated_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    db.execute(AUDIT_SCHEMA)
    db.execute(AUDIT_HISTORY_SCHEMA)
    db.execute("BEGIN IMMEDIATE")
    try:
        for row in target_rows:
            ordinal = row["ordinal"]
            _archive_prior_audit(db, module, ordinal)
            cur = db.execute(
                "UPDATE simp_replacements SET status='render_failed',replacement_text=NULL,error=? "
                "WHERE module_name=? AND ordinal=? AND status=?",
                (detail[:2000], module, ordinal, command_by_ordinal[ordinal]["status"]),
            )
            if cur.rowcount != 1:
                raise IsolatedError(f"row changed while gating {module}:{ordinal}")
            db.execute(
                "INSERT INTO isolated_trace_audit(module_name,ordinal,result_status,trace_state,compile_detail,updated_at) "
                "VALUES(?,?,?,?,?,?) ON CONFLICT(module_name,ordinal) DO UPDATE SET "
                "result_status=excluded.result_status,trace_state=excluded.trace_state,"
                "compile_detail=excluded.compile_detail,updated_at=excluded.updated_at",
                (module, ordinal, "render_failed", "term_elab_gate_refused", detail[:2000], updated_at),
            )
        db.commit()
    except Exception:
        db.rollback()
        raise
    return {"module": module, "status": "committed", "rows": len(target_rows),
            "counts": {"render_failed": len(target_rows)},
            "termElaborationGate": "refused"}


def process_module(db: sqlite3.Connection, module: str, artifacts_root: pathlib.Path,
                  scratch_root: pathlib.Path,
                  bundle_index: dict[str, list[pathlib.Path]] | None = None,
                  retry_statuses: set[str] | None = None) -> dict[str, Any]:
    path, source_bytes, source, db_commands = worker.module_rows(db, module)
    commands = _load_rows(db, module)
    has_audit = db.execute(
        "SELECT 1 FROM sqlite_master WHERE type='table' AND name='isolated_trace_audit'"
    ).fetchone() is not None
    audited_statuses: dict[int, str] = {}
    if has_audit:
        audited_statuses = {int(ordinal): str(status) for ordinal, status in db.execute(
            "SELECT ordinal,result_status FROM isolated_trace_audit WHERE module_name=?", (module,))}
    audited = set(audited_statuses)
    if retry_statuses is not None:
        inconsistent = [row["ordinal"] for row in commands
                        if row["status"] in retry_statuses and
                        row["ordinal"] in audited and
                        audited_statuses[row["ordinal"]] != row["status"]]
        if inconsistent:
            raise IsolatedError(
                f"retry status disagrees with audit for {module}: {sorted(inconsistent)[:8]}"
            )
    target_rows = _select_target_rows(commands, audited, retry_statuses)
    if not target_rows:
        return {"module": module, "status": "skipped", "rows": 0}
    existing = _existing_success_replacements(commands)
    mathlib_path = (ROOT / ".lake" / "packages" / "mathlib" / path).resolve()
    if not mathlib_path.is_file() or mathlib_path.read_bytes() != source_bytes:
        raise IsolatedError(f"pinned source does not match DB for {module}")
    # Authenticate and parse the source before any recorder trace is turned
    # into a generated term, candidate compilation is attempted, or result is
    # persisted as success.  Term syntax/elaboration extensions can dispatch
    # to arbitrary MetaM (including Meta.Simp) even without tactic syntax.
    module_name = "Mathlib." + pathlib.PurePosixPath(path).with_suffix("") \
        .as_posix().removeprefix("Mathlib/").replace("/", ".")
    source_hash = hashlib.sha256(source_bytes).hexdigest()
    try:
        extension_inventory = TSA.inspect_term_elaboration_boundary(
            module=module_name, source_path=mathlib_path,
            expected_source_sha256=source_hash,
            mathlib_root=ROOT / ".lake" / "packages" / "mathlib" / "Mathlib",
        )
    except (OSError, RuntimeError, ValueError) as error:
        return _persist_term_elaboration_gate_refusal(
            db, module, commands, target_rows,
            f"term-elaboration AST gate failed closed: {error}",
        )
    if extension_inventory["status"] != "ok":
        detail = "term-elaboration AST gate refused: " + json.dumps(
            extension_inventory["risks"], sort_keys=True)
        return _persist_term_elaboration_gate_refusal(
            db, module, commands, target_rows, detail,
        )
    _, trace_sites = worker.align_sites(source)
    command_by_ordinal = {row["ordinal"]: row for row in commands}
    candidate_ordinals = {row["ordinal"] for row in target_rows}
    site_owner: dict[int, int | None] = {}
    selected_owner: dict[int, int] = {}
    for site in trace_sites:
        if worker.TARGET.match(site.callText):
            owner = worker.command_for_site(source, db_commands, site)
            site_owner[site.siteOrdinal] = owner
            if owner in candidate_ordinals:
                selected_owner[site.siteOrdinal] = owner

    rendered: dict[int, str] = {}
    trace_state: dict[int, str] = {row["ordinal"]: "no_trace" for row in target_rows}
    failures: dict[int, tuple[str, str]] = {}
    all_pairs: dict[int, tuple[Any, Any]] = {}
    all_traces: dict[int, list[dict]] = {}
    if bundle_index is None:
        bundle_index = _build_bundle_index(artifacts_root)
    trace_dirs = bundle_index.get(path, [])
    module_scratch = pathlib.Path(tempfile.mkdtemp(
        prefix=module.replace(".", "_") + "-", dir=scratch_root
    ))
    for bundle_index, trace_dir in enumerate(trace_dirs):
        bundle_scratch = module_scratch / f"bundle-{bundle_index:04}"
        bundle_scratch.mkdir(parents=True, exist_ok=True)
        try:
            pairs, traces = _read_bundle(trace_dir, mathlib_path, source, bundle_scratch)
        except Exception as exc:
            # Preserve the exact failure as per-command diagnostic where this
            # bundle selected an affected source command.
            manifest = next(trace_dir.joinpath("stage").glob("*.manifest.json"), None)
            ords: set[int] = set()
            if manifest:
                try:
                    value = json.loads(manifest.read_text(encoding="utf-8"))
                    for item in value.get("sites", []):
                        ord = item.get("siteOrdinal")
                        if ord in selected_owner:
                            ords.add(selected_owner[ord])
                except Exception:
                    pass
            for ordinal in ords:
                failures[ordinal] = ("record_failed", f"trace authentication failed: {type(exc).__name__}: {exc}"[:2000])
                trace_state[ordinal] = "trace_authentication_failed"
            continue
        for site, render_site in pairs:
            owner = selected_owner.get(site.siteOrdinal)
            if owner is None:
                continue
            all_pairs[site.siteOrdinal] = (site, render_site)
            if site.siteOrdinal in traces:
                all_traces[site.siteOrdinal] = traces[site.siteOrdinal]
            trace_state[owner] = "trace_authenticated"

    by_command_sites: dict[int, list[tuple[Any, Any]]] = {}
    for site_ordinal, owner in selected_owner.items():
        if owner in candidate_ordinals:
            pair = all_pairs.get(site_ordinal)
            if pair is not None:
                by_command_sites.setdefault(owner, []).append(pair)
    for row in target_rows:
        ordinal = row["ordinal"]
        if ordinal in failures:
            continue
        owned = by_command_sites.get(ordinal, [])
        expected = [site for site in trace_sites
                    if site_owner.get(site.siteOrdinal) == ordinal and worker.TARGET.match(site.callText)]
        if not expected:
            failures[ordinal] = ("render_failed", "no simp trace sites in command")
            trace_state[ordinal] = "no_source_site"
            continue
        if len(owned) != len(expected):
            failures[ordinal] = ("record_failed", "one or more source-site traces were not emitted")
            continue
        rewritten, error = worker.render_command(source, row, owned, all_traces)
        if error or rewritten is None:
            failures[ordinal] = ("render_failed", (error or "renderer returned no command")[:2000])
            trace_state[ordinal] = "render_failed"
        else:
            rendered[ordinal] = _space_explicit_rw_empty_path_closers(rewritten)
            trace_state[ordinal] = "rendered"

    masks: dict[int, str] = {}
    for ordinal in failures:
        masked = _mask_body(source, command_by_ordinal[ordinal])
        if masked is not None:
            masks[ordinal] = masked

    candidate_text = _apply_edits(source, db_commands, {**existing, **rendered}, masks)
    scratch = module_scratch / "compile"
    okay, detail = _compile(path, candidate_text, scratch, 0)
    compile_status: dict[int, tuple[str, str | None]] = {}
    if okay:
        compile_status.update({ordinal: ("success", None) for ordinal in rendered})
    else:
        accepted = dict(existing)
        failing_masks = dict(masks)
        serial = 1
        for ordinal in sorted(rendered):
            trial = dict(accepted)
            trial[ordinal] = rendered[ordinal]
            trial_text = _apply_edits(source, db_commands, trial, failing_masks)
            probe_ok, probe_detail = _compile(path, trial_text, scratch, serial)
            serial += 1
            if probe_ok:
                accepted[ordinal] = rendered[ordinal]
                compile_status[ordinal] = ("success", None)
            elif "timed out" in probe_detail:
                compile_status[ordinal] = ("resource_failed", probe_detail[:2000])
            else:
                compile_status[ordinal] = (
                    "compile_failed", (probe_detail or detail or "isolated stock compile failed")[:2000])
                masked = _mask_body(source, command_by_ordinal[ordinal])
                if masked is not None:
                    failing_masks[ordinal] = masked
        # Verify the accepted batch after all known theorem failures are masked.
        final_text = _apply_edits(source, db_commands, accepted, failing_masks)
        final_ok, final_detail = _compile(path, final_text, scratch, serial)
        if not final_ok:
            # Do not revoke independently compiled successes: record the module
            # interaction only in the audit column for each attempted command.
            detail = (final_detail or detail)[:2000]

    successful_ordinals = {
        ordinal for ordinal, (status, _) in compile_status.items()
        if status == "success"
    }
    if successful_ordinals:
        successful_replacements = dict(existing)
        successful_replacements.update({
            ordinal: rendered[ordinal]
            for ordinal in successful_ordinals
        })
        candidate_text = _apply_edits(
            source, db_commands, successful_replacements, {})
        try:
            TSA.assert_success_commands_have_no_simp(
                module=module_name,
                original_source=source,
                candidate_source=candidate_text,
                expected_source_sha256=source_hash,
                command_rows=db_commands,
                success_ordinals=successful_ordinals,
                repo_root=ROOT,
            )
        except (OSError, RuntimeError, ValueError) as error:
            detail = "direct simp command postcondition failed closed: " + \
                f"{type(error).__name__}: {error}"
            for ordinal in successful_ordinals:
                compile_status[ordinal] = ("render_failed", detail[:2000])

    outcomes: dict[int, tuple[str, str | None, str, str | None]] = {}
    for ordinal in candidate_ordinals:
        if ordinal in failures:
            status, error = failures[ordinal]
            outcomes[ordinal] = (status, None, trace_state.get(ordinal, "missing"), error)
        elif ordinal in rendered:
            status, error = compile_status.get(ordinal, ("compile_failed", detail[:2000]))
            outcomes[ordinal] = (status, rendered[ordinal] if status == "success" else None,
                                 trace_state.get(ordinal, "rendered"), error)
        else:
            outcomes[ordinal] = ("record_failed", None, trace_state.get(ordinal, "missing"),
                                 "trace could not be rendered")

    updated_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    db.execute(AUDIT_SCHEMA)
    db.execute(AUDIT_HISTORY_SCHEMA)
    db.execute("BEGIN IMMEDIATE")
    try:
        for ordinal, (status, replacement, state, error) in outcomes.items():
            _check_persisted_replacement(replacement)
            _archive_prior_audit(db, module, ordinal)
            cur = db.execute(
                "UPDATE simp_replacements SET status=?,replacement_text=?,error=? "
                "WHERE module_name=? AND ordinal=? AND status=?",
                (status, replacement, error, module, ordinal,
                 command_by_ordinal[ordinal]["status"]),
            )
            if cur.rowcount != 1:
                raise IsolatedError(f"row changed while processing {module}:{ordinal}")
            db.execute(
                "INSERT INTO isolated_trace_audit(module_name,ordinal,result_status,trace_state,compile_detail,updated_at) "
                "VALUES(?,?,?,?,?,?) ON CONFLICT(module_name,ordinal) DO UPDATE SET "
                "result_status=excluded.result_status,trace_state=excluded.trace_state,"
                "compile_detail=excluded.compile_detail,updated_at=excluded.updated_at",
                (module, ordinal, status, state, error, updated_at),
            )
        db.commit()
    except Exception:
        db.rollback()
        raise
    counts: dict[str, int] = {}
    for status, _, _, _ in outcomes.values():
        counts[status] = counts.get(status, 0) + 1
    return {"module": module, "status": "committed", "rows": len(outcomes),
            "counts": counts, "bundles": len(trace_dirs)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=pathlib.Path)
    parser.add_argument("--manifest", required=True, type=pathlib.Path)
    parser.add_argument("--artifacts-root", required=True, type=pathlib.Path)
    parser.add_argument("--scratch", required=True, type=pathlib.Path)
    parser.add_argument("--limit", type=int)
    parser.add_argument(
        "--statuses", nargs="+", choices=sorted(RETRYABLE_STATUSES),
        help=("explicitly retry these manifest-owned statuses; non-record failures "
              "must already have an isolated-trace audit row"),
    )
    args = parser.parse_args(argv)
    if args.limit is not None and args.limit < 1:
        parser.error("--limit must be positive")
    retry_statuses = set(args.statuses) if args.statuses is not None else None
    try:
        modules = _read_manifest(args.manifest)
        if not modules:
            raise IsolatedError("manifest contains no modules")
        database = _writable_database(args.database)
        if args.limit is not None:
            modules = modules[:args.limit]
        args.scratch.mkdir(parents=True, exist_ok=True)
        if not args.artifacts_root.is_dir():
            raise IsolatedError(f"artifacts root not found: {args.artifacts_root}")
        bundle_index = _build_bundle_index(args.artifacts_root.resolve())
        print(f"indexed {sum(map(len, bundle_index.values()))} trace bundles across "
              f"{len(bundle_index)} modules", flush=True)
        db = sqlite3.connect(database)
        module_errors = 0
        try:
            db.execute("PRAGMA foreign_keys=ON")
            for index, module in enumerate(modules, 1):
                print(f"[{index}/{len(modules)}] {module}", flush=True)
                try:
                    result = process_module(db, module, args.artifacts_root.resolve(),
                                            args.scratch.resolve(), bundle_index,
                                            retry_statuses)
                    print(json.dumps(result, ensure_ascii=False), flush=True)
                except Exception as exc:
                    module_errors += 1
                    print(json.dumps({"module": module, "status": "module_error",
                                      "error": f"{type(exc).__name__}: {exc}"[:2000]},
                                     ensure_ascii=False), flush=True)
        finally:
            db.close()
        return 1 if module_errors else 0
    except (OSError, sqlite3.Error, IsolatedError, worker.WorkerError,
            ValueError, json.JSONDecodeError) as exc:
        print(f"FAIL {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
