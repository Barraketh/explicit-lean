#!/usr/bin/env python3
"""Retry failed simp replacement rows with exact term-free operations.

The input is a writable merged replacement database.  Failed rows are grouped
by Mathlib module, observed once per module with the operational recorder,
rendered as ``explicit_rw_v2``, and compiled as one module-level candidate.
Only rows selected from ``record_failed``, ``render_failed``, and
``compile_failed`` are updated.  Unsupported operations remain explicit
row-level residuals; no theorem/proof/pre/post expressions are serialized.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
import pathlib
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import time
from typing import Any, Callable

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Experiment"))
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))
sys.path.insert(0, str(ROOT / "test" / "SimpTrace"))

import render_simp_operations as operation_renderer  # noqa: E402
import replay_module as replay  # noqa: E402
import simp_replacement_worker as worker  # noqa: E402
import trace_identity as TI  # noqa: E402


FAILED_STATUSES = ("record_failed", "render_failed", "compile_failed")
FAILED_STATUS_SQL = ",".join("?" for _ in FAILED_STATUSES)
OPERATION_MARKER = "SIMP_OPERATIONS_SITE "
TIMEOUT_SECONDS = 30 * 60
RECORDER_IMPORT = "ExplicitLean.SimpOperations.Recording"
TERMINAL_STATUSES = frozenset({"success", *FAILED_STATUSES})


class RetryError(RuntimeError):
    """A selected row could not be safely attributed or retried."""


def select_failed_rows(db: sqlite3.Connection,
                       module: str | None = None) -> list[tuple[str, int, str, str | None]]:
    """Select every currently failed replacement row, without audit-table gates."""
    sql = (
        "SELECT module_name,ordinal,status,error FROM simp_replacements "
        f"WHERE status IN ({FAILED_STATUS_SQL})"
    )
    args: list[Any] = list(FAILED_STATUSES)
    if module is not None:
        sql += " AND module_name=?"
        args.append(module)
    sql += " ORDER BY module_name,ordinal"
    return [(str(name), int(ordinal), str(status), error)
            for name, ordinal, status, error in db.execute(sql, args)]


def _canonical_module_path(db: sqlite3.Connection, module: str) -> str:
    """Validate the DB path before reading the module's source or compiling it."""
    expected = module.replace(".", "/") + ".lean"
    path_parts = expected.split("/")
    if pathlib.PurePosixPath(expected).is_absolute() or any(
        part in {"", ".", ".."} for part in path_parts
    ):
        raise RetryError(
            f"invalid_canonical_module_path: module {module!r} maps to unsafe path {expected!r}"
        )
    row = db.execute("SELECT path FROM modules WHERE name=?", (module,)).fetchone()
    if row is None:
        raise RetryError(f"module_path_missing: no modules row for {module!r}")
    actual = str(row[0])
    if actual != expected:
        raise RetryError(
            f"canonical_module_path_mismatch: module {module!r} requires {expected!r}, "
            f"database has {actual!r}"
        )
    return expected


def _has_top_level_location(call_text: str) -> bool:
    """Return whether a direct simp call carries a trailing `at` location.

    The observer currently records the target expression only.  Rejecting a
    hypothesis location here avoids silently recording a different subject.
    Bracketed simp arguments/configuration and comments/strings are ignored.
    """
    masked = worker.S.mask_comments_and_strings(call_text)
    stack: list[str] = []
    closing = {")": "(", "]": "[", "}": "{", "⟩": "⟨"}
    for match in re.finditer(r"\bat\b", masked):
        index = match.start()
        before = masked[:index]
        stack.clear()
        cursor = 0
        while cursor < index:
            char = before[cursor]
            if char in "([{⟨":
                stack.append(char)
            elif char in closing:
                if stack and stack[-1] == closing[char]:
                    stack.pop()
            cursor += 1
        if not stack:
            previous = masked[index - 1] if index else " "
            following = masked[index + 2:index + 3]
            if previous.isspace() and (following.isspace() or following in {"*", "⊢"}):
                return True
    return False


def _source_site_owner_map(source: str, commands: list[dict[str, Any]]) -> tuple[
        list[tuple[TI.Site, worker.S.Site, int]], list[TI.Site]]:
    renderer_sites, trace_sites = worker.align_sites(source)
    renderer_by_span = {
        (site.start, site.end, site.text): site for site in renderer_sites
    }
    owned: list[tuple[TI.Site, worker.S.Site, int]] = []
    for trace_site in trace_sites:
        if not worker.TARGET.match(trace_site.callText):
            continue
        owner = worker.command_for_site(source, commands, trace_site)
        if owner is None:
            continue
        render_site = renderer_by_span.get((
            trace_site.startChar, trace_site.endChar, trace_site.callText
        ))
        if render_site is None:
            raise RetryError(
                f"renderer/recorder site identity mismatch at site {trace_site.siteOrdinal}"
            )
        owned.append((trace_site, render_site, owner))
    return owned, trace_sites


def _instrument_source(source: str, sites: list[TI.Site]) -> str:
    renderer_sites = worker.S.find_sites(source)
    by_span = {(site.start, site.end, site.text): site for site in renderer_sites}
    replacements: dict[int, list[str]] = {}
    for site in sites:
        if not site.callText.startswith("simp"):
            raise RetryError(f"unexpected non-simp site {site.siteOrdinal}")
        render_site = by_span.get((site.startChar, site.endChar, site.callText))
        if render_site is None:
            raise RetryError(f"instrumentation lost site identity {site.siteOrdinal}")
        observer = f"simp_operations_observe_at {site.siteOrdinal}" + site.callText[4:]
        # The observer restores the goal/meta state; the original tactic then
        # runs unchanged so this temporary module remains a stock-compiled
        # baseline. Parenthesized sequencing works in both standalone and
        # mid-line tactic positions recognized by the shared site scanner.
        replacements[render_site.index] = [f"({observer}; {site.callText})"]
    instrumented = worker.S.splice(source, replacements, renderer_sites)
    return worker.S.add_import(instrumented, module=RECORDER_IMPORT)


def _parse_observations(output: str, expected_sites: set[int]) -> dict[int, list[dict[str, Any]]]:
    found: dict[int, list[dict[str, Any]]] = defaultdict(list)
    for line in output.splitlines():
        stripped = line.strip()
        if not stripped.startswith(OPERATION_MARKER):
            continue
        payload = stripped[len(OPERATION_MARKER):].strip()
        site_text, separator, json_text = payload.partition(" ")
        if not separator or not site_text.isdecimal():
            raise RetryError("operational recorder emitted a malformed site label")
        site = int(site_text)
        if site not in expected_sites:
            raise RetryError(f"operational recorder emitted unrequested site label {site}")
        try:
            trace = json.loads(json_text)
        except json.JSONDecodeError as exc:
            raise RetryError(f"operational recorder emitted malformed trace for site {site}: {exc}") from exc
        if not isinstance(trace, dict) or not isinstance(trace.get("events"), list):
            raise RetryError(f"operational recorder emitted an invalid trace for site {site}")
        found[site].append(trace)
    return dict(found)


def record_operations(module_path: str, source: str, sites: list[TI.Site],
                      scratch: pathlib.Path, dylib: pathlib.Path,
                      ) -> dict[int, list[dict[str, Any]]]:
    """Run one module-level observer compile and return traces by source site."""
    traced = _instrument_source(source, sites)
    traced_path = scratch / "record" / module_path
    traced_path.parent.mkdir(parents=True, exist_ok=True)
    traced_path.write_text(traced, encoding="utf-8")
    command = ["lake", "env", "lean", f"--load-dynlib={dylib}", str(traced_path)]
    try:
        code, stdout, stderr, _ = replay.run(
            command, ROOT, timeout=TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise RetryError("recorder compile timed out after 1800 seconds") from exc
    if code:
        diagnostic = " ".join((stdout + stderr).split())[:1800]
        raise RetryError("recorder compile failed: " + (diagnostic or f"exit {code}"))
    return _parse_observations(stdout + "\n" + stderr,
                               {site.siteOrdinal for site in sites})


def _split_v2_source(rendered: str) -> tuple[list[str], str]:
    prefix = "explicit_rw_v2 "
    if not rendered.startswith(prefix):
        raise RetryError("operational renderer returned an unexpected source prefix")
    opening = rendered.find("[", len(prefix))
    if opening < 0:
        raise RetryError("operational renderer omitted its step list")
    depth = 0
    closing: int | None = None
    for index in range(opening, len(rendered)):
        if rendered[index] == "[":
            depth += 1
        elif rendered[index] == "]":
            depth -= 1
            if depth == 0:
                closing = index
                break
    if closing is None:
        raise RetryError("operational renderer returned an unterminated step list")
    steps_text = rendered[opening + 1:closing]
    steps = replay.split_steps(steps_text) if steps_text.strip() else []
    tail = rendered[closing + 1:]
    return steps, tail


def _render_lines(trace: dict[str, Any], indent: str) -> list[str]:
    rendered = operation_renderer.render_trace(trace)
    steps, tail = _split_v2_source(rendered)
    lines = worker.S.wrap_step_list(
        "explicit_rw_v2 [", steps, "]" + tail,
        indent, indent + "  ",
    )
    too_long = worker.S.overlong(lines)
    if too_long:
        raise operation_renderer.UnsupportedOperation(
            "explicit_rw_v2 operation exceeds readable line width: " + too_long[0]
        )
    return lines


def _replacement_lines(site: worker.S.Site, source_call: str,
                       rendered: list[str]) -> tuple[list[str], bool]:
    indent = site.line_indent or ""
    if site.alone_on_line:
        return worker.S.comment_original(source_call, indent) + [
            indent + line for line in rendered
        ], False
    # The first line is inserted immediately after the preceding tactic, so a
    # line comment safely terminates that line. Continuations and the v2 tactic
    # are indented as a child tactic sequence; the untouched source suffix is
    # appended by `splice` to the final operation line.
    comments = ["-- Original simp:"] + [
        indent + "  -- " + line for line in source_call.splitlines()
    ]
    body = [indent + "  " + line for line in rendered]
    return comments + body, True


def render_command(source: str, command: dict[str, Any],
                   sites: list[tuple[TI.Site, worker.S.Site]],
                   traces: dict[int, dict[str, Any]]) -> tuple[str | None, str | None]:
    command_start = worker.byte_to_char(source, command["start"])
    command_end = worker.byte_to_char(source, command["end"])
    command_text = source[command_start:command_end]
    replacements: dict[int, list[str]] = {}
    local_sites: list[worker.S.Site] = []
    multiline_midline: set[int] = set()
    for trace_site, original_site in sites:
        if not (command_start <= trace_site.startChar
                and trace_site.endChar <= command_end):
            continue
        trace = traces.get(trace_site.siteOrdinal)
        if trace is None:
            return None, f"no operational trace for source site {trace_site.siteOrdinal}"
        local_site = worker.local_site(
            original_site, source, command_start, len(local_sites)
        )
        try:
            rendered = _render_lines(trace, local_site.line_indent or "")
        except operation_renderer.UnsupportedOperation as exc:
            return None, f"site {trace_site.siteOrdinal}: unsupported operation: {exc}"
        lines, is_midline = _replacement_lines(
            local_site, trace_site.callText, rendered
        )
        replacements[local_site.index] = lines
        if is_midline:
            multiline_midline.add(local_site.index)
        local_sites.append(local_site)
    if not local_sites:
        return None, "no selected simp source sites belong to this command"
    try:
        return worker.S.splice(command_text, replacements, local_sites,
                               multiline_midline=multiline_midline), None
    except (ValueError, IndexError) as exc:
        return None, f"command splice failed: {type(exc).__name__}: {exc}"


def ensure_prerequisites() -> pathlib.Path:
    """Build the observer/replay modules and return their shared dynlib."""
    required = [
        ROOT / ".lake" / "build" / "lib" / "lean" / "ExplicitLean" /
        "SimpOperations" / "Recording.olean",
        ROOT / ".lake" / "build" / "lib" / "lean" / "ExplicitLean" /
        "ExplicitRw.olean",
    ]
    try:
        built = subprocess.run(
            ["lake", "build", "ExplicitLean:shared", "ExplicitLean.ExplicitRw"],
            cwd=ROOT, capture_output=True, text=True, timeout=TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise RetryError("building operational recorder/replay prerequisites timed out") from exc
    if built.returncode or not all(path.is_file() for path in required):
        detail = " ".join((built.stdout + built.stderr).split())[:1800]
        raise RetryError("building operational prerequisites failed: " + detail)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"],
        cwd=ROOT, capture_output=True, text=True, timeout=60,
    )
    if query.returncode:
        raise RetryError("could not resolve shared Lean library: " +
                         " ".join((query.stdout + query.stderr).split())[:1000])
    try:
        value = json.loads([line for line in query.stdout.splitlines() if line.strip()][-1])
    except (IndexError, json.JSONDecodeError) as exc:
        raise RetryError("`lake query` returned no shared library path") from exc
    library = pathlib.Path(value).resolve()
    if not library.is_file():
        raise RetryError(f"shared Lean library does not exist: {library}")
    return library


def _compile_candidate(module_path: str, text: str, scratch: pathlib.Path,
                       serial: int, dylib: pathlib.Path) -> tuple[bool, str, float]:
    target = scratch / "compile" / f"probe-{serial:05d}" / module_path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text, encoding="utf-8")
    started = time.monotonic()
    try:
        code, stdout, stderr, _ = replay.run(
            ["lake", "env", "lean", f"--load-dynlib={dylib}", str(target)],
            ROOT, timeout=TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        return False, "compile_timeout: Lean module compile timed out after 1800 seconds", time.monotonic() - started
    diagnostics = [match.group(0) for match in replay.DIAG_RE.finditer(stdout + stderr)
                   if match.group("sev") == "error"]
    detail = "\n".join(diagnostics[:8]) or " ".join((stdout + stderr).split())[:1800]
    return code == 0, detail or f"Lean exited with status {code}", time.monotonic() - started


def _selected_rows_for_module(db: sqlite3.Connection, module: str) -> list[dict[str, Any]]:
    return [
        {"ordinal": ordinal, "status": status, "error": error}
        for name, ordinal, status, error in select_failed_rows(db, module)
        if name == module
    ]


def _persist_results(db: sqlite3.Connection, module: str,
                     selected: list[dict[str, Any]],
                     outcomes: dict[int, tuple[str, str | None, str | None]]) -> None:
    if set(outcomes) != {row["ordinal"] for row in selected}:
        raise RetryError("module result set does not exactly match selected failed rows")
    db.execute("BEGIN IMMEDIATE")
    try:
        for row in selected:
            ordinal = row["ordinal"]
            status, replacement, error = outcomes[ordinal]
            if status not in TERMINAL_STATUSES:
                raise RetryError(f"invalid retry result status {status!r}")
            if status == "success":
                if not replacement or error is not None:
                    raise RetryError("success result must have replacement text and no error")
            elif replacement is not None or not error:
                raise RetryError("residual result must have an error and no replacement text")
            cursor = db.execute(
                "UPDATE simp_replacements SET status=?,replacement_text=?,error=? "
                "WHERE module_name=? AND ordinal=? AND status=?",
                (status, replacement, error, module, ordinal, row["status"]),
            )
            if cursor.rowcount != 1:
                raise RetryError(
                    f"selected DB row changed during retry: {module}:{ordinal}"
                )
        db.commit()
    except BaseException:
        db.rollback()
        raise


def _commit_module_residual(db: sqlite3.Connection, module: str,
                            selected: list[dict[str, Any]], detail: str,
                            started: float) -> dict[str, Any]:
    detail = detail[:1800]
    outcomes = {
        row["ordinal"]: ("record_failed", None, detail) for row in selected
    }
    _persist_results(db, module, selected, outcomes)
    return {
        "module": module,
        "status": "committed",
        "rows": len(outcomes),
        "counts": {"record_failed": len(outcomes)},
        "error": detail,
        "seconds": round(time.monotonic() - started, 2),
    }


def _process_module(db: sqlite3.Connection, module: str, scratch: pathlib.Path,
                    dylib: pathlib.Path, *, source_root: pathlib.Path | None = None,
                    recorder: Callable[..., dict[int, list[dict[str, Any]]]] | None = None,
                    compiler: Callable[..., tuple[bool, str, float]] | None = None,
                    ) -> dict[str, Any]:
    """Process one module using a caller-owned temporary workspace."""
    started = time.monotonic()
    selected = _selected_rows_for_module(db, module)
    if not selected:
        return {"module": module, "status": "skipped", "rows": 0}
    try:
        canonical_path = _canonical_module_path(db, module)
    except RetryError as exc:
        return _commit_module_residual(db, module, selected, str(exc), started)

    module_path, source_bytes, source, commands = worker.module_rows(db, module)
    if module_path != canonical_path:
        detail = (
            f"canonical_module_path_changed: validated {canonical_path!r}, "
            f"module reader returned {module_path!r}"
        )
        return _commit_module_residual(db, module, selected, detail, started)
    all_candidates = worker.candidate_rows(db, module)
    command_by_ordinal = {command["ordinal"]: command for command in commands}
    candidate_by_ordinal = {row["ordinal"]: row for row in all_candidates}
    if any(row["ordinal"] not in candidate_by_ordinal for row in selected):
        raise RetryError(f"selected replacement row missing from module read: {module}")
    for row in selected:
        current = candidate_by_ordinal[row["ordinal"]]
        if current["status"] != row["status"]:
            raise RetryError(f"selected replacement row changed during setup: {module}:{row['ordinal']}")

    source_root = (source_root or ROOT / ".lake" / "packages" / "mathlib").resolve()
    pinned_source = (source_root / module_path).resolve()
    if not pinned_source.is_file() or pinned_source.read_bytes() != source_bytes:
        raise RetryError(f"pinned Mathlib source differs from database for {module}: {pinned_source}")
    if OPERATION_MARKER in source:
        detail = (
            "reserved_operation_marker_collision: trusted pinned source already contains "
            f"{OPERATION_MARKER!r}; refusing to instrument it"
        )
        return _commit_module_residual(db, module, selected, detail, started)

    selected_by_ordinal = {row["ordinal"]: row for row in selected}
    command_sites: dict[int, list[tuple[TI.Site, worker.S.Site]]] = defaultdict(list)
    site_by_id: dict[int, TI.Site] = {}
    row_failures: dict[int, tuple[str, str]] = {}
    try:
        owned_sites, _ = _source_site_owner_map(source, commands)
    except Exception as exc:
        detail = f"source_site_alignment_failed: {type(exc).__name__}: {exc}"[:1800]
        outcomes = {row["ordinal"]: ("record_failed", None, detail) for row in selected}
        _persist_results(db, module, selected, outcomes)
        return {"module": module, "status": "committed", "rows": len(outcomes),
                "counts": {"record_failed": len(outcomes)}, "error": detail,
                "seconds": round(time.monotonic() - started, 2)}

    found: dict[int, list[TI.Site]] = {ordinal: [] for ordinal in selected_by_ordinal}
    for trace_site, render_site, owner in owned_sites:
        if owner not in selected_by_ordinal:
            continue
        command_sites[owner].append((trace_site, render_site))
        site_by_id[trace_site.siteOrdinal] = trace_site
        found[owner].append(trace_site)
    for row in selected:
        ordinal = row["ordinal"]
        if not found[ordinal]:
            row_failures[ordinal] = (
                "render_failed",
                f"no_simp_source_site: failed command row {ordinal} owns no direct `simp` tactic site",
            )

    # A nested direct simp would be evaluated once inside the outer observer
    # and again in the original source tactic. Do not guess invocation meaning.
    selected_sites = sorted(site_by_id.values(), key=lambda site: site.siteOrdinal)
    for left_index, outer in enumerate(selected_sites):
        for inner in selected_sites[left_index + 1:]:
            if outer.startChar <= inner.startChar and inner.endChar <= outer.endChar:
                for owner, sites in command_sites.items():
                    if any(site.siteOrdinal in {outer.siteOrdinal, inner.siteOrdinal}
                           for site, _ in sites):
                        row_failures[owner] = (
                            "record_failed",
                            f"nested_simp_site_not_replayed: source sites {outer.siteOrdinal} "
                            f"and {inner.siteOrdinal} require recursive invocation ownership",
                        )

    recordable: list[TI.Site] = []
    for site in selected_sites:
        owner = next((ordinal for ordinal, pairs in command_sites.items()
                      if any(pair[0].siteOrdinal == site.siteOrdinal for pair in pairs)), None)
        if owner is None or owner in row_failures:
            continue
        if _has_top_level_location(site.callText):
            row_failures[owner] = (
                "record_failed",
                f"hypothesis_location_not_observed: source site {site.siteOrdinal} has a trailing `at` location",
            )
            continue
        recordable.append(site)

    traces: dict[int, list[dict[str, Any]]] = {}
    if recordable:
        recorder = recorder or record_operations
        try:
            traces = recorder(module_path, source, recordable, scratch, dylib)
        except Exception as exc:
            detail = f"operation_record_failed: {type(exc).__name__}: {exc}"[:1800]
            for ordinal, pairs in command_sites.items():
                if any(site in recordable for site, _ in pairs) and ordinal not in row_failures:
                    row_failures[ordinal] = ("record_failed", detail)

    site_outcomes: dict[int, tuple[str, str | None]] = {}
    for site in recordable:
        observations = traces.get(site.siteOrdinal, [])
        owner = next((ordinal for ordinal, pairs in command_sites.items()
                      if any(pair[0].siteOrdinal == site.siteOrdinal for pair in pairs)), None)
        if owner is None or owner in row_failures:
            continue
        if len(observations) == 0:
            site_outcomes[site.siteOrdinal] = (
                "record_failed",
                f"observer_not_executed: source site {site.siteOrdinal} emitted no trace",
            )
            continue
        if len(observations) != 1:
            site_outcomes[site.siteOrdinal] = (
                "record_failed",
                f"repeated_tactic_invocation: source site {site.siteOrdinal} emitted "
                f"{len(observations)} traces; this source site needs recursive branch ownership",
            )
            continue
        try:
            rendered = operation_renderer.render_trace(observations[0])
            _render_lines(observations[0], "")
            site_outcomes[site.siteOrdinal] = ("success", rendered)
        except operation_renderer.UnsupportedOperation as exc:
            site_outcomes[site.siteOrdinal] = (
                "render_failed", f"unsupported_operation: {exc}"
            )

    candidate_replacements: dict[int, str] = {}
    for ordinal, pairs in command_sites.items():
        if ordinal in row_failures:
            continue
        failed_sites = [
            (site, site_outcomes.get(site.siteOrdinal)) for site, _ in pairs
            if site_outcomes.get(site.siteOrdinal, ("record_failed", None))[0] != "success"
        ]
        if failed_sites:
            # Keep the earliest trace/render boundary and name every concrete
            # residual in the row-level diagnostic.
            statuses = [outcome[0] for _, outcome in failed_sites if outcome is not None]
            status = "record_failed" if "record_failed" in statuses else "render_failed"
            details = [outcome[1] for _, outcome in failed_sites if outcome and outcome[1]]
            row_failures[ordinal] = (status, "; ".join(details)[:1800])
            continue
        command = command_by_ordinal.get(ordinal)
        if command is None:
            row_failures[ordinal] = (
                "record_failed", f"missing_command_row: {module}:{ordinal}"
            )
            continue
        rendered_traces = {
            site.siteOrdinal: traces[site.siteOrdinal][0]
            for site, _ in pairs
        }
        rewritten, error = render_command(source, command, pairs, rendered_traces)
        if error or rewritten is None:
            row_failures[ordinal] = (
                "render_failed", (error or "renderer produced no command")[:1800]
            )
        else:
            candidate_replacements[ordinal] = rewritten

    outcomes: dict[int, tuple[str, str | None, str | None]] = {
        ordinal: (status, None, detail)
        for ordinal, (status, detail) in row_failures.items()
    }
    if candidate_replacements:
        compiler = compiler or _compile_candidate
        existing_successes = {
            row["ordinal"]: row["replacement"]
            for row in all_candidates
            if row["status"] == "success" and row["replacement"] is not None
        }
        combined = dict(existing_successes)
        combined.update(candidate_replacements)
        combined_source = worker.module_with_replacements(source, commands, combined)
        okay, detail, seconds = compiler(module_path, combined_source, scratch, 0, dylib)
        if okay:
            for ordinal, replacement in candidate_replacements.items():
                outcomes[ordinal] = ("success", replacement, None)
        else:
            baseline_source = worker.module_with_replacements(
                source, commands, existing_successes
            )
            baseline_ok, baseline_detail, _ = compiler(
                module_path, baseline_source, scratch, 1, dylib
            )
            if not baseline_ok:
                diagnostic = (
                    "baseline_compile_failed: existing successful replacements do not "
                    "compile before this retry: " + (baseline_detail or detail)
                )[:1800]
                for ordinal in candidate_replacements:
                    outcomes[ordinal] = ("compile_failed", None, diagnostic)
            else:
                accepted = dict(existing_successes)
                serial = 2
                for ordinal, replacement in sorted(candidate_replacements.items()):
                    trial = dict(accepted)
                    trial[ordinal] = replacement
                    trial_source = worker.module_with_replacements(
                        source, commands, trial
                    )
                    probe_ok, probe_detail, _ = compiler(
                        module_path, trial_source, scratch, serial, dylib
                    )
                    serial += 1
                    if probe_ok:
                        accepted[ordinal] = replacement
                        outcomes[ordinal] = ("success", replacement, None)
                    else:
                        outcomes[ordinal] = (
                            "compile_failed", None,
                            ("compile_failed: " + probe_detail)[:1800],
                        )

    # Any selected row omitted by an earlier stage is an explicit driver
    # residual, never an implicit success or a silent pending result.
    for row in selected:
        ordinal = row["ordinal"]
        outcomes.setdefault(
            ordinal,
            ("record_failed", None,
             f"retry_incomplete: no operation result was produced for {module}:{ordinal}"),
        )
    _persist_results(db, module, selected, outcomes)
    counts: dict[str, int] = {}
    for status, _, _ in outcomes.values():
        counts[status] = counts.get(status, 0) + 1
    return {
        "module": module,
        "status": "committed",
        "rows": len(outcomes),
        "counts": counts,
        "recordedSites": len(recordable),
        "seconds": round(time.monotonic() - started, 2),
    }


def process_module(db: sqlite3.Connection, module: str, artifacts: pathlib.Path,
                   dylib: pathlib.Path, *, source_root: pathlib.Path | None = None,
                   recorder: Callable[..., dict[int, list[dict[str, Any]]]] | None = None,
                   compiler: Callable[..., tuple[bool, str, float]] | None = None,
                   ) -> dict[str, Any]:
    """Retry one module and remove all recording/probe source files afterward."""
    if not _selected_rows_for_module(db, module):
        return {"module": module, "status": "skipped", "rows": 0}
    scratch = pathlib.Path(tempfile.mkdtemp(
        prefix="explicit-rw-v2-retry-", dir=artifacts
    ))
    result: dict[str, Any] | None = None
    cleanup_error: str | None = None
    try:
        result = _process_module(
            db, module, scratch, dylib, source_root=source_root,
            recorder=recorder, compiler=compiler,
        )
    finally:
        try:
            shutil.rmtree(scratch)
        except OSError as exc:
            cleanup_error = f"{type(exc).__name__}: {exc}"
    if result is None:
        raise RetryError("module processing returned without a result")
    result["scratchCleaned"] = cleanup_error is None
    if cleanup_error is not None:
        result["scratchCleanupError"] = cleanup_error
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=pathlib.Path,
                        help="writable merged simp replacement SQLite database")
    parser.add_argument("--artifacts", type=pathlib.Path,
                        default=ROOT / ".lake" / "private" / "explicit-rw-v2-retry")
    parser.add_argument("--module", action="append", default=[],
                        help="optional exact module limit for a focused run")
    parser.add_argument("--source-root", type=pathlib.Path,
                        default=ROOT / ".lake" / "packages" / "mathlib",
                        help="pinned Mathlib source root (used for DB/source equality)")
    args = parser.parse_args(argv)
    try:
        args.database = args.database.resolve(strict=True)
        if not args.database.is_file():
            raise RetryError(f"database is not a file: {args.database}")
        args.artifacts.mkdir(parents=True, exist_ok=True)
        dylib = ensure_prerequisites()
        db = sqlite3.connect(args.database)
        db.execute("PRAGMA foreign_keys=ON")
        tables = {row[0] for row in db.execute(
            "SELECT name FROM sqlite_master WHERE type='table'"
        )}
        if not {"modules", "commands", "simp_replacements"} <= tables:
            raise RetryError("database lacks modules, commands, or simp_replacements")
        selected = select_failed_rows(db)
        modules = sorted({name for name, _, _, _ in selected})
        if args.module:
            unknown = sorted(set(args.module) - set(modules))
            if unknown:
                raise RetryError(f"requested modules have no selected failures: {unknown[:8]}")
            modules = sorted(set(args.module))
        report = {
            "database": str(args.database),
            "selectedStatuses": list(FAILED_STATUSES),
            "selectedRows": len([row for row in selected
                                 if row[0] in set(modules)]),
            "modules": [],
        }
        for module in modules:
            print(f"== {module}", flush=True)
            result = process_module(
                db, module, args.artifacts.resolve(), dylib,
                source_root=args.source_root,
            )
            report["modules"].append(result)
            print("   " + json.dumps(result, ensure_ascii=False), flush=True)
        report_path = args.artifacts / "retry-report.json"
        report_path.write_text(
            json.dumps(report, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        db.close()
        print(f"wrote {report_path}")
        return 0 if all(item["status"] in {"committed", "skipped"}
                        for item in report["modules"]) else 1
    except (OSError, sqlite3.Error, RetryError, ValueError, worker.WorkerError) as exc:
        print(f"FAIL {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
