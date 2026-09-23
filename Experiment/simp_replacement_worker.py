#!/usr/bin/env python3
"""Process queued simp replacement candidates for the modules in a manifest.

Each nonblank manifest line is one exact Mathlib module name. The worker uses
its own writable source-command database, records selected source calls with
the repository's SimpTrace recorder, renders them through ``explicit_rw``,
stock-compiles the candidate module, and commits one module's row updates in a
single SQLite transaction.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import pathlib
import re
import sqlite3
import subprocess
import sys
import tempfile
import time
from dataclasses import replace
from functools import lru_cache
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))
sys.path.insert(0, str(ROOT / "test" / "SimpTrace"))

import replay_module as replay  # noqa: E402
import sites as S  # noqa: E402
import trace_identity as TI  # noqa: E402

STATUSES = {
    "pending", "noop", "record_failed", "render_failed", "compile_failed",
    "success", "resource_failed", "worker_failed",
}
TARGET = re.compile(r"^simp(?:\s+only)?(?:\s|\[|$)")
TIMEOUT_SECONDS = 30 * 60


class WorkerError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def byte_to_char(source: str, byte_offset: int) -> int:
    raw = source.encode("utf-8")
    if not 0 <= byte_offset <= len(raw):
        raise WorkerError(f"byte offset outside module source: {byte_offset}")
    try:
        return len(raw[:byte_offset].decode("utf-8"))
    except UnicodeDecodeError as exc:
        raise WorkerError(f"byte offset splits UTF-8: {byte_offset}") from exc


def read_manifest(path: pathlib.Path) -> list[str]:
    modules: list[str] = []
    seen: set[str] = set()
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        if line != line.strip():
            raise WorkerError(f"manifest line {number} has surrounding whitespace")
        if not re.fullmatch(r"Mathlib(?:\.[A-Za-z0-9_']+)+", line):
            raise WorkerError(f"manifest line {number} is not an exact Mathlib module name: {line!r}")
        if line in seen:
            raise WorkerError(f"duplicate module in manifest: {line}")
        seen.add(line)
        modules.append(line)
    return modules


def module_rows(db: sqlite3.Connection, module: str) -> tuple[str, bytes, str, list[dict[str, Any]]]:
    row = db.execute(
        "SELECT path,source,source_sha256 FROM modules WHERE name = ?", (module,)
    ).fetchone()
    if row is None:
        raise WorkerError(f"module is missing from modules table: {module}")
    path, value, digest = row
    module_path = pathlib.PurePosixPath(path)
    if module_path.is_absolute() or ".." in module_path.parts or not path.startswith("Mathlib/"):
        raise WorkerError(f"unsafe/non-Mathlib source path for {module}: {path!r}")
    source_bytes = bytes(value)
    if sha256(source_bytes) != digest:
        raise WorkerError(f"database source hash mismatch for {module}")
    try:
        source = source_bytes.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise WorkerError(f"module source is not UTF-8 for {module}: {exc}") from exc
    commands = [
        {"ordinal": ordinal, "start": start, "end": end,
         "kind": kind, "sha256": command_hash}
        for ordinal, start, end, kind, command_hash in db.execute(
            "SELECT ordinal,start_byte,end_byte,kind,source_sha256 FROM commands "
            "WHERE module_name = ? ORDER BY ordinal", (module,)
        )
    ]
    raw = source_bytes
    for command in commands:
        start, end = command["start"], command["end"]
        if not (0 <= start < end <= len(raw)):
            raise WorkerError(f"invalid command range for {module}:{command['ordinal']}")
        if sha256(raw[start:end]) != command["sha256"]:
            raise WorkerError(f"command source hash mismatch for {module}:{command['ordinal']}")
        try:
            raw[start:end].decode("utf-8")
        except UnicodeDecodeError as exc:
            raise WorkerError(f"command range splits UTF-8 for {module}:{command['ordinal']}") from exc
    return path, source_bytes, source, commands


def candidate_rows(db: sqlite3.Connection, module: str) -> list[dict[str, Any]]:
    rows = db.execute(
        "SELECT r.ordinal,c.start_byte,c.end_byte,c.source_sha256,r.status,"
        "r.replacement_text,r.error FROM simp_replacements AS r "
        "LEFT JOIN commands AS c USING(module_name,ordinal) "
        "WHERE r.module_name = ? ORDER BY c.ordinal", (module,)
    ).fetchall()
    result = []
    for ordinal, start, end, digest, status, replacement_text, error in rows:
        if start is None or end is None or digest is None:
            raise WorkerError(f"replacement candidate has no matching command row: {module}:{ordinal}")
        if status not in STATUSES:
            raise WorkerError(f"unknown status {status!r} in {module}:{ordinal}")
        if status == "success" and not replacement_text:
            raise WorkerError(f"success row has no replacement text: {module}:{ordinal}")
        result.append({"ordinal": ordinal, "start": start, "end": end,
                       "sha256": digest, "status": status,
                       "replacement": replacement_text, "error": error})
    return result


def align_sites(source: str) -> tuple[list[S.Site], list[TI.Site]]:
    replay_sites = S.find_sites(source)
    trace_sites = TI.find_sites(source)
    trace_by_span = {(s.startChar, s.endChar, s.callText): s for s in trace_sites}
    if len(trace_by_span) != len(trace_sites):
        raise WorkerError("source-site detector produced duplicate trace identities")
    replay_by_span = {(s.start, s.end, s.text): s for s in replay_sites}
    if len(replay_by_span) != len(replay_sites):
        raise WorkerError("renderer source-site detector produced duplicate identities")
    targets = [site for site in trace_sites if TARGET.match(site.callText)]
    for trace_site in targets:
        key = (trace_site.startChar, trace_site.endChar, trace_site.callText)
        if key not in replay_by_span:
            raise WorkerError(
                "recorder and renderer source-site detectors disagree at "
                f"UTF-8 character range {trace_site.startChar}:{trace_site.endChar}"
            )
    for replay_site in replay_sites:
        if TARGET.match(replay_site.text):
            key = (replay_site.start, replay_site.end, replay_site.text)
            if key not in trace_by_span:
                raise WorkerError(
                    "renderer found a target call missing from recorder detector at "
                    f"character range {replay_site.start}:{replay_site.end}"
                )
    return replay_sites, trace_sites


def command_for_site(source: str, commands: list[dict[str, Any]], site: TI.Site) -> int | None:
    start = len(source[:site.startChar].encode("utf-8"))
    end = len(source[:site.endChar].encode("utf-8"))
    owners = [command for command in commands
              if command["start"] <= start and end <= command["end"]]
    if len(owners) > 1:
        raise WorkerError(f"source site maps to multiple commands at byte range {start}:{end}")
    if not owners:
        overlaps = [command for command in commands
                    if command["start"] < end and start < command["end"]]
        if overlaps:
            raise WorkerError(f"source site crosses command boundary at byte range {start}:{end}")
        return None
    return owners[0]["ordinal"]


def as_renderer_site(site: TI.Site, renderer_sites: list[S.Site]) -> S.Site:
    matches = [candidate for candidate in renderer_sites
               if (candidate.start, candidate.end, candidate.text) ==
               (site.startChar, site.endChar, site.callText)]
    if len(matches) != 1:
        raise WorkerError(f"source site did not map uniquely to renderer at ordinal {site.siteOrdinal}")
    return matches[0]


def instrument_selected(source: str, module_path: str, selected: list[TI.Site],
                        traced_name: str, raw_dir: pathlib.Path,
                        stage_dir: pathlib.Path) -> tuple[pathlib.Path, pathlib.Path]:
    traced_source, _ = TI.transform_with_ledger(source, traced_name, str(raw_dir), selected)
    manifest = TI.manifest(module_path, source, selected)
    staged = stage_dir / f"{traced_name}.lean"
    manifest_path = stage_dir / f"{traced_name}.manifest.json"
    staged.write_text(traced_source, encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, sort_keys=True,
                                       separators=(",", ":")) + "\n", encoding="utf-8")
    # Authenticate the generated source and edit ledger before Lean executes it.
    TI.verify_transform(source, traced_name, traced_source, selected, str(raw_dir))
    return staged, manifest_path


def record_sites(source: str, module_path: str, module_source_path: pathlib.Path,
                 selected: list[TI.Site], work_dir: pathlib.Path) -> tuple[dict[int, list[dict]], str]:
    run_root = work_dir / "trace"
    stage, raw, final = (run_root / "stage", run_root / "raw", run_root / "final")
    for directory in (stage, raw, final):
        directory.mkdir(parents=True, exist_ok=False)
    traced_name = "SimpWorker_" + hashlib.sha256(
        (module_path + "\0" + str(time.time_ns())).encode()
    ).hexdigest()[:20]
    traced, manifest = instrument_selected(source, module_path, selected,
                                           traced_name, raw, stage)
    env = os.environ.copy()
    env["SIMP_TRACE_OUT_ROOT"] = str(run_root)
    code, out, err, _ = replay.run(
        ["lake", "env", "lean", str(traced)], ROOT,
        timeout=TIMEOUT_SECONDS, env=env,
    )
    if code:
        raise WorkerError("recorder compile failed: " + " ".join((out + err).split())[:1000])
    finalize_script = ROOT / "test" / "SimpTrace" / "finalize_traces.py"
    code, out, err, _ = replay.run(
        [sys.executable, "-B", str(finalize_script),
         "--traced-source", str(traced), "--manifest", str(manifest),
         "--source", str(module_source_path), "--raw-dir", str(raw),
         "--out-dir", str(final)], ROOT, timeout=TIMEOUT_SECONDS,
    )
    if code:
        raise WorkerError("trace finalization failed: " + " ".join((out + err).split())[:1000])
    records: list[dict] = []
    for path in sorted(final.glob("*.json")):
        try:
            records.append(json.loads(path.read_text(encoding="utf-8")))
        except (OSError, json.JSONDecodeError, UnicodeDecodeError) as exc:
            raise WorkerError(f"malformed finalized trace {path.name}: {exc}") from exc
    identity, grouped = replay.validate_identity(module_path, source, selected, records)
    if identity["identity"] != "accepted":
        raise WorkerError("trace identity rejected: " + json.dumps(identity, ensure_ascii=False))
    return grouped, ""


def local_site(site: S.Site, source: str, command_start_char: int,
               local_index: int) -> S.Site:
    start = site.start - command_start_char
    end = site.end - command_start_char
    prefix = source[command_start_char:site.start]
    line = prefix.count("\n") + 1
    column = len(prefix.rsplit("\n", 1)[-1])
    line_indent = source[command_start_char:site.start]
    line_indent = line_indent.rsplit("\n", 1)[-1]
    line_indent = line_indent[:len(line_indent) - len(line_indent.lstrip(" \t"))]
    return replace(site, index=local_index, start=start, end=end, line=line, column=column,
                   line_indent=line_indent)


@lru_cache(maxsize=4)
def _cached_canonical_source_site_envelopes(
    source: str,
) -> dict[int, dict[str, Any]]:
    """Build and validate canonical T22 site envelopes from original source."""
    try:
        manifest = TI.manifest("", source, TI.find_sites(source))
        TI.validate_source_args(manifest, source)
    except (KeyError, TypeError, ValueError) as exc:
        raise WorkerError(f"canonical T22 sourceArgs validation failed: {exc}") from exc
    return {site["siteOrdinal"]: site for site in manifest["sites"]}


def _canonical_source_site_envelopes(source: str) -> dict[int, dict[str, Any]]:
    # Callers compare evidence against this mapping; do not expose the mutable
    # cached manifest itself to later code.
    return copy.deepcopy(_cached_canonical_source_site_envelopes(source))


def _rebase_trace_source_args(trace: dict | list[dict], command_start_char: int,
                              command_end_char: int, source: str,
                              canonical_site: dict[str, Any]) -> dict | list[dict]:
    """Copy invocation records and localize their authenticated source spans.

    T22 records sourceArgs offsets in Unicode scalars from the module start,
    while ``render_site`` receives this command's text. Preserve the trace
    evidence and every sourceArgs field except the two coordinates, and refuse
    malformed spans rather than allowing a slice outside this exact command.
    """
    if (not isinstance(command_start_char, int) or isinstance(command_start_char, bool)
            or not isinstance(command_end_char, int) or isinstance(command_end_char, bool)
            or command_start_char < 0 or command_end_char < command_start_char):
        raise WorkerError("invalid command character range for trace source spans")
    localized = copy.deepcopy(trace)
    if isinstance(localized, list):
        records = localized
    elif isinstance(localized, dict):
        executions = localized.get("_executions")
        records = executions if isinstance(executions, list) else [localized]
    else:
        raise WorkerError("trace invocation records are not an object or list")
    if not records:
        raise WorkerError("trace has no invocation records to localize")

    for invocation, record in enumerate(records):
        if not isinstance(record, dict):
            raise WorkerError(f"trace invocation {invocation} is not an object")
        site = record.get("site")
        if not isinstance(site, dict):
            raise WorkerError(f"trace invocation {invocation} has no source-site envelope")
        if site != canonical_site:
            raise WorkerError(
                f"trace invocation {invocation} site envelope disagrees with canonical T22 source"
            )
        try:
            TI.validate_source_args({"sites": [site]}, source)
        except (KeyError, TypeError, ValueError) as exc:
            raise WorkerError(
                f"trace invocation {invocation} sourceArgs disagree with canonical T22 source: {exc}"
            ) from exc
        source_args = site.get("sourceArgs")
        if not isinstance(source_args, list):
            raise WorkerError(f"trace invocation {invocation} has malformed sourceArgs")
        for arg_index, arg in enumerate(source_args):
            if not isinstance(arg, dict):
                raise WorkerError(
                    f"trace invocation {invocation} sourceArgs[{arg_index}] is not an object"
                )
            start, end = arg.get("startChar"), arg.get("endChar")
            if (not isinstance(start, int) or isinstance(start, bool)
                    or not isinstance(end, int) or isinstance(end, bool)
                    or not (command_start_char <= start < end <= command_end_char)):
                raise WorkerError(
                    f"trace invocation {invocation} sourceArgs[{arg_index}] has invalid or "
                    f"out-of-command span {start!r}:{end!r} for "
                    f"{command_start_char}:{command_end_char}"
                )
            arg["startChar"] = start - command_start_char
            arg["endChar"] = end - command_start_char
    return localized


def render_command(source: str, command: dict[str, Any],
                   site_pairs: list[tuple[TI.Site, S.Site]],
                   traces: dict[int, list[dict]]) -> tuple[str | None, str | None]:
    command_start = byte_to_char(source, command["start"])
    command_end = byte_to_char(source, command["end"])
    command_text = source[command_start:command_end]
    canonical_sites = _cached_canonical_source_site_envelopes(source)
    replacements: dict[int, list[str]] = {}
    local_sites: list[S.Site] = []
    for ti_site, s_site in site_pairs:
        if not (command_start <= ti_site.startChar and ti_site.endChar <= command_end):
            continue
        trace = traces.get(ti_site.siteOrdinal)
        if not trace:
            return None, f"missing invocation trace for source site {ti_site.siteOrdinal}"
        canonical_site = canonical_sites.get(ti_site.siteOrdinal)
        if canonical_site is None:
            return None, f"source site {ti_site.siteOrdinal} is absent from canonical T22 manifest"
        renderer_site = local_site(s_site, source, command_start, len(local_sites))
        try:
            local_trace = _rebase_trace_source_args(
                trace, command_start, command_end, source, canonical_site
            )
        except WorkerError as exc:
            return None, f"site {ti_site.siteOrdinal}: {exc}"
        if isinstance(local_trace, list) and len(local_trace) == 1:
            render_trace: dict | list[dict] = local_trace[0]
        else:
            render_trace = local_trace
        rendered = replay.render_site(renderer_site,
                                      render_trace,
                                      command_text,
                                      include_original_comment=False,
                                      use_manual_overrides=False)
        if rendered.get("status") != "rendered":
            return None, (f"site {ti_site.siteOrdinal}: {rendered.get('status')}: "
                          f"{rendered.get('detail', '')}")
        if any("--" in line and line.lstrip().startswith("--")
               for line in rendered.get("lines", [])):
            return None, f"renderer emitted an unexpected comment at site {ti_site.siteOrdinal}"
        replacements[renderer_site.index] = rendered["lines"]
        local_sites.append(renderer_site)
    if not local_sites:
        return None, None
    try:
        rewritten = S.splice(command_text, replacements, local_sites)
    except (ValueError, IndexError) as exc:
        return None, f"command splice failed: {type(exc).__name__}: {exc}"
    return rewritten, None


def module_with_replacements(source: str, commands: list[dict[str, Any]],
                             replacements: dict[int, str]) -> str:
    raw = source.encode("utf-8")
    edits: list[tuple[int, int, bytes]] = []
    for command in commands:
        replacement = replacements.get(command["ordinal"])
        if replacement is not None:
            edits.append((command["start"], command["end"], replacement.encode("utf-8")))
    for start, end, replacement in sorted(edits, reverse=True):
        raw = raw[:start] + replacement + raw[end:]
    try:
        translated = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise WorkerError(f"replacement produced invalid UTF-8: {exc}") from exc
    try:
        return S.add_import(translated)
    except ValueError:
        module_match = re.search(r"^module\s*$", translated, re.M)
        import_line = ("public import ExplicitLean.ExplicitRw" if module_match
                       else "import ExplicitLean.ExplicitRw")
        if module_match:
            at = module_match.end()
            return translated[:at] + "\n" + import_line + translated[at:]
        return import_line + "\n" + translated


def compile_candidate(module_path: str, text: str, scratch: pathlib.Path,
                      serial: int) -> tuple[bool, str, float]:
    target = scratch / "compile" / f"probe-{serial:05d}" / module_path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text, encoding="utf-8")
    started = time.monotonic()
    try:
        code, out, err, _ = replay.run(
            ["lake", "env", "lean", str(target)], ROOT,
            timeout=TIMEOUT_SECONDS,
        )
    except Exception as exc:
        if isinstance(exc, subprocess.TimeoutExpired):
            return False, "stock compile timed out after 1800 seconds", time.monotonic() - started
        raise
    diagnostics = [m.group(0) for m in replay.DIAG_RE.finditer(out + err)
                   if m.group("sev") == "error"]
    detail = "\n".join(diagnostics[:8]) or " ".join((out + err).split())[:1200]
    return code == 0, detail, time.monotonic() - started


def ensure_prerequisites() -> None:
    required = [
        ROOT / ".lake" / "build" / "lib" / "lean" / "ExplicitLean" /
        "SimpTrace.olean",
        ROOT / ".lake" / "build" / "lib" / "lean" / "ExplicitLean" /
        "ExplicitRw.olean",
    ]
    if all(path.is_file() for path in required):
        return
    try:
        completed = subprocess.run(
            ["lake", "build", "ExplicitLean.SimpTrace", "ExplicitLean.ExplicitRw"],
            cwd=ROOT, capture_output=True, text=True, timeout=TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise WorkerError("building recorder/renderer prerequisites timed out") from exc
    if completed.returncode != 0 or not all(path.is_file() for path in required):
        output = " ".join((completed.stdout + completed.stderr).split())[:2000]
        raise WorkerError("could not build recorder/renderer prerequisites: " + output)


def process_module(db: sqlite3.Connection, module: str, artifacts: pathlib.Path) -> dict[str, Any]:
    started = time.monotonic()
    results: dict[int, tuple[str, str | None, str | None]] = {}
    try:
        module_path, source_bytes, source, commands = module_rows(db, module)
        all_candidates = candidate_rows(db, module)
        pending = [row for row in all_candidates if row["status"] == "pending"]
        if not pending:
            return {"module": module, "status": "skipped_terminal", "rows": 0}
        command_by_ordinal = {command["ordinal"]: command for command in commands}
        for row in pending:
            command = command_by_ordinal.get(row["ordinal"])
            if command is None or (command["start"], command["end"], command["sha256"]) != (
                    row["start"], row["end"], row["sha256"]):
                raise WorkerError(f"candidate command identity mismatch: {module}:{row['ordinal']}")
        mathlib_source_path = (ROOT / ".lake" / "packages" / "mathlib" / module_path).resolve()
        if not mathlib_source_path.is_file():
            raise WorkerError(f"pinned Mathlib source missing: {mathlib_source_path}")
        if mathlib_source_path.read_bytes() != source_bytes:
            raise WorkerError(f"pinned Mathlib source differs from DB for {module}")

        renderer_sites, trace_sites = align_sites(source)
        pending_by_ordinal = {row["ordinal"]: row for row in pending}
        site_pairs: list[tuple[TI.Site, S.Site]] = []
        selected: list[TI.Site] = []
        found: dict[int, list[TI.Site]] = {ordinal: [] for ordinal in pending_by_ordinal}
        for trace_site in trace_sites:
            if not TARGET.match(trace_site.callText):
                continue
            owner = command_for_site(source, commands, trace_site)
            if owner in pending_by_ordinal:
                selected.append(trace_site)
                site_pairs.append((trace_site, as_renderer_site(trace_site, renderer_sites)))
                found[owner].append(trace_site)
        for ordinal, row in pending_by_ordinal.items():
            if not found[ordinal]:
                results[ordinal] = ("noop", None, None)

        existing_successes = {
            row["ordinal"]: row["replacement"]
            for row in all_candidates if row["status"] == "success"
        }
        scratch = pathlib.Path(tempfile.mkdtemp(
            prefix="simp-replacement-", dir=artifacts
        ))
        if selected:
            try:
                traces, _ = record_sites(source, module_path, mathlib_source_path,
                                         selected, scratch)
            except Exception as exc:
                message = f"{type(exc).__name__}: {exc}"[:2000]
                status = "resource_failed" if isinstance(exc, subprocess.TimeoutExpired) else "record_failed"
                for ordinal in found:
                    if found[ordinal]:
                        results[ordinal] = (status, None, message)
                traces = {}
            renderable: dict[int, str] = {}
            for ordinal, sites in found.items():
                if not sites or ordinal in results:
                    continue
                rewritten, error = render_command(
                    source, command_by_ordinal[ordinal], site_pairs, traces,
                )
                if error:
                    results[ordinal] = ("render_failed", None, error[:2000])
                elif rewritten is None:
                    results[ordinal] = ("render_failed", None, "renderer produced no command")
                else:
                    renderable[ordinal] = rewritten

            if renderable:
                combined = dict(existing_successes)
                combined.update(renderable)
                okay, detail, _ = compile_candidate(
                    module_path, module_with_replacements(source, commands, combined),
                    scratch, 0,
                )
                if okay:
                    for ordinal in renderable:
                        results[ordinal] = ("success", renderable[ordinal], None)
                elif "timed out" in detail:
                    for ordinal in renderable:
                        results[ordinal] = ("resource_failed", None, detail[:2000])
                else:
                    accepted = dict(existing_successes)
                    serial = 1
                    timed_out = False
                    renderable_items = list(renderable.items())
                    for item_index, (ordinal, replacement) in enumerate(renderable_items):
                        trial = dict(accepted)
                        trial[ordinal] = replacement
                        probe_ok, probe_detail, _ = compile_candidate(
                            module_path, module_with_replacements(source, commands, trial),
                            scratch, serial,
                        )
                        serial += 1
                        if probe_ok:
                            accepted[ordinal] = replacement
                            results[ordinal] = ("success", replacement, None)
                        elif "timed out" in probe_detail:
                            timed_out = True
                            for remaining_ordinal, _ in renderable_items[item_index:]:
                                results[remaining_ordinal] = (
                                    "resource_failed", None,
                                    probe_detail[:2000],
                                )
                            break
                        else:
                            results[ordinal] = (
                                "compile_failed", None,
                                (probe_detail or detail or "stock Lean compilation failed")[:2000],
                            )
                    # The final accepted prefix must itself compile; this catches
                    # order-sensitive interactions before any transaction commits.
                    okay, final_detail = True, ""
                    if not timed_out:
                        okay, final_detail, _ = compile_candidate(
                            module_path, module_with_replacements(source, commands, accepted),
                            scratch, serial,
                        )
                    if not okay:
                        for ordinal in renderable:
                            if results.get(ordinal, (None,))[0] == "success":
                                results[ordinal] = (
                                    "compile_failed", None,
                                    (final_detail or "combined replacement set failed compilation")[:2000],
                                )
            for ordinal in pending_by_ordinal:
                if ordinal not in results:
                    results[ordinal] = ("worker_failed", None,
                                        "worker did not produce a terminal row result")

        for row in pending:
            if row["ordinal"] not in results:
                results[row["ordinal"]] = ("worker_failed", None,
                                            "worker did not classify candidate")
        if any(status not in STATUSES - {"pending"}
               for status, _, _ in results.values()):
            raise WorkerError("worker generated an invalid terminal status")
        db.execute("BEGIN IMMEDIATE")
        for ordinal, (status, replacement_text, error) in results.items():
            cursor = db.execute(
                "UPDATE simp_replacements SET status=?,replacement_text=?,error=? "
                "WHERE module_name=? AND ordinal=? AND status='pending'",
                (status, replacement_text, error, module, ordinal),
            )
            if cursor.rowcount != 1:
                raise WorkerError(f"candidate row changed during module processing: {module}:{ordinal}")
        db.commit()
        counts: dict[str, int] = {}
        for status, _, _ in results.values():
            counts[status] = counts.get(status, 0) + 1
        return {"module": module, "status": "committed", "rows": len(results),
                "counts": counts, "seconds": round(time.monotonic() - started, 2),
                "artifacts": str(scratch)}
    except Exception as exc:
        if db.in_transaction:
            db.rollback()
        # Read only pending candidates here; every result is persisted together
        # with the module's other results, preserving natural resume semantics.
        try:
            rows = candidate_rows(db, module)
            failed = [(row["ordinal"], "worker_failed", None,
                       f"{type(exc).__name__}: {exc}"[:2000])
                      for row in rows if row["status"] == "pending"]
            if failed:
                db.execute("BEGIN IMMEDIATE")
                for ordinal, status, replacement_text, error in failed:
                    db.execute(
                        "UPDATE simp_replacements SET status=?,replacement_text=?,error=? "
                        "WHERE module_name=? AND ordinal=? AND status='pending'",
                        (status, replacement_text, error, module, ordinal),
                    )
                db.commit()
            return {"module": module, "status": "worker_failed", "rows": len(failed),
                    "error": f"{type(exc).__name__}: {exc}"[:2000],
                    "seconds": round(time.monotonic() - started, 2)}
        except Exception as store_exc:
            if db.in_transaction:
                db.rollback()
            return {"module": module, "status": "worker_failed", "rows": 0,
                    "error": f"{type(exc).__name__}: {exc}; failure recording also failed: {store_exc}"[:2000],
                    "seconds": round(time.monotonic() - started, 2)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=pathlib.Path,
                        help="this worker's writable SQLite database copy")
    parser.add_argument("--manifest", required=True, type=pathlib.Path,
                        help="one exact module name per nonblank line")
    parser.add_argument("--artifacts", type=pathlib.Path,
                        default=ROOT / ".lake" / "simp-replacement-worker")
    args = parser.parse_args(argv)
    try:
        modules = read_manifest(args.manifest)
        args.artifacts.mkdir(parents=True, exist_ok=True)
        ensure_prerequisites()
        db = sqlite3.connect(args.database)
        db.execute("PRAGMA foreign_keys=ON")
        tables = {row[0] for row in db.execute(
            "SELECT name FROM sqlite_master WHERE type='table'")}
        if not {"modules", "commands", "simp_replacements"}.issubset(tables):
            raise WorkerError("database lacks modules, commands, or simp_replacements table")
        report = {"database": str(args.database.resolve()),
                  "manifest": str(args.manifest.resolve()), "modules": []}
        for module in modules:
            print(f"== {module}", flush=True)
            result = process_module(db, module, args.artifacts.resolve())
            report["modules"].append(result)
            print("   " + json.dumps(result, ensure_ascii=False), flush=True)
        report_path = args.artifacts / "worker-report.json"
        report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n",
                               encoding="utf-8")
        db.close()
        print(f"wrote {report_path}")
        return 0 if all(m["status"] in {"committed", "skipped_terminal"}
                        for m in report["modules"]) else 1
    except (OSError, sqlite3.Error, WorkerError, ValueError) as exc:
        print(f"FAIL {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
