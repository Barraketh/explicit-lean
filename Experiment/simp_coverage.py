#!/usr/bin/env python3
"""Inventory and test deterministic replacements for Mathlib simp calls.

The corpus lives under ``.lake/simp-coverage``.  Every operation is resumable;
``trials`` writes one JSON result per occurrence and ``aggregate`` writes one
result per module, so interrupted full-checkout runs do not lose progress.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
MATHLIB_SOURCE = MATHLIB / "Mathlib"
OUTPUT = ROOT / ".lake" / "simp-coverage"
INVENTORY = OUTPUT / "inventory.json"
RESULTS = OUTPUT / "results"
AGGREGATE_RESULTS = OUTPUT / "aggregate-results"
REPORT_MARKER = "EXPLICIT_LEAN_SIMP_REPORT "
PARSE_FAILURE_MARKER = "EXPLICIT_LEAN_INVENTORY_PARSE_FAILURE "
SUPPORTED_KINDS = {"simp", "simp_only"}
PASSIVE_RECORDING_SCHEMA = "explicitLean.simpModuleRecording"
PASSIVE_RECORDING_SCHEMA_VERSION = 2


def run(
    command: list[str], *, timeout: int | None = None
) -> tuple[int, str, float]:
    started = time.monotonic()
    try:
        result = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        return result.returncode, result.stdout, time.monotonic() - started
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return 124, output + "\nexplicit-lean: compilation timed out\n", time.monotonic() - started


def relative_module(path: str | Path) -> str:
    path = Path(path).resolve()
    try:
        return path.relative_to(MATHLIB).as_posix()
    except ValueError as error:
        raise RuntimeError(f"inventory path is outside pinned Mathlib: {path}") from error


def occurrence_id(module: str, start: int, end: int) -> str:
    identity = f"{module}:{start}:{end}".encode()
    return hashlib.sha256(identity).hexdigest()[:16]


DECLARATION = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|instance|example|structure|class|inductive)"
    r"(?:\s+(?!where\b)([^\s:({\[\]]+))?"
)


def declaration_index(source: str) -> list[tuple[int, str]]:
    result: list[tuple[int, str]] = []
    previous = 0
    byte_offset = 0
    line = 1
    for match in DECLARATION.finditer(source):
        segment = source[previous : match.start()]
        byte_offset += len(segment.encode("utf-8"))
        line += segment.count("\n")
        if match.group(1):
            name = match.group(1)
        else:
            keyword = match.group(0).strip().split()[-1]
            name = f"<{keyword} at line {line}>"
        result.append((byte_offset, name))
        previous = match.start()
    return result


def indexed_declaration_hint(
    index: list[tuple[int, str]], byte_offset: int, line: int
) -> str:
    position = bisect_right(index, (byte_offset, "\uffff")) - 1
    return index[position][1] if position >= 0 else f"<command containing line {line}>"


def inventory(args: argparse.Namespace) -> None:
    OUTPUT.mkdir(parents=True, exist_ok=True)
    if args.modules:
        paths = [MATHLIB / module for module in args.modules]
    else:
        paths = sorted(MATHLIB_SOURCE.rglob("*.lean"))
    missing = [str(path) for path in paths if not path.is_file()]
    if missing:
        raise RuntimeError(f"missing Mathlib modules: {missing[:5]!r}")

    output_parts: list[str] = []
    elapsed = 0.0
    for batch_number, start in enumerate(range(0, len(paths), args.batch_size)):
        batch = paths[start : start + args.batch_size]
        manifest = OUTPUT / f"inventory-files-{batch_number:04}.txt"
        manifest.write_text("".join(f"{path.resolve()}\n" for path in batch), encoding="utf-8")
        command = [
            "lake",
            "env",
            "lean",
            "--run",
            "Experiment/SimpInventory.lean",
            "--files-from",
            str(manifest),
        ]
        code, batch_output, batch_elapsed = run(command, timeout=args.timeout)
        output_parts.append(batch_output)
        elapsed += batch_elapsed
        if code != 0:
            (OUTPUT / "inventory.log").write_text("".join(output_parts), encoding="utf-8")
            raise RuntimeError(f"syntax inventory batch {batch_number} failed")
    output = "".join(output_parts)
    (OUTPUT / "inventory.log").write_text(output, encoding="utf-8")

    entries: list[dict[str, Any]] = []
    parse_failures: list[str] = []
    sources: dict[str, str] = {}
    for line_text in output.splitlines():
        if line_text.startswith(PARSE_FAILURE_MARKER):
            payload = json.loads(line_text[len(PARSE_FAILURE_MARKER) :])
            parse_failures.append(relative_module(payload["file"]))
            continue
        if not line_text.startswith("{"):
            continue
        entries.append(json.loads(line_text))

    failed_modules = set(parse_failures)
    entries = [
        raw
        for raw in entries
        if relative_module(raw["file"]) not in failed_modules
    ]
    for module in parse_failures:
        entries.extend(inventory_by_elaboration(module, args.timeout))

    normalized: list[dict[str, Any]] = []
    declaration_indexes: dict[str, list[tuple[int, str]]] = {}
    for raw in entries:
        module = raw.pop("module", None) or relative_module(raw.pop("file"))
        raw.pop("file", None)
        source = sources.setdefault(module, (MATHLIB / module).read_text(encoding="utf-8"))
        index = declaration_indexes.setdefault(module, declaration_index(source))
        raw["module"] = module
        raw["id"] = occurrence_id(module, raw["startByte"], raw["endByte"])
        raw["declaration"] = indexed_declaration_hint(
            index, raw["startByte"], raw["line"]
        )
        normalized.append(raw)
    entries = normalized
    entries.sort(key=lambda item: (item["module"], item["startByte"], item["endByte"]))
    document = {
        "schema": 1,
        "mathlib_revision": mathlib_revision(),
        "elapsed_seconds": round(elapsed, 3),
        "module_count": len(paths),
        "occurrence_count": len(entries),
        "counts": counts(entry["kind"] for entry in entries),
        "elaboration_fallback_modules": sorted(parse_failures),
        "entries": entries,
    }
    INVENTORY.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {INVENTORY.relative_to(ROOT)}: {len(entries)} tactic occurrences")
    print_counts(document["counts"])


def mathlib_revision() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=MATHLIB,
        text=True,
        capture_output=True,
        check=True,
    )
    return result.stdout.strip()


def counts(values: Iterable[str]) -> dict[str, int]:
    result: dict[str, int] = {}
    for value in values:
        result[value] = result.get(value, 0) + 1
    return dict(sorted(result.items()))


def print_counts(values: dict[str, int]) -> None:
    print("  " + ", ".join(f"{key}={value}" for key, value in values.items()))


def load_inventory() -> dict[str, Any]:
    if not INVENTORY.is_file():
        raise RuntimeError("run `python3 Experiment/simp_coverage.py inventory` first")
    return json.loads(INVENTORY.read_text(encoding="utf-8"))


def inject_import(source: bytes, imported: str = "ExplicitLean.SimpExplicit") -> bytes:
    marker = b"module\n"
    position = source.find(marker)
    if position < 0:
        raise RuntimeError("Mathlib source has no `module` header")
    insertion = position + len(marker)
    import_text = f"\nimport {imported}\n".encode()
    return source[:insertion] + import_text + source[insertion:]


def inventory_by_elaboration(module: str, timeout: int) -> list[dict[str, Any]]:
    """Compile one module with a linter when final-environment parsing recovers.

    This is the correctness fallback for files whose parsing depends on scoped
    state established while elaborating earlier commands.
    """
    original = (MATHLIB / module).read_bytes()
    imported = "ExplicitLean.SimpInventory"
    import_text = f"\nimport {imported}\n".encode()
    destination = OUTPUT / "inventory-fallback" / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(inject_import(original, imported))
    command = [
        "lake",
        "env",
        "lean",
        "-DexplicitLean.simpInventory=true",
        "-Dlinter.unusedVariables=false",
        "-Dlinter.unusedSimpArgs=false",
        "-DmaxHeartbeats=0",
        str(destination),
    ]
    code, output, _ = run(command, timeout=timeout)
    log = OUTPUT / "inventory-fallback" / f"{occurrence_id(module, 0, 0)}.log"
    log.write_text(output, encoding="utf-8")
    if code != 0:
        raise RuntimeError(f"elaboration inventory failed for {module} (see {log})")
    result: list[dict[str, Any]] = []
    for line_text in output.splitlines():
        if not line_text.startswith("{"):
            continue
        raw = json.loads(line_text)
        raw.pop("file", None)
        raw["module"] = module
        raw["startByte"] -= len(import_text)
        raw["endByte"] -= len(import_text)
        raw["line"] -= import_text.count(b"\n")
        result.append(raw)
    return result


def replace_bytes(source: bytes, entry: dict[str, Any], replacement: str) -> bytes:
    start, end = entry["startByte"], entry["endByte"]
    actual = source[start:end].decode("utf-8")
    if actual != entry["source"]:
        raise RuntimeError(
            f"stale inventory for {entry['module']}:{entry['line']}: "
            f"expected {entry['source']!r}, found {actual!r}"
        )
    indent = " " * entry["column"]
    replacement = replacement.replace("\n", "\n" + indent)
    return source[:start] + replacement.encode("utf-8") + source[end:]


def recording_replacement(entry: dict[str, Any], *, passive: bool = False) -> str:
    source = entry["source"]
    if not source.startswith("simp"):
        raise RuntimeError(f"unexpected supported syntax: {source!r}")
    replacement = "simp_explicit?" + source[len("simp") :]
    if not passive:
        return replacement
    identifier = entry["id"]
    return (
        "set_option explicitLean.simpExplicit.passive true in\n"
        f"set_option explicitLean.simpExplicit.occurrenceId \"{identifier}\" in\n"
        + replacement
    )


def write_copy(root: Path, entry: dict[str, Any], replacement: str) -> Path:
    source = (MATHLIB / entry["module"]).read_bytes()
    rewritten = inject_import(replace_bytes(source, entry, replacement))
    destination = root / entry["module"]
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(rewritten)
    return destination


def lean_command(path: Path, *, report: bool = False) -> list[str]:
    command = [
        "lake",
        "env",
        "lean",
        "-Dlinter.unusedVariables=false",
        "-Dlinter.unusedSimpArgs=false",
        "-Dlinter.unreachableTactic=false",
        "-DmaxHeartbeats=0",
    ]
    if report:
        command.append("-DexplicitLean.simpExplicit.report=true")
    command.append(str(path))
    return command


def parse_recording_report(output: str) -> dict[str, Any] | None:
    marker = output.find(REPORT_MARKER)
    if marker < 0:
        return None
    start = output.find("{", marker + len(REPORT_MARKER))
    if start < 0:
        return None
    try:
        value, _ = json.JSONDecoder().raw_decode(output[start:])
        return value
    except json.JSONDecodeError:
        return None


def parse_recording_reports(output: str) -> list[dict[str, Any]]:
    """Decode every passive report in compiler output.

    Reports are deliberately line-marked because Lean may interleave ordinary
    diagnostics with tactic messages.  The decoder accepts compact JSON only
    after the marker and never attempts to recover arbitrary raw syntax or
    expressions from stderr.
    """
    reports: list[dict[str, Any]] = []
    for line in output.splitlines():
        marker = line.find(REPORT_MARKER)
        if marker < 0:
            continue
        payload = line[marker + len(REPORT_MARKER) :].strip()
        try:
            value = json.loads(payload)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            reports.append(value)
    return reports


def group_passive_reports(reports: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Merge dynamic reports into one stable record per source occurrence."""
    grouped: dict[str, dict[str, Any]] = {}
    for report_index, report in enumerate(reports):
        identifier = report.get("occurrenceId")
        if not isinstance(identifier, str) or not identifier:
            continue
        occurrence = grouped.setdefault(
            identifier,
            {
                "occurrenceId": identifier,
                "declaration": report.get("declaration"),
                "originalSyntax": report.get("originalSyntax"),
                "reportIndices": [],
                "executions": [],
            },
        )
        occurrence["reportIndices"].append(report_index)
        for execution in report.get("executions", []):
            execution = dict(execution)
            execution["executionIndex"] = len(occurrence["executions"])
            occurrence["executions"].append(execution)
    result = sorted(grouped.values(), key=lambda item: item["occurrenceId"])
    for occurrence in result:
        occurrence["executionCount"] = len(occurrence["executions"])
    return result


def passive_module_recording(
    module: str,
    entries: list[dict[str, Any]],
    *,
    timeout: int,
    keep_copy: bool = False,
) -> dict[str, Any]:
    """Record every supported occurrence in one copied-module compile.

    Replacements are applied against the original byte array in descending
    source order.  This is important because the nested option wrapper is
    longer than the original tactic and therefore must not invalidate later
    offsets.  The compiler invocation is intentionally singular; reports may
    contain multiple executions for one source ID when an enclosing tactic
    combinator runs the occurrence more than once.
    """
    if not entries:
        raise RuntimeError(f"no supported occurrences for passive module {module}")
    source = (MATHLIB / module).read_bytes()
    rewritten = source
    for entry in sorted(entries, key=lambda item: item["startByte"], reverse=True):
        rewritten = replace_bytes(
            rewritten, entry, recording_replacement(entry, passive=True)
        )
    root = OUTPUT / "module-recording"
    destination = root / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(inject_import(rewritten))
    code, output, elapsed = run(lean_command(destination), timeout=timeout)
    reports = parse_recording_reports(output)
    occurrences = group_passive_reports(reports)
    expected_ids = sorted(entry["id"] for entry in entries)
    observed_ids = sorted(occurrence["occurrenceId"] for occurrence in occurrences)
    record: dict[str, Any] = {
        "schema": PASSIVE_RECORDING_SCHEMA,
        "schema_version": PASSIVE_RECORDING_SCHEMA_VERSION,
        "module": module,
        "expected_occurrence_count": len(entries),
        "expected_occurrence_ids": expected_ids,
        "report_count": len(reports),
        "observed_occurrence_ids": observed_ids,
        "represented_occurrence_ids": sorted(set(observed_ids)),
        "compile": code == 0,
        "compile_count": 1,
        "elapsed_seconds": round(elapsed, 3),
        "wall_seconds": round(elapsed, 3),
        "reports": reports,
        "occurrences": occurrences,
        "failure_category": None if code == 0 else classify_failure(output, "recording"),
    }
    key = hashlib.sha256(f"passive:{module}".encode()).hexdigest()[:16]
    result_dir = OUTPUT / "module-recording-results"
    result_dir.mkdir(parents=True, exist_ok=True)
    (result_dir / f"{key}.json").write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (result_dir / f"{key}.log").write_text(output, encoding="utf-8")
    if not keep_copy:
        # Keep the source copy for a failed compile because it is the most
        # useful diagnostic artifact; successful runs only need JSON/log data.
        destination.unlink(missing_ok=True)
    return record


FAILURES: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("hypothesis_location", ("currently supports the target only",)),
    ("nondefault_configuration", ("does not yet encode nondefault simp configuration",)),
    ("custom_discharger", ("does not yet encode a custom discharger",)),
    ("discharged_side_condition", ("cannot yet encode a discharged side condition",)),
    ("multiple_recorded_origins", ("expected one theorem rewrite, observed",)),
    ("simproc", ("cannot yet encode simproc",)),
    ("special_rule", ("cannot yet encode special simp rule",)),
    ("unprintable_local_fact", ("cannot print inaccessible local simp lemma",)),
    ("traversal_replay", ("cannot encode this simplification as a deterministic replay",)),
    ("replacement_parse", ("unexpected token", "unexpected identifier", "parser")),
    ("timeout", ("compilation timed out",)),
)


def classify_failure(output: str, phase: str) -> str:
    for category, needles in FAILURES:
        if any(needle in output for needle in needles):
            return category
    if "declaration has metavariables" in output or "unsolved goals" in output:
        return "nested_or_multigoal_context"
    if phase == "materialized":
        return "materialized_body_rejected"
    if phase == "aggregate":
        return "aggregate_interaction"
    return "unclassified_recorder_failure"


@dataclass(frozen=True)
class TrialConfig:
    timeout: int
    keep_copies: bool


def run_trial(entry: dict[str, Any], config: TrialConfig) -> dict[str, Any]:
    RESULTS.mkdir(parents=True, exist_ok=True)
    result_path = RESULTS / f"{entry['id']}.json"
    log_path = RESULTS / f"{entry['id']}.log"
    base: dict[str, Any] = {
        "id": entry["id"],
        "module": entry["module"],
        "declaration": entry["declaration"],
        "line": entry["line"],
        "column": entry["column"],
        "kind": entry["kind"],
        "original_syntax": entry["source"],
        "ordinary_simplification_succeeds": True,
    }
    work_root = OUTPUT / ("isolated" if config.keep_copies else "work") / entry["id"]
    try:
        recording_path = write_copy(work_root / "recording", entry, recording_replacement(entry))
        code, recording_output, recording_seconds = run(
            lean_command(recording_path, report=True), timeout=config.timeout
        )
        report = parse_recording_report(recording_output)
        base.update(
            recording_compile=code == 0,
            recording_seconds=round(recording_seconds, 3),
        )
        if code != 0 or report is None:
            base.update(
                status="failed",
                failure_category=classify_failure(recording_output, "recording")
                if code != 0
                else "missing_recorder_report",
            )
            log_path.write_text(recording_output, encoding="utf-8")
            result_path.write_text(json.dumps(base, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            return base

        base["declaration"] = report["declaration"]
        base.update(
            closes_goal=report["closesGoal"],
            trace_length=report["traceLength"],
            certificate_event_count=report["certificateEventCount"],
            positions_needed=report["positionsNeeded"],
            certificate=report["certificate"],
            certificate_bytes=report["certificateBytes"],
            encoding=report.get("encoding"),
            encoding_fallback_reason=report.get("encodingFallbackReason"),
            trace_encoding_kinds=[
                event.get("encodingKind")
                for execution in report.get("executions", [])
                for event in execution.get("trace", [])
                if event.get("encodingKind") is not None
            ],
            trace_encoding_reasons=[
                event.get("encodingReason")
                for execution in report.get("executions", [])
                for event in execution.get("trace", [])
                if event.get("encodingReason") is not None
            ],
        )
        materialized_path = write_copy(
            work_root / "materialized", entry, report["certificate"]
        )
        materialized_code, materialized_output, materialized_seconds = run(
            lean_command(materialized_path), timeout=config.timeout
        )
        base.update(
            materialized_compile=materialized_code == 0,
            materialized_seconds=round(materialized_seconds, 3),
        )
        if materialized_code == 0:
            base.update(status="passed", failure_category=None)
        else:
            failure_category = (
                "intermediate_presentation_changed"
                if report["certificateEventCount"] == 0
                else classify_failure(materialized_output, "materialized")
            )
            base.update(
                status="failed",
                failure_category=failure_category,
            )
        log_path.write_text(
            "RECORDING\n" + recording_output + "\nMATERIALIZED\n" + materialized_output,
            encoding="utf-8",
        )
    except Exception as error:  # Keep a full corpus run moving and classify harness defects.
        base.update(status="failed", failure_category="harness_error", error=str(error))
        log_path.write_text(str(error) + "\n", encoding="utf-8")
    result_path.write_text(json.dumps(base, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return base


def selected_entries(args: argparse.Namespace) -> list[dict[str, Any]]:
    entries = [entry for entry in load_inventory()["entries"] if entry["kind"] in SUPPORTED_KINDS]
    if args.modules:
        wanted = set(args.modules)
        entries = [entry for entry in entries if entry["module"] in wanted]
    if getattr(args, "ids", None):
        wanted_ids = set(args.ids)
        entries = [entry for entry in entries if entry["id"] in wanted_ids]
    if getattr(args, "limit", None) is not None:
        entries = entries[: args.limit]
    return entries


def trials(args: argparse.Namespace) -> None:
    RESULTS.mkdir(parents=True, exist_ok=True)
    entries = selected_entries(args)
    if args.resume:
        entries = [entry for entry in entries if not (RESULTS / f"{entry['id']}.json").exists()]
    config = TrialConfig(timeout=args.timeout, keep_copies=args.keep_copies)
    completed = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {executor.submit(run_trial, entry, config): entry for entry in entries}
        for future in as_completed(futures):
            result = future.result()
            completed += 1
            print(
                f"[{completed}/{len(entries)}] {result['status']:6} "
                f"{result['module']}:{result['line']} ({result.get('failure_category') or 'ok'})"
            )
    write_summary()


def load_results() -> list[dict[str, Any]]:
    if not RESULTS.is_dir():
        return []
    return [json.loads(path.read_text(encoding="utf-8")) for path in sorted(RESULTS.glob("*.json"))]


def apply_all(source: bytes, entries: list[dict[str, Any]], results: dict[str, dict[str, Any]]) -> bytes:
    rewritten = source
    for entry in sorted(entries, key=lambda item: item["startByte"], reverse=True):
        result = results[entry["id"]]
        rewritten = replace_bytes(rewritten, entry, result["certificate"])
    return inject_import(rewritten)


def aggregate_module(
    module: str,
    entries: list[dict[str, Any]],
    results: dict[str, dict[str, Any]],
    timeout: int,
) -> dict[str, Any]:
    AGGREGATE_RESULTS.mkdir(parents=True, exist_ok=True)
    source = (MATHLIB / module).read_bytes()
    destination = OUTPUT / "aggregate" / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(apply_all(source, entries, results))
    code, output, elapsed = run(lean_command(destination), timeout=timeout)
    record = {
        "module": module,
        "replacement_count": len(entries),
        "compile": code == 0,
        "seconds": round(elapsed, 3),
        "failure_category": None if code == 0 else classify_failure(output, "aggregate"),
    }
    key = hashlib.sha256(module.encode()).hexdigest()[:16]
    (AGGREGATE_RESULTS / f"{key}.json").write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (AGGREGATE_RESULTS / f"{key}.log").write_text(output, encoding="utf-8")
    return record


def aggregate(args: argparse.Namespace) -> None:
    AGGREGATE_RESULTS.mkdir(parents=True, exist_ok=True)
    inventory_entries = selected_entries(args)
    entries_by_id = {entry["id"]: entry for entry in inventory_entries}
    passed = {
        result["id"]: result
        for result in load_results()
        if result["id"] in entries_by_id and result["status"] == "passed"
    }
    by_module: dict[str, list[dict[str, Any]]] = {}
    for identifier in passed:
        entry = entries_by_id[identifier]
        by_module.setdefault(entry["module"], []).append(entry)
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {
            executor.submit(aggregate_module, module, entries, passed, args.timeout): module
            for module, entries in by_module.items()
        }
        for future in as_completed(futures):
            result = future.result()
            print(
                f"{'passed' if result['compile'] else 'failed'} {result['module']} "
                f"({result['replacement_count']} replacements)"
            )
    write_summary()


def write_summary() -> None:
    inventory_document = load_inventory()
    trial_results = load_results()
    aggregate_results = []
    if AGGREGATE_RESULTS.is_dir():
        aggregate_results = [
            json.loads(path.read_text(encoding="utf-8"))
            for path in sorted(AGGREGATE_RESULTS.glob("*.json"))
        ]
    trial_status = counts(result["status"] for result in trial_results)
    failures = counts(
        result["failure_category"]
        for result in trial_results
        if result.get("failure_category") is not None
    )
    summary = {
        "schema": 1,
        "mathlib_revision": inventory_document["mathlib_revision"],
        "inventory": {
            "modules": inventory_document["module_count"],
            "occurrences": inventory_document["occurrence_count"],
            "counts": inventory_document["counts"],
        },
        "trials": {
            "completed": len(trial_results),
            "status": trial_status,
            "failure_categories": failures,
        },
        "aggregate": {
            "completed": len(aggregate_results),
            "passed": sum(result["compile"] for result in aggregate_results),
            "failed": sum(not result["compile"] for result in aggregate_results),
        },
    }
    (OUTPUT / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    lines = [
        "| Stage | Total | Passed | Failed |",
        "| --- | ---: | ---: | ---: |",
        f"| Syntax inventory | {inventory_document['occurrence_count']} | — | — |",
        f"| Isolated materialization | {len(trial_results)} | {trial_status.get('passed', 0)} | {trial_status.get('failed', 0)} |",
        f"| Aggregate modules | {len(aggregate_results)} | {summary['aggregate']['passed']} | {summary['aggregate']['failed']} |",
        "",
        "| Inventory kind | Count |",
        "| --- | ---: |",
    ]
    lines.extend(f"| `{kind}` | {count} |" for kind, count in inventory_document["counts"].items())
    lines.extend(["", "| Failure category | Count |", "| --- | ---: |"])
    if failures:
        lines.extend(f"| `{kind}` | {count} |" for kind, count in failures.items())
    else:
        lines.append("| — | 0 |")
    (OUTPUT / "summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {(OUTPUT / 'summary.json').relative_to(ROOT)}")


def report(_: argparse.Namespace) -> None:
    write_summary()
    print((OUTPUT / "summary.md").read_text(encoding="utf-8"))


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    subparsers = result.add_subparsers(dest="command", required=True)

    inventory_parser = subparsers.add_parser("inventory", help="build the syntax-aware inventory")
    inventory_parser.add_argument("--module", dest="modules", action="append", default=[])
    inventory_parser.add_argument("--timeout", type=int, default=3600)
    inventory_parser.add_argument(
        "--batch-size", type=int, default=1000,
        help="restart Lean after this many modules to bound parser memory",
    )
    inventory_parser.set_defaults(function=inventory)

    trials_parser = subparsers.add_parser("trials", help="run isolated recorder/materialization checks")
    trials_parser.add_argument("--module", dest="modules", action="append", default=[])
    trials_parser.add_argument("--id", dest="ids", action="append", default=[])
    trials_parser.add_argument("--limit", type=int)
    trials_parser.add_argument("--jobs", type=int, default=max(1, min(4, os.cpu_count() or 1)))
    trials_parser.add_argument("--timeout", type=int, default=300)
    trials_parser.add_argument("--resume", action="store_true")
    trials_parser.add_argument("--keep-copies", action="store_true")
    trials_parser.set_defaults(function=trials)

    aggregate_parser = subparsers.add_parser("aggregate", help="compile all passing replacements together")
    aggregate_parser.add_argument("--module", dest="modules", action="append", default=[])
    aggregate_parser.add_argument("--limit", type=int)
    aggregate_parser.add_argument("--jobs", type=int, default=max(1, min(4, os.cpu_count() or 1)))
    aggregate_parser.add_argument("--timeout", type=int, default=600)
    aggregate_parser.set_defaults(function=aggregate)

    report_parser = subparsers.add_parser("report", help="regenerate machine and Markdown summaries")
    report_parser.set_defaults(function=report)
    return result


def main() -> None:
    args = parser().parse_args()
    try:
        args.function(args)
    except (RuntimeError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
