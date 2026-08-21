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
FIRST_OWNER_REPORT_MARKER = "EXPLICIT_LEAN_FIRST_OWNER_REPORT "
BODY_SCOPE_PROOF_REPORT_MARKER = "EXPLICIT_LEAN_BODY_SCOPE_PROOF_REPORT "
PARSE_FAILURE_MARKER = "EXPLICIT_LEAN_INVENTORY_PARSE_FAILURE "
SUPPORTED_KINDS = {"simp", "simp_only"}
PASSIVE_RECORDING_SCHEMA = "explicitLean.simpModuleRecording"
PASSIVE_RECORDING_SCHEMA_VERSION = 4
CLOSURE_SCHEMA = "explicitLean.simpClosure"
CLOSURE_SCHEMA_VERSION = 2
EXPECTED_SIMP_REPORT_SCHEMA_VERSION = 8


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


def body_scope_id(module: str, start: int, end: int) -> str:
    identity = f"body:{module}:{start}:{end}".encode()
    return hashlib.sha256(identity).hexdigest()[:16]


def first_owner_id(entry: dict[str, Any]) -> str:
    """Return the deterministic identity used by the closed `first` probe."""
    module = entry.get("module", "")
    start = entry.get("ownerStartByte")
    end = entry.get("ownerEndByte")
    if not isinstance(start, int) or not isinstance(end, int):
        raise RuntimeError(f"first owner has no stable range: {entry!r}")
    identity = f"first:{module}:{start}:{end}".encode()
    return hashlib.sha256(identity).hexdigest()[:16]


OWNER_FIELDS = (
    "ownerKind",
    "ownerRole",
    "ownerStartByte",
    "ownerEndByte",
    "ownerSource",
    "ownerChildStartByte",
    "ownerChildEndByte",
    "ownerChildSource",
    "ownerLeftStartByte",
    "ownerLeftEndByte",
    "ownerLeftSource",
)


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
        for field in OWNER_FIELDS:
            raw.setdefault(field, None)
        if raw.get("bodyScopeStartByte") is not None:
            raw["bodyScopeId"] = body_scope_id(
                module, raw["bodyScopeStartByte"], raw["bodyScopeEndByte"]
            )
        else:
            raw["bodyScopeId"] = None
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
        for field in ("bodyScopeStartByte", "bodyScopeEndByte"):
            if raw.get(field) is not None:
                raw[field] -= len(import_text)
        for field in OWNER_FIELDS:
            if field in {
                "ownerStartByte",
                "ownerEndByte",
                "ownerChildStartByte",
                "ownerChildEndByte",
                "ownerLeftStartByte",
                "ownerLeftEndByte",
            } and raw.get(field) is not None:
                raw[field] -= len(import_text)
        raw["line"] -= import_text.count(b"\n")
        result.append(raw)
    return result


def syntax_inventory_file(path: Path, module: str, timeout: int) -> list[dict[str, Any]]:
    """Run the syntax inventory against a focused non-Mathlib source file."""
    command = [
        "lake",
        "env",
        "lean",
        "--run",
        "Experiment/SimpInventory.lean",
        str(path.resolve()),
    ]
    code, output, _ = run(command, timeout=timeout)
    if code != 0:
        raise RuntimeError(f"focused syntax inventory failed for {path}:\n{output}")
    result: list[dict[str, Any]] = []
    for line_text in output.splitlines():
        if not line_text.startswith("{"):
            continue
        raw = json.loads(line_text)
        raw.pop("file", None)
        raw["module"] = module
        raw["id"] = occurrence_id(module, raw["startByte"], raw["endByte"])
        for field in OWNER_FIELDS:
            raw.setdefault(field, None)
        if raw.get("bodyScopeStartByte") is not None:
            raw["bodyScopeId"] = body_scope_id(
                module, raw["bodyScopeStartByte"], raw["bodyScopeEndByte"]
            )
        else:
            raw["bodyScopeId"] = None
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


def replace_range_bytes(
    source: bytes, start: int, end: int, expected: str, replacement: str
) -> bytes:
    """Replace one syntax-owned range after checking its original byte slice."""
    actual = source[start:end].decode("utf-8")
    if actual != expected:
        raise RuntimeError(
            f"stale owner inventory at {start}: expected {expected!r}, found {actual!r}"
        )
    line_start = source.rfind(b"\n", 0, start) + 1
    indent = " " * len(source[line_start:start].decode("utf-8"))
    replacement = replacement.replace("\n", "\n" + indent)
    return source[:start] + replacement.encode("utf-8") + source[end:]


def scoped_executions(report: dict[str, Any] | None) -> list[dict[str, Any]]:
    if report is None:
        return []
    return [
        execution
        for execution in report.get("executions", [])
        if isinstance(execution, dict)
    ]


def classify_terminal_outcome(
    report: dict[str, Any] | None, *, materialized_compile: bool | None = None
) -> str:
    """Classify one scoped occurrence without manufacturing a replacement."""
    executions = scoped_executions(report)
    if report is None or not executions:
        return "not_reached"
    if any(
        execution.get("disposition") not in {"committed", "backtracked"}
        for execution in executions
    ):
        return "coverage_failure"
    committed_successes = [
        execution
        for execution in executions
        if execution.get("result") == "succeeded"
        and execution.get("disposition") == "committed"
    ]
    if committed_successes:
        if materialized_compile is True:
            return "materialized"
        if materialized_compile is False:
            return "coverage_failure"
        return "coverage_failure"
    if any(execution.get("result") == "succeeded" for execution in executions):
        return "attempted_backtracked"
    return "original_failure"


def committed_certificates(report: dict[str, Any]) -> list[str]:
    """Return validated, goal-closing certificates for committed executions."""
    result: list[str] = []
    for execution in scoped_executions(report):
        if execution.get("result") != "succeeded":
            continue
        if execution.get("disposition") != "committed":
            continue
        certificate = execution.get("certificate")
        if not isinstance(certificate, str) or not certificate:
            raise RuntimeError("committed execution has no certificate")
        if not execution.get("closesGoal"):
            raise RuntimeError("committed execution does not close its input goal")
        result.append(certificate)
    return result


def closure_terminal_classification(report: dict[str, Any] | None) -> str:
    """Classify an occurrence before a source replacement is attempted."""
    executions = scoped_executions(report)
    if report is None or not executions:
        return "not_reached"
    if any(
        execution.get("disposition") not in {"committed", "backtracked"}
        for execution in executions
    ):
        return "coverage_failure"
    committed = [
        execution
        for execution in executions
        if execution.get("result") == "succeeded"
        and execution.get("disposition") == "committed"
    ]
    if committed:
        return "committed_pending"
    if any(execution.get("result") == "succeeded" for execution in executions):
        return "attempted_backtracked"
    return "original_failure"


def closure_result_base(
    entry: dict[str, Any], report: dict[str, Any] | None
) -> dict[str, Any]:
    executions = scoped_executions(report)
    return {
        "id": entry["id"],
        "module": entry["module"],
        "declaration": entry.get("declaration"),
        "line": entry.get("line"),
        "column": entry.get("column"),
        "kind": entry.get("kind"),
        "original_syntax": entry.get("source"),
        "terminal_outcome": closure_terminal_classification(report),
        "materialized_compile": None,
        "failure_reason": None,
        "dispositions": [execution.get("disposition") for execution in executions],
        "execution_summaries": [
            {
                "executionIndex": execution.get("executionIndex"),
                "attemptToken": execution.get("attemptToken"),
                "result": execution.get("result"),
                "disposition": execution.get("disposition"),
                "certificate": execution.get("certificate"),
                "certificateBytes": execution.get("certificateBytes"),
                "closesGoal": execution.get("closesGoal"),
                "encodingStatus": execution.get("encodingStatus"),
                "encoding": execution.get("encoding"),
                "encodingFallbackReason": execution.get("encodingFallbackReason"),
            }
            for execution in executions
        ],
        "report": report,
        "candidate": None,
    }


def _closure_candidate(
    *,
    kind: str,
    start: int,
    end: int,
    expected: str,
    replacement: str,
    declaration: str | None,
    entry_ids: list[str],
) -> dict[str, Any]:
    return {
        "kind": kind,
        "startByte": start,
        "endByte": end,
        "expected": expected,
        "replacement": replacement,
        "declaration": declaration,
        "entry_ids": entry_ids,
    }


def _closure_owner_key(entry: dict[str, Any]) -> tuple[int, int] | None:
    start = entry.get("ownerStartByte")
    end = entry.get("ownerEndByte")
    if isinstance(start, int) and isinstance(end, int):
        return (start, end)
    return None


def _closure_committed_executions(report: dict[str, Any] | None) -> list[dict[str, Any]]:
    return [
        execution
        for execution in scoped_executions(report)
        if execution.get("result") == "succeeded"
        and execution.get("disposition") == "committed"
    ]


def closure_candidate_plan(
    source: bytes,
    entries: list[dict[str, Any]],
    recording: dict[str, Any],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Build source-range candidates and per-occurrence closure results.

    The plan intentionally handles only the source owners already validated by
    the F2/F3 materializers.  Unsupported owners become structured failures;
    they are never guessed into a replacement.
    """
    reports = {
        report.get("occurrenceId"): report
        for report in recording.get("reports", [])
        if isinstance(report.get("occurrenceId"), str)
    }
    occurrence_results = [
        closure_result_base(entry, reports.get(entry["id"])) for entry in entries
    ]
    by_id = {result["id"]: result for result in occurrence_results}
    candidates: list[dict[str, Any]] = []
    handled: set[str] = set()

    first_groups: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for entry in entries:
        if entry.get("ownerKind") == "first":
            key = _closure_owner_key(entry)
            if key is not None:
                first_groups.setdefault(key, []).append(entry)
    first_reports = {
        report.get("ownerId"): report
        for report in recording.get("first_owner_reports", [])
        if isinstance(report.get("ownerId"), str)
    }
    for group in first_groups.values():
        representative = group[0]
        key = _closure_owner_key(representative)
        assert key is not None
        group_ids = [entry["id"] for entry in group]
        handled.update(group_ids)
        owner_report = first_reports.get(first_owner_id(representative))
        committed_ids = [
            entry["id"]
            for entry in group
            if _closure_committed_executions(reports.get(entry["id"]))
        ]
        if not committed_ids:
            continue
        if owner_report is None:
            for identifier in committed_ids:
                by_id[identifier]["terminal_outcome"] = "coverage_failure"
                by_id[identifier]["failure_reason"] = "unsupported_owner_materialization"
            continue
        try:
            owner_start, owner_end = key
            owner_source = representative.get("ownerSource")
            if not isinstance(owner_source, str):
                raise RuntimeError("first owner source is missing")
            replacement = first_owner_replacement(source, representative, owner_report)
            candidate = _closure_candidate(
                kind="first_owner",
                start=owner_start,
                end=owner_end,
                expected=owner_source,
                replacement=replacement,
                declaration=representative.get("declaration"),
                entry_ids=committed_ids,
            )
            candidates.append(candidate)
            for identifier in committed_ids:
                by_id[identifier]["candidate"] = candidate.copy()
        except Exception as error:
            for identifier in committed_ids:
                by_id[identifier]["terminal_outcome"] = "coverage_failure"
                by_id[identifier]["failure_reason"] = "unsupported_owner_materialization"
                by_id[identifier]["candidate_error"] = str(error)

    for entry in entries:
        identifier = entry["id"]
        if identifier in handled:
            continue
        result = by_id[identifier]
        if result["terminal_outcome"] != "committed_pending":
            continue
        report = reports.get(identifier)
        committed = _closure_committed_executions(report)
        owner_kind = entry.get("ownerKind")
        if len(committed) > 1:
            if owner_kind not in {"and_then", "all_goals"}:
                result["terminal_outcome"] = "coverage_failure"
                result["failure_reason"] = "unsupported_owner_materialization"
                continue
            try:
                owner_start = entry.get("ownerStartByte")
                owner_end = entry.get("ownerEndByte")
                owner_source = entry.get("ownerSource")
                if not isinstance(owner_start, int) or not isinstance(owner_end, int):
                    raise RuntimeError("owner range is missing")
                if not isinstance(owner_source, str):
                    raise RuntimeError("owner source is missing")
                replacement = owner_replacement(
                    source, entry, report or {}, sibling_entries=[entry]
                )
                candidate = _closure_candidate(
                    kind="syntax_owner",
                    start=owner_start,
                    end=owner_end,
                    expected=owner_source,
                    replacement=replacement,
                    declaration=entry.get("declaration"),
                    entry_ids=[identifier],
                )
                candidates.append(candidate)
                result["candidate"] = candidate.copy()
            except Exception as error:
                result["terminal_outcome"] = "coverage_failure"
                result["failure_reason"] = "unsupported_owner_materialization"
                result["candidate_error"] = str(error)
            continue
        if len(committed) != 1:
            result["terminal_outcome"] = "coverage_failure"
            result["failure_reason"] = "missing_certificate"
            continue
        if owner_kind == "first":
            result["terminal_outcome"] = "coverage_failure"
            result["failure_reason"] = "unsupported_owner_materialization"
            continue
        certificate = committed[0].get("certificate")
        if not isinstance(certificate, str) or not certificate:
            result["terminal_outcome"] = "coverage_failure"
            result["failure_reason"] = "missing_certificate"
            continue
        candidate = _closure_candidate(
            kind="occurrence",
            start=entry["startByte"],
            end=entry["endByte"],
            expected=entry["source"],
            replacement=certificate,
            declaration=entry.get("declaration"),
            entry_ids=[identifier],
        )
        candidates.append(candidate)
        result["candidate"] = candidate.copy()

    return candidates, occurrence_results


def closure_nonoverlapping_candidates(
    candidates: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """Drop overlapping candidate clusters and return stable per-id reasons."""
    ordered = sorted(candidates, key=lambda candidate: (candidate["startByte"], candidate["endByte"]))
    invalid_ids: dict[str, str] = {}
    valid: list[dict[str, Any]] = []
    for candidate in ordered:
        overlapping = [
            previous
            for previous in valid
            if previous["startByte"] < candidate["endByte"]
            and candidate["startByte"] < previous["endByte"]
        ]
        if overlapping:
            for conflicting in overlapping:
                for identifier in conflicting["entry_ids"]:
                    invalid_ids[identifier] = "overlapping_candidate_edits"
            for identifier in candidate["entry_ids"]:
                invalid_ids[identifier] = "overlapping_candidate_edits"
            valid = [item for item in valid if item not in overlapping]
        else:
            valid.append(candidate)
    return valid, invalid_ids


def apply_closure_candidates(source: bytes, candidates: list[dict[str, Any]]) -> bytes:
    rewritten = source
    for candidate in sorted(candidates, key=lambda item: item["startByte"], reverse=True):
        rewritten = replace_range_bytes(
            rewritten,
            candidate["startByte"],
            candidate["endByte"],
            candidate["expected"],
            candidate["replacement"],
        )
    return inject_import(rewritten)


def owner_replacement(
    source: bytes,
    entry: dict[str, Any],
    report: dict[str, Any],
    *,
    sibling_entries: list[dict[str, Any]] | None = None,
) -> str:
    """Build the F2 explicit branch replacement for one syntax owner."""
    kind = entry.get("ownerKind")
    role = entry.get("ownerRole")
    if kind == "and_then" and role == "and_then_right":
        pass
    elif kind == "all_goals" and role == "all_goals_child":
        pass
    else:
        raise RuntimeError(f"unsupported or non-owning F2 syntax parent: {kind}/{role}")
    owner_start = entry.get("ownerStartByte")
    owner_end = entry.get("ownerEndByte")
    owner_source = entry.get("ownerSource")
    if not isinstance(owner_start, int) or not isinstance(owner_end, int):
        raise RuntimeError("F2 owner has no byte range")
    if not isinstance(owner_source, str):
        raise RuntimeError("F2 owner has no source")
    if sibling_entries is not None:
        owner_identity = (owner_start, owner_end)
        same_owner = [
            sibling
            for sibling in sibling_entries
            if (sibling.get("ownerStartByte"), sibling.get("ownerEndByte"))
            == owner_identity
        ]
        if len(same_owner) != 1:
            raise RuntimeError("F2 owner contains multiple instrumented occurrences")
        for sibling in sibling_entries:
            if sibling.get("id") == entry.get("id"):
                continue
            sibling_start = sibling.get("startByte")
            if isinstance(sibling_start, int) and owner_start <= sibling_start < owner_end:
                raise RuntimeError("F2 owner contains another supported occurrence")
    certificates = committed_certificates(report)
    if not certificates:
        raise RuntimeError("F2 owner has no committed successful executions")
    if kind == "and_then":
        left_start = entry.get("ownerLeftStartByte")
        left_end = entry.get("ownerLeftEndByte")
        left_source = entry.get("ownerLeftSource")
        if not isinstance(left_start, int) or not isinstance(left_end, int):
            raise RuntimeError("andThen owner has no left-child range")
        if not isinstance(left_source, str):
            raise RuntimeError("andThen owner has no left-child source")
        actual_left = source[left_start:left_end].decode("utf-8")
        if actual_left != left_source:
            raise RuntimeError("andThen left-child inventory is stale")
        replacement = "focus\n  " + left_source
        # Bullets are peers of the left tactic.  The range replacer supplies
        # the owner's authored indentation after each newline.
        bullet_prefix = "  "
    else:
        replacement = ""
        bullet_prefix = ""
    for index, certificate in enumerate(certificates):
        lines = certificate.splitlines()
        if not lines:
            raise RuntimeError("empty F2 certificate")
        if index == 0 and kind == "and_then":
            replacement += "\n"
        elif index > 0:
            replacement += "\n"
        replacement += bullet_prefix + "· " + lines[0]
        for line in lines[1:]:
            replacement += "\n" + bullet_prefix + "  " + line
    actual_owner = source[owner_start:owner_end].decode("utf-8")
    if actual_owner != owner_source:
        raise RuntimeError("F2 owner inventory is stale")
    return replacement


def first_owner_replacement(
    source: bytes, entry: dict[str, Any], owner_report: dict[str, Any]
) -> str:
    """Build `exact <proof>` for one closed, syntax-owned `first` fragment."""
    if entry.get("ownerKind") != "first" or entry.get("ownerRole") != "first_branch":
        raise RuntimeError(f"not a first-owner entry: {entry!r}")
    owner_start = entry.get("ownerStartByte")
    owner_end = entry.get("ownerEndByte")
    owner_source = entry.get("ownerSource")
    if not isinstance(owner_start, int) or not isinstance(owner_end, int):
        raise RuntimeError("first owner has no byte range")
    if not isinstance(owner_source, str):
        raise RuntimeError("first owner has no source")
    actual = source[owner_start:owner_end].decode("utf-8")
    if actual != owner_source:
        raise RuntimeError("first owner inventory is stale")
    if owner_report.get("ownerId") != first_owner_id(entry):
        raise RuntimeError(f"first owner report identity mismatch: {owner_report!r}")
    proof = owner_report.get("proof")
    if not isinstance(proof, str) or not proof.strip():
        raise RuntimeError("first owner report has no proof")
    if owner_report.get("closesGoal") is not True:
        raise RuntimeError("first owner report did not close its input goal")
    lines = proof.splitlines()
    if not lines:
        raise RuntimeError("first owner report has an empty proof")
    replacement = "exact " + lines[0]
    for line in lines[1:]:
        replacement += "\n" + "  " + line
    return replacement


def materialize_owner_source(
    source: bytes,
    entry: dict[str, Any],
    report: dict[str, Any],
    *,
    sibling_entries: list[dict[str, Any]] | None = None,
) -> bytes:
    replacement = owner_replacement(
        source, entry, report, sibling_entries=sibling_entries
    )
    start = entry["ownerStartByte"]
    end = entry["ownerEndByte"]
    return replace_range_bytes(source, start, end, entry["ownerSource"], replacement)


def recording_replacement(entry: dict[str, Any], *, passive: bool = False) -> str:
    source = entry["source"]
    if not source.startswith("simp"):
        raise RuntimeError(f"unexpected supported syntax: {source!r}")
    replacement = "simp_explicit?" + source[len("simp") :]
    if not passive:
        return replacement
    identifier = entry["id"]
    return f'simp_explicit_record "{identifier}"' + source[len("simp") :]


def _replace_body_children(
    body_source: bytes, body_start: int, entries: list[dict[str, Any]]
) -> bytes:
    """Apply occurrence replacements inside one untouched body slice.

    The child offsets are translated only after the original body slice has
    been verified.  This keeps the enclosing body edit and its children as a
    single insertion-safe operation; no earlier replacement can drift a
    later source offset.
    """
    rewritten = body_source
    for entry in sorted(entries, key=lambda item: item["startByte"], reverse=True):
        local = dict(entry)
        local["startByte"] = entry["startByte"] - body_start
        local["endByte"] = entry["endByte"] - body_start
        # The body slice begins at the first tactic token, but continuation
        # lines retain their original file indentation.  New lines introduced
        # by a child replacement therefore need the original absolute column.
        rewritten = replace_bytes(
            rewritten, local, recording_replacement(entry, passive=True)
        )
    return rewritten


def _replace_body_scope_entries(
    body_source: bytes, body_start: int, entries: list[dict[str, Any]]
) -> bytes:
    """Rewrite body children and closed `first` owners in one local edit plan."""
    first_entries = [entry for entry in entries if entry.get("ownerKind") == "first"]
    first_groups: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for entry in first_entries:
        start = entry.get("ownerStartByte")
        end = entry.get("ownerEndByte")
        if not isinstance(start, int) or not isinstance(end, int):
            raise RuntimeError(f"first owner has no complete range: {entry!r}")
        first_groups.setdefault((start, end), []).append(entry)
    first_ranges = sorted(first_groups, key=lambda item: (item[0], item[1]))
    for index, (start, end) in enumerate(first_ranges):
        if index and first_ranges[index - 1][1] > start:
            raise RuntimeError("overlapping first owners require a broader materializer")
    edits: list[tuple[int, int, str, str]] = []
    covered_ids: set[str] = set()
    for (owner_start, owner_end), owner_entries in first_groups.items():
        if len({(entry.get("ownerStartByte"), entry.get("ownerEndByte")) for entry in owner_entries}) != 1:
            raise RuntimeError("first owner range grouping is inconsistent")
        owner_source = owner_entries[0].get("ownerSource")
        if not isinstance(owner_source, str):
            raise RuntimeError("first owner source is missing")
        owner_slice = body_source[owner_start - body_start : owner_end - body_start]
        if owner_slice.decode("utf-8") != owner_source:
            raise RuntimeError("first owner slice is stale")
        rewritten_owner = _replace_body_children(
            owner_slice, owner_start, owner_entries
        ).decode("utf-8")
        owner_token = first_owner_id(owner_entries[0])
        wrapper = f'simp_explicit_first_scope "{owner_token}" in\n  {rewritten_owner}'
        edits.append((owner_start - body_start, owner_end - body_start, owner_source, wrapper))
        covered_ids.update(entry.get("id") for entry in owner_entries if isinstance(entry.get("id"), str))
    for entry in entries:
        if entry.get("id") in covered_ids:
            continue
        edits.append(
            (
                entry["startByte"] - body_start,
                entry["endByte"] - body_start,
                entry["source"],
                recording_replacement(entry, passive=True),
            )
        )
    rewritten = body_source
    for start, end, expected, replacement in sorted(edits, key=lambda item: item[0], reverse=True):
        rewritten = replace_range_bytes(rewritten, start, end, expected, replacement)
    return rewritten


def _body_entry(source: bytes, entry: dict[str, Any]) -> dict[str, Any]:
    start = entry["bodyScopeStartByte"]
    end = entry["bodyScopeEndByte"]
    line_start = source.rfind(b"\n", 0, start) + 1
    column = len(source[line_start:start].decode("utf-8"))
    return {
        "startByte": start,
        "endByte": end,
        "source": entry["bodyScopeSource"],
        "column": column,
    }


def body_scope_replacement(
    source: bytes,
    body_entry: dict[str, Any],
    entries: list[dict[str, Any]],
    scope_id: str,
    *,
    export_proof: bool = False,
) -> str:
    body_start = body_entry["startByte"]
    body_source = source[body_start : body_entry["endByte"]]
    actual = body_source.decode("utf-8")
    if actual != body_entry["source"]:
        raise RuntimeError(
            f"stale body inventory at {body_start}: expected "
            f"{body_entry['source']!r}, found {actual!r}"
        )
    rewritten = _replace_body_scope_entries(body_source, body_start, entries).decode("utf-8")
    # Continuation lines in the inventoried body slice retain their absolute
    # source indentation.  The outer `replace_bytes` call will restore the
    # body's base column after every generated newline, so remove that base
    # column here before nesting the complete body two spaces under the scope
    # wrapper.  Generated continuation lines for an occurrence at the very
    # start of a body are already relative and therefore have no base prefix
    # to remove.
    base_prefix = " " * body_entry["column"]
    body_lines = rewritten.split("\n")
    for index in range(1, len(body_lines)):
        if body_lines[index].startswith(base_prefix):
            body_lines[index] = body_lines[index][len(base_prefix) :]
    relative_body = "\n".join(body_lines)
    nested_body = relative_body.replace("\n", "\n  ")
    command = "simp_explicit_body_scope_proof" if export_proof else "simp_explicit_body_scope"
    return f'{command} "{scope_id}" in\n  {nested_body}'


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
    # Lean uses the source path relative to its module root when assigning
    # names to anonymous declarations.  Every copied Mathlib module must keep
    # the original `Mathlib.Foo` identity or source references to those
    # generated names can fail even before an instrumented tactic executes.
    try:
        mathlib_index = path.parts.index("Mathlib")
    except ValueError:
        pass
    else:
        module_root = Path(*path.parts[:mathlib_index])
        command.extend(["-R", str(module_root)])
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


def parse_first_owner_reports(output: str) -> list[dict[str, Any]]:
    """Decode closed-first owner proof markers from a copied source compile."""
    reports: list[dict[str, Any]] = []
    for line in output.splitlines():
        marker = line.find(FIRST_OWNER_REPORT_MARKER)
        if marker < 0:
            continue
        payload = line[marker + len(FIRST_OWNER_REPORT_MARKER) :].strip()
        try:
            value = json.loads(payload)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            reports.append(value)
    return reports


def parse_body_scope_proof_reports(output: str) -> list[dict[str, Any]]:
    """Decode on-demand whole-body proof markers from a copied source compile."""
    reports: list[dict[str, Any]] = []
    for line in output.splitlines():
        marker = line.find(BODY_SCOPE_PROOF_REPORT_MARKER)
        if marker < 0:
            continue
        payload = line[marker + len(BODY_SCOPE_PROOF_REPORT_MARKER) :].strip()
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
    source_path: Path | None = None,
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
    source = (source_path or (MATHLIB / module)).read_bytes()
    rewritten = source
    body_groups: dict[str, list[dict[str, Any]]] = {}
    unscoped_entries: list[dict[str, Any]] = []
    for entry in entries:
        scope_id = entry.get("bodyScopeId")
        if scope_id and entry.get("bodyScopeStartByte") is not None:
            body_groups.setdefault(scope_id, []).append(entry)
        else:
            unscoped_entries.append(entry)
    edits: list[tuple[int, int, str, dict[str, Any]]] = []
    for scope_id, group in body_groups.items():
        representative = group[0]
        body = _body_entry(source, representative)
        edits.append(
            (
                body["startByte"],
                body["endByte"],
                body_scope_replacement(source, body, group, scope_id),
                body,
            )
        )
    for entry in unscoped_entries:
        edits.append((entry["startByte"], entry["endByte"],
                      recording_replacement(entry, passive=True), entry))
    for start, end, replacement, edit_entry in sorted(edits, key=lambda item: item[0], reverse=True):
        rewritten = replace_bytes(rewritten, edit_entry, replacement)
    root = OUTPUT / "module-recording"
    destination = root / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(inject_import(rewritten))
    # A copied module may have been compiled by an earlier bounded run.  Lean
    # can then reuse its adjacent olean without elaborating the instrumented
    # source, silently dropping the new scope reports.  Remove only artifacts
    # for this exact copied module before the singular recording compile.
    for suffix in (".olean", ".ilean", ".c", ".trace", ".hash"):
        destination.with_suffix(suffix).unlink(missing_ok=True)
    code, output, elapsed = run(lean_command(destination), timeout=timeout)
    reports = parse_recording_reports(output)
    first_owner_reports = parse_first_owner_reports(output)
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
        "first_owner_reports": first_owner_reports,
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
        trace_events = [
            event
            for execution in report.get("executions", [])
            for event in execution.get("trace", [])
        ]
        premise_events = [event for event in trace_events if event.get("premises")]
        base.update(
            recording_schema=report.get("schema"),
            recording_schema_version=report.get("schemaVersion"),
            local_renames=report.get("localRenames", []),
            closes_goal=report["closesGoal"],
            trace_length=report["traceLength"],
            certificate_event_count=report["certificateEventCount"],
            positions_needed=report["positionsNeeded"],
            certificate=report["certificate"],
            certificate_bytes=report["certificateBytes"],
            encoding=report.get("encoding"),
            encoding_fallback_reason=report.get("encodingFallbackReason"),
            trace_encoding_kinds=[
                event.get("encodingKind") for event in trace_events
                if event.get("encodingKind") is not None
            ],
            trace_encoding_reasons=[
                event.get("encodingReason") for event in trace_events
                if event.get("encodingReason") is not None
            ],
            trace_selector_kinds=[event.get("selectorKind") for event in trace_events],
            trace_selector_values=[event.get("selectorValue") for event in trace_events],
            premise_event_count=len(premise_events),
            premise_event_encoding_kinds=[
                event.get("encodingKind") for event in premise_events
            ],
            premise_event_outer_origin_kinds=[
                [origin.get("kind") for origin in event.get("origins", [])]
                for event in premise_events
            ],
            premise_event_outer_origin_names=[
                [origin.get("name") for origin in event.get("origins", [])]
                for event in premise_events
            ],
            premise_event_premise_origin_counts=[
                [len(premise.get("origins", [])) for premise in event.get("premises", [])]
                for event in premise_events
            ],
            premise_binding_names=[
                premise.get("bindingName")
                for event in premise_events
                for premise in event.get("premises", [])
            ],
            premise_encoding_kinds=[
                premise.get("encodingKind")
                for event in premise_events
                for premise in event.get("premises", [])
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


def closure_results_dir() -> Path:
    directory = OUTPUT / "closure-results"
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def closure_module_key(module: str) -> str:
    return hashlib.sha256(module.encode()).hexdigest()[:16]


def closure_module_path(module: str) -> Path:
    return closure_results_dir() / f"{closure_module_key(module)}.json"


def closure_occurrence_ids_digest(entries: list[dict[str, Any]]) -> str:
    payload = json.dumps(
        sorted(entry["id"] for entry in entries),
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def closure_source_sha256(source: bytes) -> str:
    return hashlib.sha256(source).hexdigest()


def write_json_atomic(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def closure_record_complete(
    path: Path,
    module: str,
    revision: str,
    *,
    source_sha256: str,
    expected_occurrence_ids_digest: str,
) -> bool:
    try:
        record = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return (
        isinstance(record, dict)
        and record.get("schema") == CLOSURE_SCHEMA
        and record.get("schemaVersion") == CLOSURE_SCHEMA_VERSION
        and record.get("module") == module
        and record.get("mathlib_revision") == revision
        and record.get("complete") is True
        and record.get("source_sha256") == source_sha256
        and record.get("expected_occurrence_ids_digest") == expected_occurrence_ids_digest
        and record.get("passive_recording_schema_version") == PASSIVE_RECORDING_SCHEMA_VERSION
        and record.get("expected_simp_report_schema_version")
        == EXPECTED_SIMP_REPORT_SCHEMA_VERSION
    )


def closure_record_matches_inventory(
    record: dict[str, Any],
    module: str,
    entries: list[dict[str, Any]],
    revision: str,
    *,
    source_path: Path | None = None,
) -> bool:
    """Validate a loaded record against the current full inventory module."""
    try:
        source = source_path.read_bytes() if source_path is not None else (MATHLIB / module).read_bytes()
    except OSError:
        return False
    expected_ids = sorted(entry["id"] for entry in entries)
    occurrences = record.get("occurrences")
    actual_ids = [
        occurrence.get("id")
        for occurrence in occurrences
        if isinstance(occurrence, dict)
    ] if isinstance(occurrences, list) else []
    return (
        record.get("schema") == CLOSURE_SCHEMA
        and record.get("schemaVersion") == CLOSURE_SCHEMA_VERSION
        and record.get("module") == module
        and record.get("mathlib_revision") == revision
        and record.get("complete") is True
        and record.get("source_sha256") == closure_source_sha256(source)
        and record.get("expected_occurrence_ids_digest")
        == closure_occurrence_ids_digest(entries)
        and record.get("passive_recording_schema_version")
        == PASSIVE_RECORDING_SCHEMA_VERSION
        and record.get("expected_simp_report_schema_version")
        == EXPECTED_SIMP_REPORT_SCHEMA_VERSION
        and record.get("expected_occurrence_ids") == expected_ids
        and len(actual_ids) == len(expected_ids)
        and len(set(actual_ids)) == len(expected_ids)
        and sorted(actual_ids) == expected_ids
    )


def compile_closure_candidates(
    module: str,
    source: bytes,
    candidates: list[dict[str, Any]],
    timeout: int,
    *,
    label: str,
    keep_copy: bool,
) -> dict[str, Any]:
    """Compile one exact candidate subset and retain its provenance."""
    started = time.monotonic()
    try:
        rewritten = apply_closure_candidates(source, candidates)
    except Exception as error:
        return {
            "label": label,
            "candidate_ids": [identifier for candidate in candidates for identifier in candidate["entry_ids"]],
            "declarations": sorted({candidate.get("declaration") for candidate in candidates}),
            "compile_invoked": False,
            "compile": False,
            "seconds": round(time.monotonic() - started, 3),
            "failure_reason": "source_rewrite_failure",
            "error": str(error),
        }
    attempt_key = hashlib.sha256(f"{module}:{label}".encode()).hexdigest()[:16]
    attempt_root = OUTPUT / "closure-attempts" / attempt_key
    destination = attempt_root / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(rewritten)
    for suffix in (".olean", ".ilean", ".c", ".trace", ".hash"):
        destination.with_suffix(suffix).unlink(missing_ok=True)
    code, output, elapsed = run(lean_command(destination), timeout=timeout)
    result = {
        "label": label,
        "candidate_ids": [identifier for candidate in candidates for identifier in candidate["entry_ids"]],
        "declarations": sorted({candidate.get("declaration") for candidate in candidates}),
        "compile_invoked": True,
        "compile": code == 0,
        "seconds": round(elapsed, 3),
        "failure_reason": None if code == 0 else classify_failure(output, "materialized"),
    }
    if not keep_copy and code == 0:
        destination.unlink(missing_ok=True)
    log_path = OUTPUT / "closure-attempts" / module / f"{label}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(output, encoding="utf-8")
    return result


def _body_scope_proof_rename_prefix(local_renames: list[dict[str, Any]]) -> str:
    """Render the exact local-name map exported by a body proof report."""
    if not local_renames:
        return ""
    parts: list[str] = []
    for rename in local_renames:
        if not isinstance(rename, dict):
            raise RuntimeError("body proof local-renames metadata is malformed")
        context_index = rename.get("contextIndex")
        generated_name = rename.get("generatedName")
        if not isinstance(context_index, int) or context_index < 0:
            raise RuntimeError("body proof local-renames metadata has an invalid index")
        if not isinstance(generated_name, str) or not generated_name:
            raise RuntimeError("body proof local-renames metadata has an invalid name")
        if set(rename) != {"contextIndex", "generatedName"}:
            raise RuntimeError("body proof local-renames metadata has unexpected fields")
        parts.append(f"{context_index} => {generated_name}")
    return "simp_explicit_rename [" + ", ".join(parts) + "]\n"


def body_scope_proof_replacement(report: dict[str, Any]) -> str:
    """Turn a validated whole-body proof report into a tactic sequence.

    The proof renderer may have renamed inaccessible locals in the enclosing
    declaration.  Keep the report's exact index/name map adjacent to the
    proof, so the source replacement remains deterministic and composable.
    """
    proof = report.get("proof")
    if not isinstance(proof, str) or not proof.strip():
        raise RuntimeError("body proof report has no proof")
    if report.get("closesGoal") is not True:
        raise RuntimeError("body proof report did not close its input goal")
    if report.get("failureReason") is not None:
        raise RuntimeError("body proof report contains a failure reason")
    local_renames = report.get("localRenames", [])
    if not isinstance(local_renames, list):
        raise RuntimeError("body proof report has malformed local-renames metadata")
    prefix = _body_scope_proof_rename_prefix(local_renames)
    lines = proof.splitlines()
    if not lines:
        raise RuntimeError("body proof report has an empty proof")
    replacement = prefix + "exact " + lines[0]
    for line in lines[1:]:
        replacement += "\n  " + line
    return replacement


def _eligible_body_scope_proof_candidates(
    source: bytes,
    entries: list[dict[str, Any]],
    candidates: list[dict[str, Any]],
    failed_ids: set[str],
    singleton_failures: dict[str, str],
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """Select the deliberately narrow singleton whole-body fallback set.

    A body fallback owns exactly one occurrence in the current module entry
    set.  In particular, it never claims a body containing another supported
    occurrence merely because that occurrence was not a diagnostic survivor.
    """
    entries_by_id = {entry.get("id"): entry for entry in entries}
    eligible: list[dict[str, Any]] = []
    rejected: dict[str, str] = {}
    for candidate in candidates:
        candidate_ids = candidate.get("entry_ids", [])
        if len(candidate_ids) != 1:
            continue
        identifier = candidate_ids[0]
        if identifier not in failed_ids:
            continue
        if singleton_failures.get(identifier) != "materialized_body_rejected":
            continue
        if candidate.get("kind") != "occurrence":
            continue
        entry = entries_by_id.get(identifier)
        if not isinstance(entry, dict):
            rejected[identifier] = "body_scope_proof_missing_entry"
            continue
        start = entry.get("bodyScopeStartByte")
        end = entry.get("bodyScopeEndByte")
        scope_id = entry.get("bodyScopeId")
        body_source = entry.get("bodyScopeSource")
        if (
            not isinstance(start, int)
            or not isinstance(end, int)
            or start >= end
            or not isinstance(scope_id, str)
            or not scope_id
            or not isinstance(body_source, str)
        ):
            rejected[identifier] = "body_scope_proof_ineligible"
            continue
        body_entries = [
            other
            for other in entries
            if other.get("bodyScopeId") == scope_id
            and other.get("bodyScopeStartByte") == start
            and other.get("bodyScopeEndByte") == end
        ]
        if len(body_entries) != 1 or body_entries[0].get("id") != identifier:
            rejected[identifier] = "body_scope_proof_not_singleton"
            continue
        try:
            body = _body_entry(source, entry)
            if body["source"] != body_source:
                raise RuntimeError("body source differs from inventory")
        except Exception:
            rejected[identifier] = "body_scope_proof_ineligible"
            continue
        eligible.append(
            {
                "candidate": candidate,
                "entry": entry,
                "body": body,
                "scope_id": scope_id,
            }
        )
    return eligible, rejected


def compile_body_scope_proofs(
    module: str,
    source: bytes,
    eligible: list[dict[str, Any]],
    timeout: int,
    *,
    keep_copy: bool,
) -> dict[str, Any]:
    """Passively export all eligible singleton body proofs in one compile."""
    if not eligible:
        raise RuntimeError("body proof fallback requires at least one eligible scope")
    ranges = sorted(
        (
            item["body"]["startByte"],
            item["body"]["endByte"],
            item,
        )
        for item in eligible
    )
    for previous, current in zip(ranges, ranges[1:]):
        if previous[1] > current[0]:
            raise RuntimeError("overlapping body proof scopes require broader ownership")
    rewritten = source
    for _, _, item in sorted(ranges, key=lambda value: value[0], reverse=True):
        replacement = body_scope_replacement(
            source,
            item["body"],
            [item["entry"]],
            item["scope_id"],
            export_proof=True,
        )
        rewritten = replace_range_bytes(
            rewritten,
            item["body"]["startByte"],
            item["body"]["endByte"],
            item["body"]["source"],
            replacement,
        )
    label = "body-scope-proof-fallback"
    attempt_key = hashlib.sha256(f"{module}:{label}".encode()).hexdigest()[:16]
    attempt_root = OUTPUT / "closure-attempts" / attempt_key
    destination = attempt_root / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(inject_import(rewritten))
    for suffix in (".olean", ".ilean", ".c", ".trace", ".hash"):
        destination.with_suffix(suffix).unlink(missing_ok=True)
    code, output, elapsed = run(lean_command(destination), timeout=timeout)
    reports = parse_body_scope_proof_reports(output)
    expected_scope_ids = [item["scope_id"] for item in eligible]
    expected_ids = [item["entry"]["id"] for item in eligible]
    reports_by_scope: dict[str, dict[str, Any]] = {}
    duplicate_scope_ids: set[str] = set()
    for report in reports:
        scope_id = report.get("scopeId")
        if not isinstance(scope_id, str):
            continue
        if scope_id in reports_by_scope:
            duplicate_scope_ids.add(scope_id)
        reports_by_scope[scope_id] = report
    result: dict[str, Any] = {
        "label": label,
        "candidate_ids": expected_ids,
        "declarations": sorted({item["entry"].get("declaration") for item in eligible}),
        "scope_ids": expected_scope_ids,
        "compile_invoked": True,
        "compile": code == 0,
        "seconds": round(elapsed, 3),
        "failure_reason": None if code == 0 else classify_failure(output, "materialized"),
        "report_count": len(reports),
        "reports": reports,
        "valid_scope_ids": [],
        "invalid_scope_ids": [],
        "duplicate_scope_ids": sorted(duplicate_scope_ids),
    }
    valid_scope_ids: list[str] = []
    invalid_scope_ids: list[str] = []
    for item in eligible:
        scope_id = item["scope_id"]
        report = reports_by_scope.get(scope_id)
        valid = (
            code == 0
            and scope_id not in duplicate_scope_ids
            and isinstance(report, dict)
            and report.get("scopeId") == scope_id
            and report.get("closesGoal") is True
            and isinstance(report.get("proof"), str)
            and bool(report["proof"].strip())
            and report.get("failureReason") is None
        )
        if valid:
            # Exercise the same strict source encoder used below while the
            # report is still attached to this audit record.
            try:
                body_scope_proof_replacement(report)
            except Exception:
                valid = False
        if valid:
            valid_scope_ids.append(scope_id)
        else:
            invalid_scope_ids.append(scope_id)
    result["valid_scope_ids"] = valid_scope_ids
    result["invalid_scope_ids"] = invalid_scope_ids
    if code == 0 and invalid_scope_ids:
        result["failure_reason"] = "body_scope_proof_report_invalid"
    if not keep_copy and code == 0:
        destination.unlink(missing_ok=True)
    log_path = OUTPUT / "closure-attempts" / module / f"{label}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(output, encoding="utf-8")
    return result


def body_scope_proof_candidates(
    source: bytes,
    eligible: list[dict[str, Any]],
    fallback_attempt: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """Build body-range candidates only from validated fallback reports."""
    reports = {
        report.get("scopeId"): report
        for report in fallback_attempt.get("reports", [])
        if isinstance(report, dict) and isinstance(report.get("scopeId"), str)
    }
    valid_scope_ids = set(fallback_attempt.get("valid_scope_ids", []))
    candidates: list[dict[str, Any]] = []
    failures: dict[str, str] = {}
    for item in eligible:
        identifier = item["entry"]["id"]
        scope_id = item["scope_id"]
        if scope_id not in valid_scope_ids:
            failures[identifier] = fallback_attempt.get("failure_reason") or (
                "body_scope_proof_report_invalid"
            )
            continue
        report = reports.get(scope_id)
        try:
            replacement = body_scope_proof_replacement(report or {})
        except Exception:
            failures[identifier] = "body_scope_proof_report_invalid"
            continue
        candidate = {
            "kind": "body_scope_proof",
            "startByte": item["body"]["startByte"],
            "endByte": item["body"]["endByte"],
            "expected": item["body"]["source"],
            "replacement": replacement,
            "declaration": item["entry"].get("declaration"),
            "entry_ids": [identifier],
            "bodyScopeId": scope_id,
            "proofBytes": report.get("proofBytes", len(report["proof"].encode("utf-8"))),
            "localRenames": report.get("localRenames", []),
        }
        candidates.append(candidate)
    return candidates, failures


def diagnose_closure_candidates(
    module: str,
    source: bytes,
    candidates: list[dict[str, Any]],
    timeout: int,
    *,
    keep_copy: bool,
) -> dict[str, Any]:
    """Bisect failing declaration groups and classify failing singletons.

    A failed optimistic module is not necessarily an interaction failure.  A
    singleton failure identified by the declaration bisection is an
    independently attributable candidate failure; callers can then compile
    the remaining candidates as one survivor aggregate.
    """
    attempts: list[dict[str, Any]] = []
    by_declaration: dict[str | None, list[dict[str, Any]]] = {}
    for candidate in candidates:
        by_declaration.setdefault(candidate.get("declaration"), []).append(candidate)
    counter = 0

    def visit(group: list[dict[str, Any]], label: str) -> None:
        nonlocal counter
        counter += 1
        attempt = compile_closure_candidates(
            module,
            source,
            group,
            timeout,
            label=f"diagnostic-{counter:04}-{label}",
            keep_copy=keep_copy,
        )
        attempts.append(attempt)
        if attempt["compile"] or len(group) <= 1:
            return
        midpoint = max(1, len(group) // 2)
        visit(group[:midpoint], label + "-a")
        visit(group[midpoint:], label + "-b")

    for index, (declaration, group) in enumerate(sorted(by_declaration.items(), key=lambda item: str(item[0]))):
        visit(group, f"decl-{index:04}")
    singleton_failures: dict[str, str] = {}
    for attempt in attempts:
        if attempt.get("compile"):
            continue
        candidate_ids = attempt.get("candidate_ids", [])
        if len(candidate_ids) != 1:
            continue
        identifier = candidate_ids[0]
        singleton_failures[identifier] = (
            attempt.get("failure_reason") or "unclassified_materialized_failure"
        )
    return {
        "attempts": attempts,
        "singleton_failures": singleton_failures,
    }


def _closure_failure_reason_for_report(
    result: dict[str, Any], reason: str
) -> None:
    result["terminal_outcome"] = "coverage_failure"
    result["failure_reason"] = reason
    result["materialized_compile"] = False


def validate_closure_recording(
    recording: dict[str, Any], entries: list[dict[str, Any]]
) -> dict[str, Any]:
    """Validate the stable identity/result envelope before planning edits."""
    expected_ids = {entry["id"] for entry in entries}
    observed_ids = {
        report.get("occurrenceId")
        for report in recording.get("reports", [])
        if isinstance(report, dict) and isinstance(report.get("occurrenceId"), str)
    }
    unexpected_ids = sorted(observed_ids - expected_ids)
    malformed_result_ids: set[str] = set()
    schema_mismatch_ids: set[str] = set()
    for report in recording.get("reports", []):
        if not isinstance(report, dict):
            continue
        identifier = report.get("occurrenceId")
        if not isinstance(identifier, str) or identifier not in expected_ids:
            continue
        if (
            report.get("schema") != "explicitLean.simpRecording"
            or report.get("schemaVersion") != EXPECTED_SIMP_REPORT_SCHEMA_VERSION
        ):
            schema_mismatch_ids.add(identifier)
        for execution in report.get("executions", []):
            if not isinstance(execution, dict):
                malformed_result_ids.add(identifier)
                continue
            if (
                execution.get("result") not in {"succeeded", "failed"}
                or execution.get("disposition") not in {"committed", "backtracked"}
            ):
                malformed_result_ids.add(identifier)
    return {
        "unexpected_ids": unexpected_ids,
        "malformed_result_ids": sorted(malformed_result_ids),
        "schema_mismatch_ids": sorted(schema_mismatch_ids),
    }


def run_closure_module(
    module: str,
    entries: list[dict[str, Any]],
    revision: str,
    timeout: int,
    *,
    keep_copy: bool,
    source_path: Path | None = None,
) -> dict[str, Any]:
    """Run the one-recording, optimistic-then-diagnostic module closure path."""
    started = time.monotonic()
    recording = passive_module_recording(
        module,
        entries,
        timeout=timeout,
        keep_copy=keep_copy,
        source_path=source_path,
    )
    candidates: list[dict[str, Any]] = []
    occurrence_results: list[dict[str, Any]]
    planning_failures: dict[str, str] = {}
    recording_validation = validate_closure_recording(recording, entries)
    unexpected_recording_ids = set(recording_validation["unexpected_ids"])
    invalid_recording_reasons = {
        identifier: "malformed_recording_result"
        for identifier in recording_validation["malformed_result_ids"]
    }
    invalid_recording_reasons.update(
        {
            identifier: "recording_schema_mismatch"
            for identifier in recording_validation["schema_mismatch_ids"]
        }
    )
    if recording.get("compile") and not unexpected_recording_ids:
        source = source_path.read_bytes() if source_path is not None else (MATHLIB / module).read_bytes()
        candidates, occurrence_results = closure_candidate_plan(source, entries, recording)
        invalid_ids = set(invalid_recording_reasons)
        if invalid_ids:
            candidates = [
                candidate
                for candidate in candidates
                if not invalid_ids.intersection(candidate["entry_ids"])
            ]
            planning_failures.update(invalid_recording_reasons)
        candidates, overlapping = closure_nonoverlapping_candidates(candidates)
        planning_failures.update(overlapping)
    else:
        reports = {
            report.get("occurrenceId"): report
            for report in recording.get("reports", [])
            if isinstance(report.get("occurrenceId"), str)
        }
        occurrence_results = [
            closure_result_base(entry, reports.get(entry["id"])) for entry in entries
        ]
        if not recording.get("compile"):
            # A failed copied-module compile cannot establish reachability or
            # commitment for any occurrence, even if partial diagnostics were
            # emitted before the failure.
            planning_failures.update(
                {entry["id"]: "recording_compile_failure" for entry in entries}
            )
        elif unexpected_recording_ids:
            planning_failures.update(
                {entry["id"]: "recording_identity_mismatch" for entry in entries}
            )

    by_id = {result["id"]: result for result in occurrence_results}
    for identifier, reason in planning_failures.items():
        _closure_failure_reason_for_report(by_id[identifier], reason)
    for candidate in candidates:
        for identifier in candidate["entry_ids"]:
            by_id[identifier]["candidate"] = candidate.copy()
    incomplete_candidate_plan = any(
        result.get("terminal_outcome") == "coverage_failure"
        for result in occurrence_results
    )
    # This describes planning before any candidate compilation.  It must not
    # be recomputed from later singleton/aggregate materialization failures.
    candidate_plan_complete = not incomplete_candidate_plan

    source = source_path.read_bytes() if source_path is not None else (MATHLIB / module).read_bytes()
    source_sha256 = closure_source_sha256(source)
    expected_occurrence_ids_digest = closure_occurrence_ids_digest(entries)
    attempts: list[dict[str, Any]] = []
    optimistic: dict[str, Any] | None = None
    survivor_optimistic: dict[str, Any] | None = None
    body_scope_fallback: dict[str, Any] | None = None
    body_scope_fallback_aggregate: dict[str, Any] | None = None
    body_scope_fallback_failures: dict[str, str] = {}
    singleton_failures: dict[str, str] = {}
    aggregate_compile: bool | None = None
    aggregate_failure_reason: str | None = None
    if recording.get("compile") and candidates:
        optimistic = compile_closure_candidates(
            module,
            source,
            candidates,
            timeout,
            label="optimistic",
            keep_copy=keep_copy,
        )
        attempts.append(optimistic)
        aggregate_compile = optimistic["compile"]
        if optimistic["compile"]:
            # aggregate_compile describes exactly this candidate subset.  A
            # separate candidate_plan_complete flag preserves any unrelated
            # planning failure without invalidating candidates that compiled.
            for candidate in candidates:
                for identifier in candidate["entry_ids"]:
                    result = by_id[identifier]
                    result["terminal_outcome"] = "materialized"
                    result["materialized_compile"] = True
                    result["failure_reason"] = None
        else:
            diagnostics = diagnose_closure_candidates(
                module, source, candidates, timeout, keep_copy=keep_copy
            )
            attempts.extend(diagnostics["attempts"])
            singleton_failures = diagnostics["singleton_failures"]
            failed_ids = set(singleton_failures)
            if failed_ids:
                survivor_candidates = [
                    candidate
                    for candidate in candidates
                    if not failed_ids.intersection(candidate["entry_ids"])
                ]

                # A committed occurrence whose ordinary certificate is
                # rejected in the complete body gets one deliberately narrow
                # whole-body proof attempt.  The fallback is eligible only for
                # a singleton occurrence body; all other singleton failures
                # retain their original reason code.
                eligible, eligibility_failures = _eligible_body_scope_proof_candidates(
                    source,
                    entries,
                    candidates,
                    failed_ids,
                    singleton_failures,
                )
                body_scope_fallback_failures.update(eligibility_failures)
                fallback_candidates: list[dict[str, Any]] = []
                if eligible:
                    try:
                        body_scope_fallback = compile_body_scope_proofs(
                            module,
                            source,
                            eligible,
                            timeout,
                            keep_copy=keep_copy,
                        )
                        attempts.append(body_scope_fallback)
                        fallback_candidates, report_failures = body_scope_proof_candidates(
                            source, eligible, body_scope_fallback
                        )
                        body_scope_fallback_failures.update(report_failures)
                    except Exception as error:
                        # This is a bounded source-rewrite/report failure for
                        # the eligible singleton set.  Keep the diagnostic
                        # artifact as an uninvoked attempt and continue with
                        # the ordinary survivor path.
                        body_scope_fallback = {
                            "label": "body-scope-proof-fallback",
                            "candidate_ids": [item["entry"]["id"] for item in eligible],
                            "declarations": sorted(
                                {item["entry"].get("declaration") for item in eligible}
                            ),
                            "scope_ids": [item["scope_id"] for item in eligible],
                            "compile_invoked": False,
                            "compile": False,
                            "seconds": 0,
                            "failure_reason": "body_scope_proof_source_rewrite_failure",
                            "report_count": 0,
                            "reports": [],
                            "valid_scope_ids": [],
                            "invalid_scope_ids": [item["scope_id"] for item in eligible],
                            "error": str(error),
                        }
                        attempts.append(body_scope_fallback)
                        body_scope_fallback_failures.update(
                            {
                                item["entry"]["id"]: body_scope_fallback["failure_reason"]
                                for item in eligible
                            }
                        )

                fallback_ids = {
                    identifier
                    for candidate in fallback_candidates
                    for identifier in candidate["entry_ids"]
                }
                # Replace each eligible failed occurrence in the candidate
                # aggregate, and retain the exact body candidate on its
                # occurrence record even if the final aggregate later rejects
                # it.  The aggregate compile below is the only acceptance
                # criterion for marking it materialized.
                for candidate in fallback_candidates:
                    for identifier in candidate["entry_ids"]:
                        by_id[identifier]["candidate"] = candidate.copy()

                aggregate_candidates = survivor_candidates + fallback_candidates
                if fallback_candidates:
                    body_scope_fallback_aggregate = compile_closure_candidates(
                        module,
                        source,
                        aggregate_candidates,
                        timeout,
                        label="body-scope-proof-aggregate",
                        keep_copy=keep_copy,
                    )
                    attempts.append(body_scope_fallback_aggregate)
                    if body_scope_fallback_aggregate["compile"]:
                        for candidate in aggregate_candidates:
                            for identifier in candidate["entry_ids"]:
                                result = by_id[identifier]
                                result["terminal_outcome"] = "materialized"
                                result["materialized_compile"] = True
                                result["failure_reason"] = None
                        unresolved_ids = failed_ids - fallback_ids
                        for identifier in unresolved_ids:
                            if identifier in by_id:
                                _closure_failure_reason_for_report(
                                    by_id[identifier],
                                    body_scope_fallback_failures.get(
                                        identifier, singleton_failures.get(identifier, "singleton_candidate_failures")
                                    ),
                                )
                        all_candidate_ids = {
                            identifier
                            for candidate in candidates
                            for identifier in candidate["entry_ids"]
                        }
                        aggregate_candidate_ids = {
                            identifier
                            for candidate in aggregate_candidates
                            for identifier in candidate["entry_ids"]
                        }
                        if aggregate_candidate_ids == all_candidate_ids:
                            # The fallback aggregate is now the accepted
                            # complete aggregate.  The failed optimistic
                            # attempt remains in `attempts` for auditability.
                            aggregate_compile = True
                            aggregate_failure_reason = None
                        else:
                            aggregate_failure_reason = "singleton_candidate_failures"
                    else:
                        body_scope_fallback_failures.update(
                            {
                                identifier: "body_scope_proof_rejected"
                                for candidate in fallback_candidates
                                for identifier in candidate["entry_ids"]
                            }
                        )

                # If no fallback aggregate was accepted, compile the ordinary
                # survivors exactly as before.  This keeps unresolved
                # singleton failures attributable without pretending that a
                # body proof was materialized in isolation.
                fallback_aggregate_accepted = (
                    body_scope_fallback_aggregate is not None
                    and body_scope_fallback_aggregate.get("compile") is True
                )
                if not fallback_aggregate_accepted and survivor_candidates:
                    survivor_optimistic = compile_closure_candidates(
                        module,
                        source,
                        survivor_candidates,
                        timeout,
                        label="survivor-optimistic",
                        keep_copy=keep_copy,
                    )
                    attempts.append(survivor_optimistic)
                if fallback_aggregate_accepted:
                    # The accepted body aggregate already materialized all
                    # candidates it contains.  Any failed singleton outside
                    # that aggregate remains a coverage failure.
                    for identifier in failed_ids - fallback_ids:
                        if identifier in by_id:
                            _closure_failure_reason_for_report(
                                by_id[identifier],
                                body_scope_fallback_failures.get(
                                    identifier,
                                    singleton_failures.get(identifier, "singleton_candidate_failures"),
                                ),
                            )
                elif survivor_optimistic is not None and survivor_optimistic["compile"]:
                    # The requested all-candidate aggregate remains failed:
                    # only the survivor aggregate is independently proven.
                    aggregate_failure_reason = "singleton_candidate_failures"
                    for candidate in survivor_candidates:
                        for identifier in candidate["entry_ids"]:
                            result = by_id[identifier]
                            result["terminal_outcome"] = "materialized"
                            result["materialized_compile"] = True
                            result["failure_reason"] = None
                    for identifier in failed_ids:
                        if identifier in by_id:
                            _closure_failure_reason_for_report(
                                by_id[identifier],
                                body_scope_fallback_failures.get(
                                    identifier, singleton_failures.get(identifier, "singleton_candidate_failures")
                                ),
                            )
                else:
                    aggregate_failure_reason = "aggregate_interaction"
                    for candidate in candidates:
                        for identifier in candidate["entry_ids"]:
                            if identifier in body_scope_fallback_failures:
                                reason = body_scope_fallback_failures[identifier]
                            elif identifier in singleton_failures:
                                reason = singleton_failures[identifier]
                            else:
                                reason = aggregate_failure_reason
                            _closure_failure_reason_for_report(by_id[identifier], reason)
            else:
                # No independently failing singleton was found, so the
                # optimistic failure is a genuine cross-candidate
                # interaction (or an unresolved multi-candidate failure).
                aggregate_failure_reason = "aggregate_interaction"
                for candidate in candidates:
                    for identifier in candidate["entry_ids"]:
                        _closure_failure_reason_for_report(
                            by_id[identifier], aggregate_failure_reason
                        )
    elif recording.get("compile") and not candidates:
        aggregate_compile = None
        if incomplete_candidate_plan:
            aggregate_failure_reason = "candidate_plan_incomplete"

    for result in occurrence_results:
        if result["terminal_outcome"] == "committed_pending":
            _closure_failure_reason_for_report(
                result,
                planning_failures.get(result["id"], "missing_certificate"),
            )

    # Candidate compilation and overall closure completeness are separate
    # facts.  A successful recording with only legitimate non-success
    # outcomes (not_reached, attempted_backtracked, or original_failure) has
    # no replacement work and is complete even though aggregate compilation
    # is skipped because there are no candidates.
    terminal_classification_complete = not any(
        result.get("terminal_outcome") in {"coverage_failure", "committed_pending"}
        for result in occurrence_results
    )
    candidate_materialization_complete = all(
        result.get("candidate") is None
        or (
            result.get("terminal_outcome") == "materialized"
            and result.get("materialized_compile") is True
        )
        for result in occurrence_results
    )
    closure_complete = (
        recording.get("compile") is True
        and terminal_classification_complete
        and candidate_materialization_complete
    )
    materialization_compile_count = sum(
        bool(attempt.get("compile_invoked")) for attempt in attempts
    )

    module_compile_provenance = {
        "aggregateCompile": aggregate_compile,
        "optimisticCompile": (
            optimistic.get("compile") if optimistic is not None else None
        ),
        "aggregateFailureReason": aggregate_failure_reason,
        "candidatePlanComplete": candidate_plan_complete,
        "terminalClassificationComplete": terminal_classification_complete,
        "closureComplete": closure_complete,
        "recordingValidation": recording_validation,
        "survivorCompile": (
            survivor_optimistic.get("compile")
            if survivor_optimistic is not None
            else None
        ),
        "survivorCandidateCount": (
            len(survivor_optimistic.get("candidate_ids", []))
            if survivor_optimistic is not None
            else 0
        ),
        "singletonFailures": singleton_failures,
        "bodyScopeProofFallback": body_scope_fallback,
        "bodyScopeProofAggregate": body_scope_fallback_aggregate,
        "bodyScopeProofFailures": body_scope_fallback_failures,
        "attemptCount": len(attempts),
        "attemptLabels": [attempt.get("label") for attempt in attempts],
    }
    for result in occurrence_results:
        result["module_compile"] = module_compile_provenance.copy()

    materialization_seconds = sum(attempt.get("seconds", 0) for attempt in attempts)
    record: dict[str, Any] = {
        "schema": CLOSURE_SCHEMA,
        "schemaVersion": CLOSURE_SCHEMA_VERSION,
        "complete": True,
        "mathlib_revision": revision,
        "module": module,
        "source_sha256": source_sha256,
        "expected_occurrence_ids_digest": expected_occurrence_ids_digest,
        "passive_recording_schema_version": PASSIVE_RECORDING_SCHEMA_VERSION,
        "expected_simp_report_schema_version": EXPECTED_SIMP_REPORT_SCHEMA_VERSION,
        "expected_occurrence_count": len(entries),
        "expected_occurrence_ids": sorted(entry["id"] for entry in entries),
        "observed_occurrence_ids": recording.get("observed_occurrence_ids", []),
        "recording_validation": recording_validation,
        "recording": {
            "compile": recording.get("compile"),
            "compile_count": recording.get("compile_count", 0),
            "elapsed_seconds": recording.get("elapsed_seconds", 0),
            "report_count": recording.get("report_count", 0),
            "observed_occurrence_ids": recording.get("observed_occurrence_ids", []),
            "first_owner_reports": recording.get("first_owner_reports", []),
            "failure_category": recording.get("failure_category"),
        },
        "occurrences": occurrence_results,
        "aggregate": {
            "compile": aggregate_compile,
            "optimistic_compile": (
                optimistic.get("compile") if optimistic is not None else None
            ),
            "failure_reason": aggregate_failure_reason,
            "candidate_plan_complete": candidate_plan_complete,
            "terminal_classification_complete": terminal_classification_complete,
            "closure_complete": closure_complete,
            "singleton_failures": singleton_failures,
            "body_scope_proof_fallback": body_scope_fallback,
            "body_scope_proof_aggregate": body_scope_fallback_aggregate,
            "body_scope_proof_failures": body_scope_fallback_failures,
            "survivor_compile": (
                survivor_optimistic.get("compile")
                if survivor_optimistic is not None
                else None
            ),
            "survivor_candidate_count": (
                len(survivor_optimistic.get("candidate_ids", []))
                if survivor_optimistic is not None
                else 0
            ),
            "replacement_count": len(candidates),
            "attempts": attempts,
            "materialization_compile_count": materialization_compile_count,
            "seconds": round(materialization_seconds, 3),
        },
        "timings": {
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "recording_seconds": recording.get("elapsed_seconds", 0),
            "materialization_seconds": round(materialization_seconds, 3),
        },
    }
    write_json_atomic(closure_module_path(module), record)
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


def load_closure_records() -> list[dict[str, Any]]:
    directory = closure_results_dir()
    records: list[dict[str, Any]] = []
    for path in sorted(directory.glob("*.json")):
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            records.append(value)
    return records


def write_closure_summary(revision: str) -> dict[str, Any]:
    inventory = load_inventory()
    expected_entries = [
        entry for entry in inventory["entries"] if entry["kind"] in SUPPORTED_KINDS
    ]
    expected_by_module: dict[str, list[dict[str, Any]]] = {}
    for entry in expected_entries:
        expected_by_module.setdefault(entry["module"], []).append(entry)
    valid_by_module: dict[str, dict[str, Any]] = {}
    for record in load_closure_records():
        module = record.get("module")
        if not isinstance(module, str) or module not in expected_by_module:
            continue
        if closure_record_matches_inventory(
            record, module, expected_by_module[module], revision
        ):
            valid_by_module[module] = record
    records = [valid_by_module[module] for module in sorted(valid_by_module)]
    expected_module_ids = sorted(expected_by_module)
    valid_module_ids = sorted(valid_by_module)
    missing_module_ids = [
        module for module in expected_module_ids if module not in valid_by_module
    ]
    expected_occurrence_ids = {
        entry["id"] for entry in expected_entries
    }
    occurrence_values = [
        occurrence
        for record in records
        for occurrence in record.get("occurrences", [])
    ]
    valid_occurrence_ids = {
        occurrence.get("id")
        for occurrence in occurrence_values
        if isinstance(occurrence.get("id"), str)
    }
    missing_occurrence_ids = sorted(expected_occurrence_ids - valid_occurrence_ids)
    outcome_counts = counts(
        occurrence.get("terminal_outcome", "unclassified")
        for occurrence in occurrence_values
    )
    reason_counts = counts(
        occurrence.get("failure_reason")
        for occurrence in occurrence_values
        if occurrence.get("failure_reason") is not None
    )
    aggregate_values = [record.get("aggregate", {}) for record in records]
    aggregate_passed = sum(value.get("compile") is True for value in aggregate_values)
    aggregate_failed = sum(value.get("compile") is False for value in aggregate_values)
    aggregate_skipped = sum(value.get("compile") is None for value in aggregate_values)
    closure_complete_modules = sum(
        value.get("closure_complete") is True for value in aggregate_values
    )
    closure_incomplete_modules = len(expected_module_ids) - closure_complete_modules
    summary: dict[str, Any] = {
        "schema": CLOSURE_SCHEMA,
        "schemaVersion": CLOSURE_SCHEMA_VERSION,
        "mathlib_revision": revision,
        "modules": len(records),
        "occurrences": len(occurrence_values),
        "expected_modules": len(expected_module_ids),
        "expected_occurrences": len(expected_occurrence_ids),
        "valid_recorded_modules": len(valid_module_ids),
        "valid_recorded_occurrences": len(valid_occurrence_ids),
        "missing_modules": missing_module_ids,
        "missing_occurrences": missing_occurrence_ids,
        "closure_modules": {
            "complete": closure_complete_modules,
            "incomplete": closure_incomplete_modules,
        },
        "terminal_outcomes": outcome_counts,
        "reason_clusters": reason_counts,
        "compile_counts": {
            "recording": sum(
                record.get("recording", {}).get("compile_count", 0) for record in records
            ),
            "materialization": sum(
                record.get("aggregate", {}).get("materialization_compile_count", 0)
                for record in records
            ),
        },
        "materialized_replacements": outcome_counts.get("materialized", 0),
        "aggregate_modules": {
            "passed": aggregate_passed,
            "failed": aggregate_failed,
            "skipped": aggregate_skipped,
        },
        "timings": {
            "recording_seconds": round(
                sum(record.get("timings", {}).get("recording_seconds", 0) for record in records),
                3,
            ),
            "materialization_seconds": round(
                sum(
                    record.get("timings", {}).get("materialization_seconds", 0)
                    for record in records
                ),
                3,
            ),
            "elapsed_seconds": round(
                sum(record.get("timings", {}).get("elapsed_seconds", 0) for record in records),
                3,
            ),
        },
    }
    summary_path = OUTPUT / "closure-summary.json"
    write_json_atomic(summary_path, summary)
    lines = [
        "| Closure stage | Count |",
        "| --- | ---: |",
        f"| Expected modules | {summary['expected_modules']} |",
        f"| Valid recorded modules | {summary['valid_recorded_modules']} |",
        f"| Missing modules | {len(summary['missing_modules'])} |",
        f"| Expected occurrences | {summary['expected_occurrences']} |",
        f"| Valid recorded occurrences | {summary['valid_recorded_occurrences']} |",
        f"| Missing occurrences | {len(summary['missing_occurrences'])} |",
        f"| Closure modules complete | {summary['closure_modules']['complete']} |",
        f"| Closure modules incomplete | {summary['closure_modules']['incomplete']} |",
        f"| Recording compiles | {summary['compile_counts']['recording']} |",
        f"| Materialization compiles | {summary['compile_counts']['materialization']} |",
        f"| Materialized replacements | {summary['materialized_replacements']} |",
        f"| Aggregate modules passed | {aggregate_passed} |",
        f"| Aggregate modules failed | {aggregate_failed} |",
        f"| Aggregate modules skipped | {aggregate_skipped} |",
        "",
        "| Terminal outcome | Count |",
        "| --- | ---: |",
    ]
    lines.extend(f"| `{kind}` | {count} |" for kind, count in outcome_counts.items())
    lines.extend(["", "| Failure reason | Count |", "| --- | ---: |"])
    if reason_counts:
        lines.extend(f"| `{kind}` | {count} |" for kind, count in reason_counts.items())
    else:
        lines.append("| — | 0 |")
    (OUTPUT / "closure-summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return summary


def closure(args: argparse.Namespace) -> None:
    inventory_document = load_inventory()
    revision = inventory_document["mathlib_revision"]
    entries = [
        entry
        for entry in inventory_document["entries"]
        if entry["kind"] in SUPPORTED_KINDS
        and (not args.modules or entry["module"] in set(args.modules))
    ]
    by_module: dict[str, list[dict[str, Any]]] = {}
    for entry in entries:
        by_module.setdefault(entry["module"], []).append(entry)
    modules = sorted(by_module)
    if args.limit is not None:
        modules = modules[: args.limit]
    pending: list[str] = []
    for module in modules:
        path = closure_module_path(module)
        module_entries = by_module[module]
        module_source = (MATHLIB / module).read_bytes()
        if args.resume and closure_record_complete(
            path,
            module,
            revision,
            source_sha256=closure_source_sha256(module_source),
            expected_occurrence_ids_digest=closure_occurrence_ids_digest(module_entries),
        ):
            print(f"resume-skip {module}")
            continue
        pending.append(module)
    completed = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {
            executor.submit(
                run_closure_module,
                module,
                by_module[module],
                revision,
                args.timeout,
                keep_copy=args.keep_copies,
            ): module
            for module in pending
        }
        for future in as_completed(futures):
            module = futures[future]
            try:
                record = future.result()
            except Exception as error:
                module_source = (MATHLIB / module).read_bytes()
                record = {
                    "schema": CLOSURE_SCHEMA,
                    "schemaVersion": CLOSURE_SCHEMA_VERSION,
                    "complete": True,
                    "mathlib_revision": revision,
                    "module": module,
                    "source_sha256": closure_source_sha256(module_source),
                    "expected_occurrence_ids_digest": closure_occurrence_ids_digest(
                        by_module[module]
                    ),
                    "passive_recording_schema_version": PASSIVE_RECORDING_SCHEMA_VERSION,
                    "expected_simp_report_schema_version": EXPECTED_SIMP_REPORT_SCHEMA_VERSION,
                    "expected_occurrence_count": len(by_module[module]),
                    "expected_occurrence_ids": sorted(entry["id"] for entry in by_module[module]),
                    "observed_occurrence_ids": [],
                    "recording": {
                        "compile": False,
                        "compile_count": 0,
                        "failure_category": "harness_error",
                    },
                    "occurrences": [
                        {
                            **closure_result_base(entry, None),
                            "terminal_outcome": "coverage_failure",
                            "failure_reason": "harness_error",
                            "materialized_compile": False,
                        }
                        for entry in by_module[module]
                    ],
                    "aggregate": {
                        "compile": False,
                        "failure_reason": "harness_error",
                        "replacement_count": 0,
                        "attempts": [],
                        "materialization_compile_count": 0,
                    },
                    "timings": {"elapsed_seconds": 0, "recording_seconds": 0, "materialization_seconds": 0},
                    "error": str(error),
                }
                write_json_atomic(closure_module_path(module), record)
            completed += 1
            aggregate = record.get("aggregate", {})
            print(
                f"[{completed}/{len(pending)}] {module} "
                f"aggregate={'passed' if aggregate.get('compile') else 'failed' if aggregate.get('compile') is False else 'skipped'} "
                f"outcomes={counts(item.get('terminal_outcome') for item in record.get('occurrences', []))}"
            )
    summary = write_closure_summary(revision)
    print(
        f"closure summary: {summary['modules']} modules, "
        f"{summary['materialized_replacements']} materialized replacements"
    )


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

    closure_parser = subparsers.add_parser(
        "closure", help="run one resumable passive-recording/materialization pass per module"
    )
    closure_parser.add_argument("--module", dest="modules", action="append", default=[])
    closure_parser.add_argument(
        "--limit", type=int, help="limit the number of modules processed"
    )
    closure_parser.add_argument(
        "--jobs", type=int, default=max(1, min(4, os.cpu_count() or 1))
    )
    closure_parser.add_argument("--timeout", type=int, default=600)
    closure_parser.add_argument("--resume", action="store_true")
    closure_parser.add_argument("--keep-copies", action="store_true")
    closure_parser.set_defaults(function=closure)

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
