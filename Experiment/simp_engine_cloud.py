#!/usr/bin/env python3
"""Inventory, shard, materialize, and reduce the full schema-19 Mathlib run."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import traceback
from typing import Any

import check_simp_engine_pin as pin
import simp_engine_inventory as coverage


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = coverage.MATHLIB
REPORT_SCHEMA = 1
CERTIFICATE_SCHEMA = 19
ENGINE_ID = {
    "leanVersion": pin.LEAN_VERSION,
    "leanCommit": pin.LEAN_COMMIT,
    "certificateSchema": CERTIFICATE_SCHEMA,
}

SOURCE_RECORD = re.compile(
    r"SIMP_ENGINE_SOURCE_RECORD occurrence=(\S+) certificate=(\S+) "
    r"deferredSubjects=(\d+) subjects=(\d+)"
)
SOURCE_REPLAY = re.compile(r"SIMP_ENGINE_SOURCE_REPLAY occurrence=(\S+)")
SOURCE_UNSUCCESSFUL = re.compile(
    r"SIMP_ENGINE_SOURCE_UNSUCCESSFUL occurrence=(\S+)"
)
SOURCE_RECORDER_FAILURE = re.compile(
    r"SIMP_ENGINE_SOURCE_RECORDER_FAILURE occurrence=(\S+)"
)

ALLOWED_TERMINALS = {
    "materialized",
    "deferred_simproc",
    "deferred_custom_discharger",
    "deferred_simproc_and_custom_discharger",
    "not_executed",
    "unsuccessful_execution",
}
DEFERRED_REASONS_BY_TERMINAL = {
    "deferred_simproc": {"simproc"},
    "deferred_custom_discharger": {"custom_discharger"},
    "deferred_simproc_and_custom_discharger": {
        "simproc", "custom_discharger"
    },
}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def json_write(path: Path, value: Any, *, pretty: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(
        value,
        indent=2 if pretty else None,
        separators=None if pretty else (",", ":"),
        sort_keys=True,
    )
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(encoded + "\n", encoding="utf-8")
    temporary.replace(path)


def command_output(command: list[str], *, timeout: int = 60) -> str:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(f"command failed ({completed.returncode}): {command}\n{completed.stdout}")
    return completed.stdout.strip()


def current_commit() -> str:
    return command_output(["git", "rev-parse", "HEAD"])


def assert_repository(expected_commit: str | None, allow_dirty: bool) -> str:
    commit = current_commit()
    if expected_commit and commit != expected_commit:
        raise RuntimeError(f"moving_ref: expected {expected_commit}, checked out {commit}")
    if not allow_dirty:
        for command in (
            ["git", "diff", "--quiet", "HEAD", "--"],
            ["git", "diff", "--cached", "--quiet", "HEAD", "--"],
        ):
            completed = subprocess.run(command, cwd=ROOT, check=False)
            if completed.returncode:
                raise RuntimeError("dirty_tracked_worktree")
    return commit


def mathlib_commit() -> str:
    return command_output(["git", "-C", str(MATHLIB), "rev-parse", "HEAD"])


def module_shard(module: str, shard_count: int) -> int:
    if shard_count <= 0:
        raise ValueError("shard count must be positive")
    return int.from_bytes(hashlib.sha256(module.encode()).digest()[:8], "big") % shard_count


def module_paths(prefix: str, maximum: int | None) -> list[Path]:
    paths = sorted((MATHLIB / "Mathlib").rglob("*.lean"))
    if prefix:
        paths = [path for path in paths if path.relative_to(MATHLIB).as_posix().startswith(prefix)]
    if maximum is not None:
        paths = paths[:maximum]
    if not paths:
        raise RuntimeError(f"inventory selected no Mathlib modules for prefix {prefix!r}")
    return paths


def inventory_batch(paths: list[Path], timeout: int) -> tuple[list[dict[str, Any]], list[str]]:
    relative_paths = [str(path.relative_to(ROOT)) for path in paths]
    command = [
        "lake",
        "env",
        "lean",
        "--run",
        "Experiment/SimpEngineInventory.lean",
        *relative_paths,
    ]
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"syntax inventory batch timed out after {timeout}s") from error
    if completed.returncode:
        diagnostics = completed.stderr.splitlines()
        excerpt = "\n".join(diagnostics[-200:])
        raise RuntimeError(
            f"syntax inventory batch failed ({completed.returncode}) with "
            f"{len(diagnostics)} diagnostics:\n"
            f"{excerpt}"
        )
    entries: list[dict[str, Any]] = []
    fallbacks: list[str] = []
    for line in completed.stdout.splitlines():
        if line.startswith("{"):
            entries.append(json.loads(line))
        elif line.startswith("SIMP_ENGINE_INVENTORY_FULL_FALLBACK file="):
            fallbacks.append(line.split("=", 1)[1])
    return entries, fallbacks


def build_inventory(args: argparse.Namespace) -> None:
    commit = assert_repository(args.commit or None, args.allow_dirty)
    paths = module_paths(args.module_prefix, args.max_modules)
    path_to_module = {
        path.resolve(): path.relative_to(MATHLIB).as_posix() for path in paths
    }
    by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    fallback_modules: set[str] = set()
    for start in range(0, len(paths), args.batch_size):
        batch = paths[start : start + args.batch_size]
        raw_entries, fallback_files = inventory_batch(batch, args.timeout)
        for fallback_file in fallback_files:
            fallback_path = Path(fallback_file)
            if not fallback_path.is_absolute():
                fallback_path = ROOT / fallback_path
            module = path_to_module.get(fallback_path.resolve())
            if module is None:
                raise RuntimeError(f"inventory fallback returned an unrequested file: {fallback_path}")
            fallback_modules.add(module)
        for raw in raw_entries:
            raw_path = Path(raw.pop("file"))
            if not raw_path.is_absolute():
                raw_path = ROOT / raw_path
            module = path_to_module.get(raw_path.resolve())
            if module is None:
                raise RuntimeError(f"inventory returned an unrequested file: {raw_path}")
            if raw["kind"] not in coverage.SUPPORTED_KINDS:
                continue
            raw["module"] = module
            raw["id"] = coverage.occurrence_id(
                module, int(raw["startByte"]), int(raw["endByte"])
            )
            by_module[module].append(raw)
        print(f"inventory: parsed {min(start + args.batch_size, len(paths))}/{len(paths)} modules")
    modules: list[dict[str, Any]] = []
    seen_occurrences: dict[str, dict[str, Any]] = {}
    duplicate_syntax_records = 0
    nested_occurrences = 0
    for path in paths:
        module = path.relative_to(MATHLIB).as_posix()
        source = path.read_bytes()
        by_range: dict[tuple[int, int], dict[str, Any]] = {}
        for occurrence in by_module[module]:
            byte_range = (int(occurrence["startByte"]), int(occurrence["endByte"]))
            previous = by_range.get(byte_range)
            if previous is not None and previous != occurrence:
                raise RuntimeError(
                    f"conflicting inventory records at {module}:{byte_range}: "
                    f"{previous} != {occurrence}"
                )
            if previous is not None:
                duplicate_syntax_records += 1
            by_range[byte_range] = occurrence
        occurrences = sorted(
            by_range.values(),
            key=lambda item: (int(item["startByte"]), -int(item["endByte"])),
        )
        containing_ends: list[int] = []
        previous_start: int | None = None
        for occurrence in occurrences:
            coverage.validate_occurrence(source, occurrence)
            if occurrence.get("syntaxKind") != "Lean.Parser.Tactic.simp":
                raise RuntimeError(
                    f"unexpected syntax kind at {module}:{occurrence['line']}: "
                    f"{occurrence.get('syntaxKind')}"
                )
            start = int(occurrence["startByte"])
            end = int(occurrence["endByte"])
            if start == previous_start:
                raise RuntimeError(f"conflicting occurrence starts in {module} at {start}")
            previous_start = start
            while containing_ends and start >= containing_ends[-1]:
                containing_ends.pop()
            if containing_ends:
                if end > containing_ends[-1]:
                    raise RuntimeError(
                        f"partially overlapping occurrences in {module} at {start}:{end}"
                    )
                nested_occurrences += 1
            containing_ends.append(end)
            occurrence_id = str(occurrence["id"])
            if occurrence_id in seen_occurrences:
                raise RuntimeError(
                    f"duplicate occurrence id: {occurrence_id}: "
                    f"{seen_occurrences[occurrence_id]} != {occurrence}"
                )
            seen_occurrences[occurrence_id] = occurrence
        modules.append(
            {
                "module": module,
                "moduleHash": sha256(module.encode()),
                "sourceHash": sha256(source),
                "occurrences": occurrences,
            }
        )
    inventory = {
        "reportSchema": REPORT_SCHEMA,
        "kind": "simp_engine_inventory",
        "commit": commit,
        "mathlibCommit": mathlib_commit(),
        "engine": ENGINE_ID,
        "modulePrefix": args.module_prefix,
        "generatedAt": utc_now(),
        "moduleFileCount": len(modules),
        "inventoriedModuleCount": sum(bool(item["occurrences"]) for item in modules),
        "occurrenceCount": len(seen_occurrences),
        "nestedOccurrenceCount": nested_occurrences,
        "duplicateSyntaxRecords": duplicate_syntax_records,
        "fullFrontendFallbacks": sorted(fallback_modules),
        "modules": modules,
    }
    json_write(Path(args.output), inventory)
    print(
        "schema-19 cloud inventory: "
        f"{inventory['moduleFileCount']} files, "
        f"{inventory['inventoriedModuleCount']} modules with occurrences, "
        f"{inventory['occurrenceCount']} occurrences, "
        f"{nested_occurrences} nested, "
        f"{len(fallback_modules)} full-frontend fallbacks, "
        f"{duplicate_syntax_records} duplicate syntax records collapsed"
    )


def dynamic_library() -> str:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=600,
        check=False,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    return json.loads(command_output(["lake", "query", "ExplicitLean:shared", "--json"]))


def reset_output_directory(path: Path) -> None:
    resolved = path.resolve()
    if resolved in {ROOT.resolve(), Path("/")} or len(resolved.parts) < 4:
        raise RuntimeError(f"unsafe output directory: {resolved}")
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True)


def recording_copy(
    output: Path,
    module: str,
    source: bytes,
    occurrences: list[dict[str, Any]],
    certificate_directory: Path,
) -> Path:
    def replacement(occurrence: dict[str, Any]) -> str:
        occurrence_id = str(occurrence["id"])
        return (
            f"simp_engine_source_recording {json.dumps(occurrence_id)} "
            f"{json.dumps(str(certificate_directory.resolve()))}"
        )

    source = coverage.rewrite_simp_heads(source, occurrences, replacement)
    source = coverage.inject_import(source, "ExplicitLean.SimpEngine.Source")
    destination = output / "work" / "record" / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def materialized_copy(
    output: Path,
    stage: str,
    module: str,
    source: bytes,
    occurrences: list[dict[str, Any]],
    certificate_sources: dict[str, list[str]],
    selected: set[str],
) -> Path:
    chosen = [
        occurrence for occurrence in occurrences
        if str(occurrence["id"]) in selected
    ]

    def replacement(occurrence: dict[str, Any]) -> str:
        occurrence_id = str(occurrence["id"])
        terms = sorted(set(certificate_sources[occurrence_id]))
        if not terms:
            raise RuntimeError(f"selected occurrence has no certificate: {occurrence_id}")
        array_source = coverage.lean_string_array_source(
            terms, int(occurrence["column"])
        )
        return (
            f"simp_engine_apply {json.dumps(occurrence_id)} "
            f"(certificates := {array_source})"
        )

    source = coverage.rewrite_simp_heads(source, chosen, replacement)
    source = coverage.inject_import(source, "ExplicitLean.SimpEngine.Source")
    destination = output / "work" / stage / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def log_path(output: Path, stage: str, module: str) -> Path:
    path = output / "logs" / stage / Path(module).with_suffix(".log")
    path.parent.mkdir(parents=True, exist_ok=True)
    return path


def compile_copy(
    destination: Path, dynlib: str, timeout: int, destination_log: Path
) -> tuple[int, str, float]:
    command = coverage.lean_command(destination)
    command.insert(3, f"--load-dynlib={dynlib}")
    code, output, duration = coverage.run(command, timeout=timeout)
    destination_log.write_text(output, encoding="utf-8")
    return code, output, duration


def deferred_reasons(certificate: dict[str, Any]) -> set[str]:
    result: set[str] = set()
    for subject in certificate.get("subjects", []):
        simproc_trace = subject.get("simprocs", {})
        if isinstance(simproc_trace, dict) and simproc_trace.get("order"):
            result.add("simproc")
        deferred = subject.get("deferred")
        if deferred is None:
            continue
        recognized = False
        if deferred == "customDischarger":
            result.add("custom_discharger")
            recognized = True
        elif isinstance(deferred, dict):
            if (
                "customDischarger" in deferred
                or "simprocAndCustomDischarger" in deferred
            ):
                result.add("custom_discharger")
                recognized = True
            if "simproc" in deferred or "simprocAndCustomDischarger" in deferred:
                result.add("simproc")
                recognized = True
        if not recognized:
            result.add("unknown")
    return result


def occurrence_shell(occurrence: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": occurrence["id"],
        "kind": occurrence["kind"],
        "line": occurrence["line"],
        "column": occurrence["column"],
        "successfulExecutions": 0,
        "unsuccessfulExecutions": 0,
        "replayedExecutions": 0,
        "deferredReasons": [],
        "certificates": [],
        "terminal": "unclassified",
    }


def failed_module_result(
    module_entry: dict[str, Any], terminal: str, message: str
) -> dict[str, Any]:
    occurrences = []
    for occurrence in module_entry["occurrences"]:
        item = occurrence_shell(occurrence)
        item["terminal"] = terminal
        occurrences.append(item)
    return {
        "module": module_entry["module"],
        "sourceHash": module_entry["sourceHash"],
        "recording": None,
        "materialization": None,
        "occurrences": occurrences,
        "errors": [message],
    }


def module_has_failure(result: dict[str, Any]) -> bool:
    if result.get("errors"):
        return True
    return any(
        occurrence.get("terminal") not in ALLOWED_TERMINALS
        for occurrence in result.get("occurrences", [])
    )


def compile_exhausted_capacity(exit_code: int) -> bool:
    """Recognize process death caused by the worker's memory/capacity limit."""
    return exit_code in {-9, 137}


def preserve_failure_source(output: Path, stage: str, module: str, source: Path) -> None:
    destination = output / "failures" / stage / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def cleanup_module_work(output: Path, module: str) -> None:
    work = output / "work"
    if not work.is_dir():
        return
    for stage in work.iterdir():
        relative = module.removesuffix(".lean") if stage.name == "certificates" else module
        target = stage / relative
        if target.is_dir():
            shutil.rmtree(target)
        elif target.exists():
            target.unlink()


def classify_deferred(reasons: set[str]) -> str:
    if reasons == {"simproc"}:
        return "deferred_simproc"
    if reasons == {"custom_discharger"}:
        return "deferred_custom_discharger"
    if reasons == {"simproc", "custom_discharger"}:
        return "deferred_simproc_and_custom_discharger"
    return "recording_failure"


def classify_occurrence_executions(
    executions: list[dict[str, Any]], unsuccessful_executions: int
) -> str | None:
    """Return a terminal outcome, or `None` when every execution can materialize."""
    if executions:
        reasons = {
            reason
            for execution in executions
            for reason in execution["deferredReasons"]
        }
        return classify_deferred(reasons) if reasons else None
    if unsuccessful_executions:
        return "unsuccessful_execution"
    return "not_executed"


def compile_diagnostic_group(
    output: Path,
    module: str,
    source: bytes,
    occurrences: list[dict[str, Any]],
    certificate_sources: dict[str, list[str]],
    selected: set[str],
    dynlib: str,
    timeout: int,
    ordinal: int,
) -> bool:
    stage = f"bisect-{ordinal}"
    copy = materialized_copy(
        output, stage, module, source, occurrences, certificate_sources, selected
    )
    code, compile_output, _ = compile_copy(
        copy, dynlib, timeout, log_path(output, "bisect", f"{ordinal}-{module}")
    )
    actual = Counter(SOURCE_REPLAY.findall(compile_output))
    expected = Counter(
        {
            occurrence_id: len(certificate_sources[occurrence_id])
            for occurrence_id in selected
        }
    )
    return code != 0 or actual != expected


def bisect_materialization_failure(
    output: Path,
    module: str,
    source: bytes,
    occurrences: list[dict[str, Any]],
    certificate_sources: dict[str, list[str]],
    selected: set[str],
    dynlib: str,
    timeout: int,
    budget: int = 12,
) -> list[list[str]]:
    queue = [sorted(selected)]
    leaves: list[list[str]] = []
    compiles = 0
    while queue and compiles < budget:
        group = queue.pop(0)
        if len(group) <= 1:
            leaves.append(group)
            continue
        midpoint = len(group) // 2
        failing_children: list[list[str]] = []
        for child in (group[:midpoint], group[midpoint:]):
            if compiles >= budget:
                break
            compiles += 1
            if compile_diagnostic_group(
                output,
                module,
                source,
                occurrences,
                certificate_sources,
                set(child),
                dynlib,
                timeout,
                compiles,
            ):
                failing_children.append(child)
        if not failing_children:
            leaves.append(group)
        else:
            queue.extend(failing_children)
    leaves.extend(queue)
    return leaves


def process_module(
    output: Path,
    module_entry: dict[str, Any],
    dynlib: str,
    timeout: int,
) -> dict[str, Any]:
    module = str(module_entry["module"])
    occurrences = list(module_entry["occurrences"])
    known = {str(occurrence["id"]) for occurrence in occurrences}
    source_path = MATHLIB / module
    source = source_path.read_bytes()
    if sha256(source) != module_entry["sourceHash"]:
        return failed_module_result(module_entry, "harness_failure", "source_hash_mismatch")
    certificate_directory = output / "work" / "certificates" / module.removesuffix(".lean")
    recorded = recording_copy(output, module, source, occurrences, certificate_directory)
    record_code, record_output, record_duration = compile_copy(
        recorded, dynlib, timeout, log_path(output, "record", module)
    )
    recorder_failures = Counter(SOURCE_RECORDER_FAILURE.findall(record_output))
    unknown_recorder = set(recorder_failures) - known
    if record_code or recorder_failures or unknown_recorder:
        preserve_failure_source(output, "record", module, recorded)
        capacity_failure = compile_exhausted_capacity(record_code)
        message = (
            f"recording_{'capacity_failure' if capacity_failure else 'compile_failure'}="
            f"exit={record_code}; "
            f"recorder_failures={dict(recorder_failures)}; unknown={sorted(unknown_recorder)}"
        )
        result = failed_module_result(
            module_entry,
            "capacity_failure" if capacity_failure else "recording_failure",
            message,
        )
        result["recording"] = {
            "exitCode": record_code,
            "seconds": record_duration,
            "log": str(log_path(output, "record", module).relative_to(output)),
        }
        return result

    unsuccessful = Counter(SOURCE_UNSUCCESSFUL.findall(record_output))
    unknown_unsuccessful = set(unsuccessful) - known
    successes: dict[str, list[dict[str, Any]]] = defaultdict(list)
    certificate_sources: dict[str, list[str]] = defaultdict(list)
    errors: list[str] = []
    for match in SOURCE_RECORD.finditer(record_output):
        occurrence_id, certificate_name, deferred_count, subject_count = match.groups()
        if occurrence_id not in known:
            errors.append(f"unknown_recorded_occurrence:{occurrence_id}")
            continue
        certificate_path = Path(certificate_name)
        if not certificate_path.is_file():
            errors.append(f"missing_certificate:{occurrence_id}:{certificate_path}")
            continue
        encoded = certificate_path.read_text(encoding="utf-8")
        try:
            certificate = json.loads(encoded)
        except json.JSONDecodeError as error:
            errors.append(f"invalid_certificate_json:{occurrence_id}:{error}")
            continue
        if certificate.get("engine") != ENGINE_ID:
            errors.append(f"certificate_engine_mismatch:{occurrence_id}")
        reasons = deferred_reasons(certificate)
        if int(deferred_count) != sum(
            subject.get("deferred") is not None for subject in certificate.get("subjects", [])
        ):
            errors.append(f"deferred_count_mismatch:{occurrence_id}")
        if int(subject_count) != len(certificate.get("subjects", [])):
            errors.append(f"subject_count_mismatch:{occurrence_id}")
        certificate_sources[occurrence_id].append(encoded)
        successes[occurrence_id].append(
            {
                "sha256": sha256(encoded.encode()),
                "initialState": certificate.get("initialState"),
                "finalState": certificate.get("finalState"),
                "deferredReasons": sorted(reasons),
            }
        )
    if unknown_unsuccessful:
        errors.append(f"unknown_unsuccessful_occurrences:{sorted(unknown_unsuccessful)}")
    if errors:
        preserve_failure_source(output, "record", module, recorded)
        result = failed_module_result(module_entry, "recording_failure", ";".join(errors))
        result["recording"] = {
            "exitCode": record_code,
            "seconds": record_duration,
            "log": str(log_path(output, "record", module).relative_to(output)),
        }
        return result

    occurrence_results: dict[str, dict[str, Any]] = {
        str(occurrence["id"]): occurrence_shell(occurrence) for occurrence in occurrences
    }
    selected: set[str] = set()
    for occurrence_id, occurrence_result in occurrence_results.items():
        execution_records = successes[occurrence_id]
        occurrence_result["successfulExecutions"] = len(execution_records)
        occurrence_result["unsuccessfulExecutions"] = unsuccessful[occurrence_id]
        occurrence_result["certificates"] = execution_records
        all_reasons = {
            reason
            for execution in execution_records
            for reason in execution["deferredReasons"]
        }
        occurrence_result["deferredReasons"] = sorted(all_reasons)
        terminal = classify_occurrence_executions(
            execution_records, unsuccessful[occurrence_id]
        )
        if terminal is None:
            selected.add(occurrence_id)
        else:
            occurrence_result["terminal"] = terminal

    materialization: dict[str, Any] | None = None
    if selected:
        materialized = materialized_copy(
            output,
            "materialized",
            module,
            source,
            occurrences,
            certificate_sources,
            selected,
        )
        materialize_code, materialize_output, materialize_duration = compile_copy(
            materialized, dynlib, timeout, log_path(output, "materialized", module)
        )
        actual = Counter(SOURCE_REPLAY.findall(materialize_output))
        expected = Counter(
            {
                occurrence_id: len(certificate_sources[occurrence_id])
                for occurrence_id in selected
            }
        )
        unknown_replay = set(actual) - selected
        materialization = {
            "exitCode": materialize_code,
            "seconds": materialize_duration,
            "expectedExecutions": sum(expected.values()),
            "actualExecutions": sum(actual.values()),
            "log": str(log_path(output, "materialized", module).relative_to(output)),
        }
        if materialize_code == 0 and actual == expected and not unknown_replay:
            for occurrence_id in selected:
                occurrence_results[occurrence_id]["terminal"] = "materialized"
                occurrence_results[occurrence_id]["replayedExecutions"] = actual[occurrence_id]
        else:
            preserve_failure_source(output, "materialized", module, materialized)
            capacity_failure = compile_exhausted_capacity(materialize_code)
            failure_kind = (
                "materialization_capacity_failure"
                if capacity_failure else "materialization_failed"
            )
            errors.append(
                f"{failure_kind}:exit={materialize_code}:expected={dict(expected)}:"
                f"actual={dict(actual)}:unknown={sorted(unknown_replay)}"
            )
            if not capacity_failure:
                materialization["failingGroups"] = bisect_materialization_failure(
                    output,
                    module,
                    source,
                    occurrences,
                    certificate_sources,
                    selected,
                    dynlib,
                    timeout,
                )
            for occurrence_id in selected:
                occurrence_results[occurrence_id]["terminal"] = (
                    "capacity_failure" if capacity_failure else "materialization_failure"
                )

    return {
        "module": module,
        "sourceHash": module_entry["sourceHash"],
        "recording": {
            "exitCode": record_code,
            "seconds": record_duration,
            "successfulExecutions": sum(map(len, successes.values())),
            "unsuccessfulExecutions": sum(unsuccessful.values()),
            "log": str(log_path(output, "record", module).relative_to(output)),
        },
        "materialization": materialization,
        "occurrences": list(occurrence_results.values()),
        "errors": errors,
    }


def shard_report_path(output: Path, index: int) -> Path:
    return output / "reports" / f"shard-{index:04d}.json"


def run_shard(args: argparse.Namespace) -> None:
    inventory = json.loads(Path(args.inventory).read_text(encoding="utf-8"))
    assert_repository(inventory["commit"], args.allow_dirty)
    if inventory.get("reportSchema") != REPORT_SCHEMA or inventory.get("engine") != ENGINE_ID:
        raise RuntimeError("incompatible cloud inventory")
    if mathlib_commit() != inventory["mathlibCommit"]:
        raise RuntimeError("mathlib_commit_mismatch")
    if not 0 <= args.shard_index < args.shard_count:
        raise RuntimeError("invalid shard index")
    output = Path(args.output_dir)
    reset_output_directory(output)
    assigned = [
        module
        for module in inventory["modules"]
        if module["occurrences"]
        and module_shard(module["module"], args.shard_count) == args.shard_index
    ]
    report = {
        "reportSchema": REPORT_SCHEMA,
        "kind": "simp_engine_shard",
        "commit": inventory["commit"],
        "mathlibCommit": inventory["mathlibCommit"],
        "engine": ENGINE_ID,
        "shardIndex": args.shard_index,
        "shardCount": args.shard_count,
        "startedAt": utc_now(),
        "completedAt": None,
        "complete": False,
        "stoppedAfterFailure": None,
        "assignedModuleCount": len(assigned),
        "modules": [],
        "harnessErrors": [],
    }
    report_path = shard_report_path(output, args.shard_index)
    json_write(report_path, report)
    try:
        dynlib = dynamic_library()
    except Exception as error:
        report["harnessErrors"].append(f"dynamic_library:{error}")
        report["modules"] = [
            failed_module_result(module, "harness_failure", "dynamic_library_failure")
            for module in assigned
        ]
    else:
        for ordinal, module in enumerate(assigned, start=1):
            try:
                result = process_module(output, module, dynlib, args.module_timeout)
            except Exception as error:
                failure_log = log_path(output, "harness", module["module"])
                failure_log.write_text(traceback.format_exc(), encoding="utf-8")
                result = failed_module_result(
                    module, "harness_failure", f"{type(error).__name__}:{error}"
                )
            try:
                cleanup_module_work(output, module["module"])
            except Exception as error:
                result["errors"].append(
                    f"work_cleanup_failure:{type(error).__name__}:{error}"
                )
            report["modules"].append(result)
            json_write(report_path, report)
            terminals = Counter(
                occurrence["terminal"] for occurrence in result["occurrences"]
            )
            print(
                f"shard {args.shard_index}: {ordinal}/{len(assigned)} "
                f"{module['module']} {dict(terminals)}",
                flush=True,
            )
            if args.stop_after_failure and module_has_failure(result):
                report["stoppedAfterFailure"] = module["module"]
                json_write(report_path, report)
                break
    report["complete"] = len(report["modules"]) == len(assigned)
    report["completedAt"] = utc_now()
    json_write(report_path, report)
    if (output / "work").exists():
        shutil.rmtree(output / "work")
    print(
        f"schema-19 cloud shard {args.shard_index}/{args.shard_count}: "
        f"{len(report['modules'])}/{len(assigned)} modules reported"
    )
    if report["stoppedAfterFailure"] is not None:
        raise SystemExit(1)


def find_shard_reports(directory: Path) -> list[Path]:
    return sorted(directory.rglob("shard-*.json"))


def reduce_reports(args: argparse.Namespace) -> int:
    inventory = json.loads(Path(args.inventory).read_text(encoding="utf-8"))
    assert_repository(inventory["commit"], args.allow_dirty)
    report_paths = find_shard_reports(Path(args.reports_dir))
    shard_reports = [json.loads(path.read_text(encoding="utf-8")) for path in report_paths]
    failures: list[str] = []
    if not shard_reports:
        failures.append("no_shard_reports")
        shard_count = args.shard_count or 0
    else:
        counts = {int(report.get("shardCount", -1)) for report in shard_reports}
        if len(counts) != 1:
            failures.append(f"inconsistent_shard_counts:{sorted(counts)}")
        shard_count = next(iter(counts)) if len(counts) == 1 else (args.shard_count or 0)
    if args.shard_count is not None and shard_count != args.shard_count:
        failures.append(f"unexpected_shard_count:{shard_count}:{args.shard_count}")
    reports_by_index: dict[int, dict[str, Any]] = {}
    for report in shard_reports:
        index = int(report.get("shardIndex", -1))
        if index in reports_by_index:
            failures.append(f"duplicate_shard:{index}")
        reports_by_index[index] = report
        for field in ("reportSchema", "commit", "mathlibCommit", "engine"):
            expected = inventory[field]
            if report.get(field) != expected:
                failures.append(f"shard_{index}_{field}_mismatch")
        if report.get("kind") != "simp_engine_shard":
            failures.append(f"shard_{index}_kind_mismatch")
        if not report.get("complete"):
            failures.append(f"incomplete_shard:{index}")
        failures.extend(f"shard_{index}_harness:{error}" for error in report.get("harnessErrors", []))
    expected_indices = set(range(shard_count))
    if set(reports_by_index) != expected_indices:
        failures.append(
            f"shard_coverage:missing={sorted(expected_indices - set(reports_by_index))}:"
            f"extra={sorted(set(reports_by_index) - expected_indices)}"
        )

    expected_modules = {
        module["module"]: module
        for module in inventory["modules"]
        if module["occurrences"]
    }
    if inventory.get("moduleFileCount") != len(inventory.get("modules", [])):
        failures.append("inventory_module_file_count_mismatch")
    if inventory.get("inventoriedModuleCount", len(expected_modules)) != len(expected_modules):
        failures.append("inventory_module_count_mismatch")
    actual_modules: dict[str, dict[str, Any]] = {}
    for index, report in reports_by_index.items():
        expected_assigned = sum(
            module_shard(name, shard_count) == index for name in expected_modules
        )
        if report.get("assignedModuleCount", expected_assigned) != expected_assigned:
            failures.append(f"assigned_module_count_mismatch:{index}")
        for module in report.get("modules", []):
            name = module.get("module")
            if name in actual_modules:
                failures.append(f"duplicate_module:{name}")
            actual_modules[name] = module
            if name not in expected_modules:
                failures.append(f"unknown_module:{name}")
            elif module_shard(name, shard_count) != index:
                failures.append(f"wrong_shard:{name}:{index}")
    if set(actual_modules) != set(expected_modules):
        failures.append(
            f"module_coverage:missing={len(set(expected_modules) - set(actual_modules))}:"
            f"extra={len(set(actual_modules) - set(expected_modules))}"
        )

    expected_occurrences = {
        occurrence["id"]: occurrence
        for module in expected_modules.values()
        for occurrence in module["occurrences"]
    }
    if inventory.get("occurrenceCount", len(expected_occurrences)) != len(expected_occurrences):
        failures.append("inventory_occurrence_count_mismatch")
    actual_occurrences: dict[str, dict[str, Any]] = {}
    terminal_counts: Counter[str] = Counter()
    successful_executions = 0
    unsuccessful_executions = 0
    replayed_executions = 0
    for module_name, module in actual_modules.items():
        expected_module = expected_modules.get(module_name)
        if expected_module and module.get("sourceHash") != expected_module["sourceHash"]:
            failures.append(f"source_hash_mismatch:{module_name}")
        for error in module.get("errors", []):
            failures.append(f"module_error:{module_name}:{error}")
        module_successful = 0
        module_unsuccessful = 0
        module_replayed = 0
        module_materialized = 0
        for occurrence in module.get("occurrences", []):
            occurrence_id = occurrence.get("id")
            if occurrence_id in actual_occurrences:
                failures.append(f"duplicate_occurrence:{occurrence_id}")
            actual_occurrences[occurrence_id] = occurrence
            expected = expected_occurrences.get(occurrence_id)
            if expected is None:
                failures.append(f"unknown_occurrence:{occurrence_id}")
                continue
            for field in ("kind", "line", "column"):
                if occurrence.get(field) != expected[field]:
                    failures.append(f"occurrence_provenance:{occurrence_id}:{field}")
            terminal = occurrence.get("terminal", "unclassified")
            terminal_counts[terminal] += 1
            successful = int(occurrence.get("successfulExecutions", 0))
            unsuccessful = int(occurrence.get("unsuccessfulExecutions", 0))
            replayed = int(occurrence.get("replayedExecutions", 0))
            if min(successful, unsuccessful, replayed) < 0:
                failures.append(f"negative_execution_count:{occurrence_id}")
            certificates = occurrence.get("certificates", [])
            if not isinstance(certificates, list) or len(certificates) != successful:
                failures.append(f"certificate_execution_mismatch:{occurrence_id}")
                certificates = []
            certificate_reasons: set[str] = set()
            for certificate in certificates:
                if not isinstance(certificate, dict):
                    failures.append(f"invalid_certificate_report:{occurrence_id}")
                    continue
                reasons = certificate.get("deferredReasons", [])
                if not isinstance(reasons, list):
                    failures.append(f"invalid_certificate_reasons:{occurrence_id}")
                    continue
                certificate_reasons.update(map(str, reasons))
                if not certificate.get("sha256") or certificate.get("initialState") is None \
                        or certificate.get("finalState") is None:
                    failures.append(f"incomplete_certificate_report:{occurrence_id}")
            reasons = set(map(str, occurrence.get("deferredReasons", [])))
            if reasons != certificate_reasons:
                failures.append(f"deferred_reason_union_mismatch:{occurrence_id}")
            successful_executions += successful
            unsuccessful_executions += unsuccessful
            replayed_executions += replayed
            module_successful += successful
            module_unsuccessful += unsuccessful
            module_replayed += replayed
            if terminal == "materialized":
                module_materialized += successful
                if successful == 0 or replayed != successful or reasons:
                    failures.append(f"materialized_execution_mismatch:{occurrence_id}")
            elif terminal == "unsuccessful_execution" and (successful != 0 or unsuccessful == 0):
                failures.append(f"unsuccessful_execution_mismatch:{occurrence_id}")
            elif terminal == "not_executed" and (successful != 0 or unsuccessful != 0):
                failures.append(f"not_executed_mismatch:{occurrence_id}")
            elif terminal in DEFERRED_REASONS_BY_TERMINAL:
                if successful == 0 or replayed != 0 or reasons != DEFERRED_REASONS_BY_TERMINAL[terminal]:
                    failures.append(f"deferred_execution_mismatch:{occurrence_id}")
            elif terminal not in ALLOWED_TERMINALS:
                failures.append(f"failure_terminal:{occurrence_id}:{terminal}")
            if terminal != "materialized" and replayed != 0:
                failures.append(f"unexpected_replay:{occurrence_id}:{terminal}")
        recording = module.get("recording")
        if not isinstance(recording, dict) or recording.get("exitCode") != 0:
            failures.append(f"recording_summary_mismatch:{module_name}")
        elif recording.get("successfulExecutions") != module_successful or \
                recording.get("unsuccessfulExecutions") != module_unsuccessful:
            failures.append(f"recording_count_mismatch:{module_name}")
        materialization = module.get("materialization")
        if module_materialized:
            if not isinstance(materialization, dict) or materialization.get("exitCode") != 0:
                failures.append(f"materialization_summary_mismatch:{module_name}")
            elif materialization.get("expectedExecutions") != module_materialized or \
                    materialization.get("actualExecutions") != module_replayed:
                failures.append(f"materialization_count_mismatch:{module_name}")
        elif materialization is not None:
            failures.append(f"unexpected_materialization_summary:{module_name}")
    if set(actual_occurrences) != set(expected_occurrences):
        failures.append(
            f"occurrence_coverage:missing={len(set(expected_occurrences) - set(actual_occurrences))}:"
            f"extra={len(set(actual_occurrences) - set(expected_occurrences))}"
        )

    summary = {
        "reportSchema": REPORT_SCHEMA,
        "kind": "simp_engine_closure",
        "commit": inventory["commit"],
        "mathlibCommit": inventory["mathlibCommit"],
        "engine": inventory["engine"],
        "generatedAt": utc_now(),
        "passed": not failures,
        "shardCount": shard_count,
        "moduleFileCount": inventory["moduleFileCount"],
        "inventoriedModuleCount": len(expected_modules),
        "occurrenceCount": len(expected_occurrences),
        "reportedOccurrenceCount": len(actual_occurrences),
        "terminalCounts": dict(sorted(terminal_counts.items())),
        "successfulExecutions": successful_executions,
        "unsuccessfulExecutions": unsuccessful_executions,
        "replayedExecutions": replayed_executions,
        "failureCount": len(failures),
        "failures": failures,
    }
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    json_write(output / "simp-engine-closure.json", summary, pretty=True)
    markdown = [
        "# Schema-17 full Mathlib closure",
        "",
        f"- Commit: `{summary['commit']}`",
        f"- Mathlib: `{summary['mathlibCommit']}`",
        f"- Result: **{'PASS' if summary['passed'] else 'FAIL'}**",
        f"- Modules with occurrences: {summary['inventoriedModuleCount']}",
        f"- Occurrences: {summary['reportedOccurrenceCount']} / {summary['occurrenceCount']}",
        f"- Successful executions: {successful_executions}",
        f"- Replayed executions: {replayed_executions}",
        f"- Unsuccessful executions: {unsuccessful_executions}",
        "",
        "## Terminal outcomes",
        "",
    ]
    markdown.extend(f"- `{key}`: {value}" for key, value in sorted(terminal_counts.items()))
    if failures:
        markdown.extend(["", "## Failures", ""])
        markdown.extend(f"- `{failure}`" for failure in failures[:500])
        if len(failures) > 500:
            markdown.append(f"- ... {len(failures) - 500} more (see JSON)")
    (output / "simp-engine-closure.md").write_text(
        "\n".join(markdown) + "\n", encoding="utf-8"
    )
    print(
        "schema-19 full closure: "
        f"{len(actual_occurrences)}/{len(expected_occurrences)} occurrences, "
        f"terminals={dict(terminal_counts)}, failures={len(failures)}"
    )
    return 0 if not failures else 1


def print_matrix(args: argparse.Namespace) -> None:
    if args.shard_count <= 0 or args.shard_count > 256:
        raise RuntimeError("shard count must be between 1 and 256")
    print(json.dumps(list(range(args.shard_count)), separators=(",", ":")))


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    subparsers = result.add_subparsers(dest="command", required=True)

    inventory = subparsers.add_parser("inventory")
    inventory.add_argument("--output", required=True)
    inventory.add_argument("--commit", default="")
    inventory.add_argument("--module-prefix", default="Mathlib/")
    inventory.add_argument("--max-modules", type=int)
    inventory.add_argument("--batch-size", type=int, default=2048)
    inventory.add_argument("--timeout", type=int, default=3600)
    inventory.add_argument("--allow-dirty", action="store_true")
    inventory.set_defaults(function=build_inventory)

    matrix = subparsers.add_parser("matrix")
    matrix.add_argument("--shard-count", type=int, required=True)
    matrix.set_defaults(function=print_matrix)

    shard = subparsers.add_parser("shard")
    shard.add_argument("--inventory", required=True)
    shard.add_argument("--shard-index", type=int, required=True)
    shard.add_argument("--shard-count", type=int, required=True)
    shard.add_argument("--output-dir", required=True)
    shard.add_argument("--module-timeout", type=int, default=900)
    shard.add_argument("--stop-after-failure", action="store_true")
    shard.add_argument("--allow-dirty", action="store_true")
    shard.set_defaults(function=run_shard)

    reduce_parser = subparsers.add_parser("reduce")
    reduce_parser.add_argument("--inventory", required=True)
    reduce_parser.add_argument("--reports-dir", required=True)
    reduce_parser.add_argument("--output-dir", required=True)
    reduce_parser.add_argument("--shard-count", type=int)
    reduce_parser.add_argument("--allow-dirty", action="store_true")
    reduce_parser.set_defaults(function=lambda args: sys.exit(reduce_reports(args)))
    return result


def main() -> None:
    args = parser().parse_args()
    args.function(args)


if __name__ == "__main__":
    main()
