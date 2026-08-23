#!/usr/bin/env python3
"""Record bounded modules once, then replay every wholly non-deferred occurrence."""

from __future__ import annotations

from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import subprocess

import simp_engine_inventory as coverage


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / ".lake" / "simp-engine-replay"
MODULES = (
    "Mathlib/Data/List/DropRight.lean",
    "Mathlib/CategoryTheory/EqToHom.lean",
)
RECORDING = re.compile(
    r"SIMP_ENGINE_RECORDING occurrence=(\S+).* deferredSubjects=(\d+) subjects=(\d+)"
)
REPLAY = re.compile(r"SIMP_ENGINE_REPLAY occurrence=(\S+) branches=")


def dynamic_library() -> str:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
    )
    if query.returncode:
        raise RuntimeError(query.stdout + query.stderr)
    return json.loads(query.stdout.strip())


def inventory(module: str) -> tuple[bytes, list[dict[str, object]]]:
    source_path = coverage.MATHLIB / module
    source = source_path.read_bytes()
    entries = [
        entry for entry in coverage.syntax_inventory_file(source_path, module, 180)
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    if not entries:
        raise RuntimeError(f"bounded production module has no supported simp calls: {module}")
    return source, entries


def instrument(
    module: str,
    source: bytes,
    entries: list[dict[str, object]],
    tactic: str,
    selected: set[str] | None,
) -> Path:
    for entry in sorted(entries, key=lambda item: item["startByte"], reverse=True):
        occurrence = str(entry["id"])
        if selected is not None and occurrence not in selected:
            continue
        original = str(entry["source"])
        replacement = f"{tactic} {json.dumps(occurrence)}" + original[len("simp") :]
        source = coverage.replace_bytes(source, entry, replacement)
    imported = (
        "ExplicitLean.SimpEngine.Recording"
        if tactic == "simp_engine_recording_id"
        else "ExplicitLean.SimpEngine.Replay"
    )
    source = coverage.inject_import(source, imported)
    stage = "record" if tactic == "simp_engine_recording_id" else "replay"
    destination = OUTPUT / stage / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def compile_copy(destination: Path, dynlib: str, timeout: int) -> tuple[int, str]:
    command = coverage.lean_command(destination)
    command.insert(3, f"--load-dynlib={dynlib}")
    code, output, _ = coverage.run(command, timeout=timeout)
    destination.with_suffix(".log").write_text(output, encoding="utf-8")
    return code, output


def main() -> None:
    dynlib = dynamic_library()
    occurrence_total = 0
    selected_total = 0
    deferred_total = 0
    not_executed_total = 0
    replay_execution_total = 0
    for module in MODULES:
        source, entries = inventory(module)
        known = {str(entry["id"]) for entry in entries}
        recording_copy = instrument(
            module, source, entries, "simp_engine_recording_id", selected=None
        )
        code, recording_output = compile_copy(recording_copy, dynlib, timeout=600)
        if code:
            raise RuntimeError(
                f"recording pass failed in {module}; see {recording_copy.with_suffix('.log')}"
            )
        executions: dict[str, list[int]] = defaultdict(list)
        for match in RECORDING.finditer(recording_output):
            occurrence, deferred_subjects, _subjects = match.groups()
            if occurrence not in known:
                raise RuntimeError(f"unknown occurrence id in recording log: {occurrence}")
            executions[occurrence].append(int(deferred_subjects))
        selected = {
            occurrence for occurrence, outcomes in executions.items()
            if outcomes and all(deferred == 0 for deferred in outcomes)
        }
        deferred = {
            occurrence for occurrence, outcomes in executions.items()
            if any(deferred_subjects > 0 for deferred_subjects in outcomes)
        }
        not_executed = known - executions.keys()
        replay_copy = instrument(
            module, source, entries, "simp_engine_replay_id", selected=selected
        )
        code, replay_output = compile_copy(replay_copy, dynlib, timeout=600)
        if code:
            raise RuntimeError(
                f"replay pass failed in {module}; see {replay_copy.with_suffix('.log')}"
            )
        actual = Counter(match.group(1) for match in REPLAY.finditer(replay_output))
        expected = Counter({occurrence: len(executions[occurrence]) for occurrence in selected})
        if actual != expected:
            raise RuntimeError(
                f"replay execution mismatch in {module}: expected {expected}, got {actual}"
            )
        occurrence_total += len(known)
        selected_total += len(selected)
        deferred_total += len(deferred)
        not_executed_total += len(not_executed)
        replay_execution_total += sum(expected.values())
    print(
        "schema-16 production replay: "
        f"{len(MODULES)} modules, {occurrence_total} occurrences, "
        f"{selected_total} replayed, {deferred_total} simproc/custom deferred, "
        f"{not_executed_total} not executed, {replay_execution_total} executions: ok"
    )


if __name__ == "__main__":
    main()
