#!/usr/bin/env python3
"""Targeted source integration gate for the reduceCtorEq semantic tranche.

This is intentionally a small, independent harness.  It shares only the
syntax-aware inventory/rewrite/compile helpers with the broad source gate and
uses a private scratch tree so the two gates cannot overwrite one another.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import shutil
import subprocess

import simp_engine_inventory as coverage


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / ".lake" / "simp-engine-ctor-source"

# These are the four modules selected from the full histogram. The occurrence
# counts and source results below are locked to the reviewed baseline.
FIXTURES = (
    (
        "sum-interval",
        coverage.MATHLIB / "Mathlib/Data/Sum/Interval.lean",
        "Mathlib/Data/Sum/Interval.lean",
        23,
    ),
    (
        "finsupp-option",
        coverage.MATHLIB / "Mathlib/Data/Finsupp/Option.lean",
        "Mathlib/Data/Finsupp/Option.lean",
        24,
    ),
    (
        "lie-classical",
        coverage.MATHLIB / "Mathlib/Algebra/Lie/Classical.lean",
        "Mathlib/Algebra/Lie/Classical.lean",
        21,
    ),
    (
        "root-system-g2",
        coverage.MATHLIB / "Mathlib/LinearAlgebra/RootSystem/Finite/G2.lean",
        "Mathlib/LinearAlgebra/RootSystem/Finite/G2.lean",
        41,
    ),
)

RECORD = re.compile(
    r"SIMP_ENGINE_SOURCE_RECORD occurrence=(\S+) certificate=(\S+) "
    r"deferredSubjects=(\d+) subjects=(\d+)"
)
REPLAY = re.compile(r"SIMP_ENGINE_SOURCE_REPLAY occurrence=(\S+)")
UNSUCCESSFUL = re.compile(r"SIMP_ENGINE_SOURCE_UNSUCCESSFUL occurrence=(\S+)")
RECORDER_FAILURE = re.compile(
    r"SIMP_ENGINE_SOURCE_RECORDER_FAILURE occurrence=(\S+)"
)

RESULT_DISPOSITIONS = {"done", "visit", "continueSome"}

EXPECTED_TOTALS = {
    "occurrences": 109,
    "materialized": 67,
    "deferred": 42,
    "unsuccessful": 0,
    "replayExecutions": 73,
    "ctorCommittedResults": 41,
    "ctorSemanticCandidates": 41,
}

# occurrence, materialized, deferred, unsuccessful, replay executions,
# committed reduceCtorEq results, committed constructor semantic candidates
EXPECTED_MODULE_TOTALS = {
    "Mathlib/Data/Sum/Interval.lean": (23, 5, 18, 0, 5, 32, 32),
    "Mathlib/Data/Finsupp/Option.lean": (24, 18, 6, 0, 20, 1, 1),
    "Mathlib/Algebra/Lie/Classical.lean": (21, 20, 1, 0, 24, 8, 8),
    "Mathlib/LinearAlgebra/RootSystem/Finite/G2.lean": (41, 24, 17, 0, 24, 0, 0),
}


def dynamic_library() -> str:
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    if query.returncode:
        raise RuntimeError(query.stdout + query.stderr)
    return json.loads(query.stdout.strip())


def inventory(path: Path, module: str, expected: int) -> tuple[bytes, list[dict[str, object]]]:
    source = path.read_bytes()
    entries = [
        entry
        for entry in coverage.syntax_inventory_file(path, module, 600)
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    if len(entries) != expected:
        raise RuntimeError(
            f"syntax inventory changed for {module}: expected {expected}, "
            f"got {len(entries)}"
        )
    return source, entries


def recording_copy(
    key: str,
    module: str,
    source: bytes,
    entries: list[dict[str, object]],
    certificate_directory: Path,
) -> Path:
    def replacement(entry: dict[str, object]) -> str:
        occurrence = str(entry["id"])
        return (
            f"simp_engine_source_recording {json.dumps(occurrence)} "
            f"{json.dumps(str(certificate_directory))}"
        )

    source = coverage.rewrite_simp_heads(source, entries, replacement)
    source = coverage.inject_import(source, "ExplicitLean.SimpEngine.Source")
    destination = OUTPUT / "record" / key / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def materialized_copy(
    key: str,
    module: str,
    source: bytes,
    entries: list[dict[str, object]],
    certificates: dict[str, list[Path]],
    selected: set[str],
) -> Path:
    chosen = [entry for entry in entries if str(entry["id"]) in selected]

    def replacement(entry: dict[str, object]) -> str:
        occurrence = str(entry["id"])
        terms = sorted(
            {path.read_text(encoding="utf-8") for path in certificates[occurrence]}
        )
        if not terms:
            raise RuntimeError(f"selected occurrence has no certificate source: {occurrence}")
        array_source = coverage.lean_string_array_source(
            terms, int(entry["column"])
        )
        return (
            f"simp_engine_apply {json.dumps(occurrence)} "
            f"(certificates := {array_source})"
        )

    source = coverage.rewrite_simp_heads(source, chosen, replacement)
    source = coverage.inject_import(source, "ExplicitLean.SimpEngine.Source")
    destination = OUTPUT / "materialized" / key / module
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def compile_copy(destination: Path, dynlib: str, timeout: int) -> tuple[int, str]:
    command = coverage.lean_command(destination)
    command.insert(3, f"--load-dynlib={dynlib}")
    code, output, _duration = coverage.run(command, timeout=timeout)
    destination.with_suffix(".log").write_text(output, encoding="utf-8")
    return code, output


def name_components(value: object) -> list[str]:
    """Validate a serialized Lean Name and return display components."""
    if not isinstance(value, list):
        raise ValueError(f"simproc/candidate name is not an array: {value!r}")
    result: list[str] = []
    for component in value:
        if (
            not isinstance(component, list)
            or len(component) != 2
            or component[0] not in {"str", "num"}
        ):
            raise ValueError(f"invalid name component: {component!r}")
        if component[0] == "str":
            if not isinstance(component[1], str):
                raise ValueError(f"invalid string name component: {component!r}")
            result.append(component[1])
        else:
            if (
                not isinstance(component[1], int)
                or isinstance(component[1], bool)
                or component[1] < 0
            ):
                raise ValueError(f"invalid numeric name component: {component!r}")
            result.append(f"#{component[1]}")
    return result


def is_reduce_ctor_eq(value: object) -> bool:
    return name_components(value) == ["reduceCtorEq"]


def decoded_simproc_observations(subject: dict[str, object]) -> list[dict[str, object]]:
    """Decode and validate one compressed simproc dictionary/order trace."""
    trace = subject.get("simprocs")
    if not isinstance(trace, dict):
        raise ValueError("subject simproc trace is not an object")
    dictionary = trace.get("dictionary")
    order = trace.get("order")
    if not isinstance(dictionary, list) or not isinstance(order, list):
        raise ValueError("subject simproc dictionary/order is not an array")
    for observation in dictionary:
        if not isinstance(observation, dict):
            raise ValueError("simproc dictionary entry is not an object")
        # Validate every dictionary name, including entries not reached by the
        # order, so malformed compressed data cannot be silently ignored.
        name_components(observation.get("name"))
    result: list[dict[str, object]] = []
    for index in order:
        if (
            not isinstance(index, int)
            or isinstance(index, bool)
            or not 0 <= index < len(dictionary)
        ):
            raise ValueError(f"invalid simproc dictionary index: {index!r}")
        result.append(dictionary[index])
    return result


def reduce_ctor_counts(certificate: dict[str, object]) -> tuple[int, int]:
    """Return (committed result observations, semantic candidate events).

    Both counts retain multiplicity and come from rollback-aware certificate
    state, so calls made only by failed speculative candidates are absent.
    Candidate events are counted across all subjects, including certificates
    whose source execution was deferred for some other operation.
    """
    subjects = certificate.get("subjects")
    if not isinstance(subjects, list):
        raise ValueError("certificate subjects is not an array")
    committed = 0
    candidates = 0
    for subject in subjects:
        if not isinstance(subject, dict):
            raise ValueError("certificate subject is not an object")
        for observation in decoded_simproc_observations(subject):
            if is_reduce_ctor_eq(observation.get("name")):
                disposition = observation.get("stepDisposition")
                if disposition in RESULT_DISPOSITIONS:
                    committed += 1
        program = subject.get("program")
        if not isinstance(program, dict):
            raise ValueError("subject program is not an object")
        events = program.get("events")
        if not isinstance(events, list):
            raise ValueError("subject program events is not an array")
        for event in events:
            if not isinstance(event, dict):
                raise ValueError("program event is not an object")
            operation = event.get("operation")
            if not isinstance(operation, dict):
                raise ValueError("program event operation is not an object")
            semantic = operation.get("semanticSimproc")
            if semantic is None:
                continue
            if not isinstance(semantic, dict):
                raise ValueError("semantic simproc operation is not an object")
            fold = semantic.get("fold")
            if not isinstance(fold, dict):
                raise ValueError("semantic simproc fold is not an object")
            fold_candidates = fold.get("candidates")
            if not isinstance(fold_candidates, list):
                raise ValueError("semantic simproc candidates is not an array")
            for candidate in fold_candidates:
                if not isinstance(candidate, dict):
                    raise ValueError("semantic simproc candidate is not an object")
                if is_reduce_ctor_eq(candidate.get("declaration")):
                    semantics = candidate.get("semantics")
                    if (
                        not isinstance(semantics, dict)
                        or "constructorDisjoint" not in semantics
                    ):
                        raise ValueError(
                            "reduceCtorEq candidate lacks constructorDisjoint semantics"
                        )
                    candidates += 1
    return committed, candidates


def parse_recording(
    module: str,
    entries: list[dict[str, object]],
    certificate_directory: Path,
    output: str,
) -> tuple[dict[str, list[int]], dict[str, list[Path]], Counter[str]]:
    known = {str(entry["id"]) for entry in entries}
    outcomes: dict[str, list[int]] = defaultdict(list)
    certificates: dict[str, list[Path]] = defaultdict(list)
    recorded_paths: list[Path] = []
    for match in RECORD.finditer(output):
        occurrence, certificate, deferred, subjects = match.groups()
        if occurrence not in known:
            raise RuntimeError(f"unknown occurrence in source log for {module}: {occurrence}")
        certificate_path = Path(certificate)
        if not certificate_path.is_file():
            raise RuntimeError(f"certificate source was not written: {certificate_path}")
        try:
            payload = json.loads(certificate_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise RuntimeError(f"invalid certificate source: {certificate_path}") from error
        payload_subjects = payload.get("subjects")
        if not isinstance(payload_subjects, list) or len(payload_subjects) != int(subjects):
            raise RuntimeError(
                f"source log/certificate subject mismatch for {occurrence}: "
                f"log={subjects}, certificate={len(payload_subjects) if isinstance(payload_subjects, list) else payload_subjects!r}"
            )
        actual_deferred = sum(
            1
            for subject in payload_subjects
            if isinstance(subject, dict) and subject.get("deferred") is not None
        )
        if actual_deferred != int(deferred):
            raise RuntimeError(
                f"source log/certificate deferred mismatch for {occurrence}: "
                f"log={deferred}, certificate={actual_deferred}"
            )
        # Decode each emitted certificate now, including deferred executions;
        # this is also where compressed simproc traces and candidate events are
        # validated before materialization filters anything out.
        reduce_ctor_counts(payload)
        outcomes[occurrence].append(int(deferred))
        certificates[occurrence].append(certificate_path)
        recorded_paths.append(certificate_path)

    unsuccessful = Counter(match.group(1) for match in UNSUCCESSFUL.finditer(output))
    unknown_unsuccessful = set(unsuccessful) - known
    if unknown_unsuccessful:
        raise RuntimeError(
            f"unknown unsuccessful occurrence in source log for {module}: "
            f"{unknown_unsuccessful}"
        )
    recorder_failures = set(RECORDER_FAILURE.findall(output))
    if recorder_failures:
        raise RuntimeError(f"source recorder failures for {module}: {recorder_failures}")

    emitted_files = set(certificate_directory.glob("*.json"))
    if emitted_files != set(recorded_paths):
        raise RuntimeError(
            f"certificate log/file mismatch for {module}: "
            f"logged={sorted(map(str, set(recorded_paths)))}, "
            f"files={sorted(map(str, emitted_files))}"
        )
    return outcomes, certificates, unsuccessful


def main() -> None:
    # This is a dedicated exact scratch root.  Do not broaden this deletion:
    # the broad source gate uses a different directory and is out of scope.
    if OUTPUT.exists():
        shutil.rmtree(OUTPUT)
    OUTPUT.mkdir(parents=True)

    dynlib = dynamic_library()
    occurrence_total = 0
    materialized_total = 0
    deferred_total = 0
    unsuccessful_total = 0
    replay_execution_total = 0
    ctor_committed_result_total = 0
    ctor_candidate_total = 0
    module_results: list[tuple[str, int, int, int, int, int, int, int]] = []

    for key, path, module, expected_occurrences in FIXTURES:
        source, entries = inventory(path, module, expected_occurrences)
        known = {str(entry["id"]) for entry in entries}
        certificate_directory = OUTPUT / "certificates" / key
        recorded = recording_copy(
            key, module, source, entries, certificate_directory
        )
        code, _output = compile_copy(recorded, dynlib, timeout=1200)
        if code:
            raise RuntimeError(
                f"source recording failed for {module}; see {recorded.with_suffix('.log')}"
            )
        recording_output = recorded.with_suffix(".log").read_text(encoding="utf-8")
        outcomes, certificates, unsuccessful = parse_recording(
            module, entries, certificate_directory, recording_output
        )
        selected = {
            occurrence
            for occurrence, executions in outcomes.items()
            if executions and all(deferred == 0 for deferred in executions)
        }
        deferred = {
            occurrence
            for occurrence, executions in outcomes.items()
            if any(subjects > 0 for subjects in executions)
        }
        not_executed = known - outcomes.keys() - unsuccessful.keys()
        if not_executed:
            raise RuntimeError(
                f"source recording was not total for {module}: {not_executed}"
            )

        materialized = materialized_copy(
            key, module, source, entries, certificates, selected
        )
        code, materialized_output = compile_copy(
            materialized, dynlib, timeout=1200
        )
        if code:
            raise RuntimeError(
                f"materialized module failed for {module}; "
                f"see {materialized.with_suffix('.log')}"
            )
        actual_replays = Counter(
            match.group(1) for match in REPLAY.finditer(materialized_output)
        )
        expected_replays = Counter(
            {
                occurrence: len(outcomes[occurrence])
                for occurrence in selected
            }
        )
        if actual_replays != expected_replays:
            raise RuntimeError(
                f"materialized execution mismatch in {module}: "
                f"expected {expected_replays}, got {actual_replays}"
            )

        module_committed = 0
        module_candidates = 0
        for paths in certificates.values():
            for certificate_path in paths:
                payload = json.loads(certificate_path.read_text(encoding="utf-8"))
                committed, candidates = reduce_ctor_counts(payload)
                module_committed += committed
                module_candidates += candidates
        if module_candidates > module_committed:
            raise RuntimeError(
                f"reduceCtorEq candidate/use ordering failed in {module}: "
                f"candidates={module_candidates}, committed={module_committed}"
            )

        module_execution_total = sum(expected_replays.values())
        occurrence_total += len(known)
        materialized_total += len(selected)
        deferred_total += len(deferred)
        unsuccessful_total += sum(unsuccessful.values())
        replay_execution_total += module_execution_total
        ctor_committed_result_total += module_committed
        ctor_candidate_total += module_candidates
        module_results.append(
            (
                module,
                len(known),
                len(selected),
                len(deferred),
                sum(unsuccessful.values()),
                module_execution_total,
                module_committed,
                module_candidates,
            )
        )

    totals = {
        "occurrences": occurrence_total,
        "materialized": materialized_total,
        "deferred": deferred_total,
        "unsuccessful": unsuccessful_total,
        "replayExecutions": replay_execution_total,
        "ctorCommittedResults": ctor_committed_result_total,
        "ctorSemanticCandidates": ctor_candidate_total,
    }
    if totals != EXPECTED_TOTALS:
        raise RuntimeError(
            f"targeted source totals changed: expected {EXPECTED_TOTALS}, got {totals}"
        )
    actual_module_totals = {
        module: result
        for module, *result in module_results
    }
    if actual_module_totals != {
        module: list(result) for module, result in EXPECTED_MODULE_TOTALS.items()
    }:
        raise RuntimeError(
            "targeted source module totals changed: "
            f"expected {EXPECTED_MODULE_TOTALS}, got {actual_module_totals}"
        )

    modules = ",".join(module for module, *_rest in module_results)
    marker = (
        "reduceCtorEq targeted source: "
        f"modules={modules} occurrences={occurrence_total} "
        f"materialized={materialized_total} deferred={deferred_total} "
        f"unsuccessful={unsuccessful_total} replayExecutions={replay_execution_total} "
        f"ctorCommittedResults={ctor_committed_result_total} "
        f"ctorSemanticCandidates={ctor_candidate_total}: ok"
    )
    print(marker)


if __name__ == "__main__":
    main()
