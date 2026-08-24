#!/usr/bin/env python3
"""Round-trip schema-19 source and compile focused/bounded materialized modules."""

from __future__ import annotations

from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import shutil
import subprocess

import simp_engine_inventory as coverage


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / ".lake" / "simp-engine-source"
FIXTURES = (
    ("focused", ROOT / "Experiment/SimpEngineSourceFixture.lean",
     "Experiment/SimpEngineSourceFixture.lean", True),
    ("drop-right", coverage.MATHLIB / "Mathlib/Data/List/DropRight.lean",
     "Mathlib/Data/List/DropRight.lean", False),
    ("eq-to-hom", coverage.MATHLIB / "Mathlib/CategoryTheory/EqToHom.lean",
     "Mathlib/CategoryTheory/EqToHom.lean", False),
    ("eventually-const", coverage.MATHLIB / "Mathlib/Order/Filter/EventuallyConst.lean",
     "Mathlib/Order/Filter/EventuallyConst.lean", False),
    ("polynomial-reverse", coverage.MATHLIB / "Mathlib/Algebra/Polynomial/Reverse.lean",
     "Mathlib/Algebra/Polynomial/Reverse.lean", False),
    ("ring-inj-surj", coverage.MATHLIB / "Mathlib/Algebra/Ring/InjSurj.lean",
     "Mathlib/Algebra/Ring/InjSurj.lean", False),
    ("pfunctor-m", coverage.MATHLIB / "Mathlib/Data/PFunctor/Multivariate/M.lean",
     "Mathlib/Data/PFunctor/Multivariate/M.lean", False),
    ("ordinal-notation", coverage.MATHLIB / "Mathlib/SetTheory/Ordinal/Notation.lean",
     "Mathlib/SetTheory/Ordinal/Notation.lean", False),
    ("process-stopping", coverage.MATHLIB / "Mathlib/Probability/Process/Stopping.lean",
     "Mathlib/Probability/Process/Stopping.lean", False),
    ("surjective-on-stalks",
     coverage.MATHLIB / "Mathlib/AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean",
     "Mathlib/AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean", False),
    ("multiset-functor", coverage.MATHLIB / "Mathlib/Data/Multiset/Functor.lean",
     "Mathlib/Data/Multiset/Functor.lean", False),
    ("vector3", coverage.MATHLIB / "Mathlib/Data/Vector3.lean",
     "Mathlib/Data/Vector3.lean", False),
    ("mv-polynomial-height",
     coverage.MATHLIB / "Mathlib/NumberTheory/Height/MvPolynomial.lean",
     "Mathlib/NumberTheory/Height/MvPolynomial.lean", False),
    ("finite-index-representations",
     coverage.MATHLIB / "Mathlib/RepresentationTheory/FiniteIndex.lean",
     "Mathlib/RepresentationTheory/FiniteIndex.lean", False),
    ("topology-constructions",
     coverage.MATHLIB / "Mathlib/Topology/Constructions.lean",
     "Mathlib/Topology/Constructions.lean", False),
    ("l2-space",
     coverage.MATHLIB / "Mathlib/MeasureTheory/Function/L2Space.lean",
     "Mathlib/MeasureTheory/Function/L2Space.lean", False),
)
RECORD = re.compile(
    r"SIMP_ENGINE_SOURCE_RECORD occurrence=(\S+) certificate=(\S+) "
    r"deferredSubjects=(\d+) subjects=(\d+)"
)
REPLAY = re.compile(r"SIMP_ENGINE_SOURCE_REPLAY occurrence=(\S+)")
UNSUCCESSFUL = re.compile(r"SIMP_ENGINE_SOURCE_UNSUCCESSFUL occurrence=(\S+)")
RECORDER_FAILURE = re.compile(r"SIMP_ENGINE_SOURCE_RECORDER_FAILURE occurrence=(\S+)")


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


def inventory(path: Path, module: str) -> tuple[bytes, list[dict[str, object]]]:
    source = path.read_bytes()
    entries = [
        entry for entry in coverage.syntax_inventory_file(path, module, 180)
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    if not entries:
        raise RuntimeError(f"source fixture has no supported simp calls: {module}")
    return source, entries


def recording_copy(
    key: str, module: str, source: bytes, entries: list[dict[str, object]],
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
    key: str, module: str, source: bytes, entries: list[dict[str, object]],
    certificates: dict[str, list[Path]], selected: set[str],
) -> Path:
    chosen = [entry for entry in entries if str(entry["id"]) in selected]

    def replacement(entry: dict[str, object]) -> str:
        occurrence = str(entry["id"])
        terms = sorted({path.read_text(encoding="utf-8") for path in certificates[occurrence]})
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
    if "Mathlib" not in destination.parts and "Experiment" in destination.parts:
        experiment_index = destination.parts.index("Experiment")
        # Recording and materialized copies must have the same logical module
        # name so Lean's generated private declaration names remain stable.
        command[-1:-1] = ["-R", str(Path(*destination.parts[:experiment_index]))]
    code, output, _ = coverage.run(command, timeout=timeout)
    destination.with_suffix(".log").write_text(output, encoding="utf-8")
    return code, output


def check_engine_mismatch(
    module: str, source: bytes, entries: list[dict[str, object]],
    certificates: dict[str, list[Path]], dynlib: str,
) -> None:
    occurrence = next(
        str(entry["id"]) for entry in entries
        if len(certificates.get(str(entry["id"]), [])) == 1
    )
    payload = json.loads(certificates[occurrence][0].read_text(encoding="utf-8"))
    payload["engine"]["certificateSchema"] += 1
    mutation = OUTPUT / "mutations" / f"{occurrence}.json"
    mutation.parent.mkdir(parents=True, exist_ok=True)
    mutation.write_text(
        json.dumps(payload, separators=(",", ":"), sort_keys=True), encoding="utf-8"
    )
    materialized = materialized_copy(
        "engine-mismatch", module, source, entries,
        {occurrence: [mutation]}, {occurrence},
    )
    code, output = compile_copy(materialized, dynlib, timeout=600)
    if code == 0 or "source_certificate_engine_mismatch" not in output:
        raise RuntimeError(
            "mutated source certificate was not rejected by engine identity; "
            f"see {materialized.with_suffix('.log')}"
        )


def main() -> None:
    dynlib = dynamic_library()
    occurrence_total = 0
    materialized_total = 0
    deferred_total = 0
    unsuccessful_total = 0
    execution_total = 0
    for key, path, module, require_total in FIXTURES:
        source, entries = inventory(path, module)
        known = {str(entry["id"]) for entry in entries}
        certificate_directory = OUTPUT / "certificates" / key
        if certificate_directory.exists():
            shutil.rmtree(certificate_directory)
        recorded = recording_copy(key, module, source, entries, certificate_directory)
        code, output = compile_copy(recorded, dynlib, timeout=600)
        if code:
            raise RuntimeError(f"source recording failed; see {recorded.with_suffix('.log')}")
        outcomes: dict[str, list[int]] = defaultdict(list)
        certificates: dict[str, list[Path]] = defaultdict(list)
        for match in RECORD.finditer(output):
            occurrence, certificate, deferred, _subjects = match.groups()
            if occurrence not in known:
                raise RuntimeError(f"unknown occurrence in source log: {occurrence}")
            certificate_path = Path(certificate)
            if not certificate_path.is_file():
                raise RuntimeError(f"certificate source was not written: {certificate_path}")
            outcomes[occurrence].append(int(deferred))
            certificates[occurrence].append(certificate_path)
        unsuccessful = Counter(match.group(1) for match in UNSUCCESSFUL.finditer(output))
        unknown_unsuccessful = set(unsuccessful) - known
        if unknown_unsuccessful:
            raise RuntimeError(
                f"unknown unsuccessful occurrence in source log: {unknown_unsuccessful}"
            )
        recorder_failures = set(RECORDER_FAILURE.findall(output))
        if recorder_failures:
            raise RuntimeError(f"source recorder failures: {recorder_failures}")
        selected = {
            occurrence for occurrence, executions in outcomes.items()
            if executions and all(deferred == 0 for deferred in executions)
        }
        deferred = {
            occurrence for occurrence, executions in outcomes.items()
            if any(subjects > 0 for subjects in executions)
        }
        not_executed = known - outcomes.keys() - unsuccessful.keys()
        terminal = selected | deferred | set(unsuccessful)
        if require_total and (terminal != known or not_executed):
            raise RuntimeError(
                f"focused source fixture was not total: selected={selected}, "
                f"deferred={deferred}, unsuccessful={unsuccessful}, "
                f"not_executed={not_executed}"
            )
        if key == "focused":
            check_engine_mismatch(module, source, entries, certificates, dynlib)
        materialized = materialized_copy(
            key, module, source, entries, certificates, selected
        )
        code, output = compile_copy(materialized, dynlib, timeout=600)
        if code:
            raise RuntimeError(
                f"materialized module failed; see {materialized.with_suffix('.log')}"
            )
        actual = Counter(match.group(1) for match in REPLAY.finditer(output))
        expected = Counter({occurrence: len(outcomes[occurrence]) for occurrence in selected})
        if actual != expected:
            raise RuntimeError(
                f"materialized execution mismatch in {module}: expected {expected}, got {actual}"
            )
        occurrence_total += len(known)
        materialized_total += len(selected)
        deferred_total += len(deferred)
        unsuccessful_total += sum(unsuccessful.values())
        execution_total += sum(expected.values())
    print(
        "schema-19 source materialization: "
        f"{len(FIXTURES)} modules, {occurrence_total} occurrences, "
        f"{materialized_total} materialized, {deferred_total} deferred, "
        f"{unsuccessful_total} unsuccessful, {execution_total} executions, "
        "engine mutation rejected: ok"
    )


if __name__ == "__main__":
    main()
