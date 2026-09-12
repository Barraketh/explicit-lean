#!/usr/bin/env python3
"""Compile the focused boundary-state replacement probe."""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
LOCATION_PROBE = "Experiment/SimpEngineBoundaryProbe.lean"
APPLY_PROBE = "Experiment/SimpEngineBoundaryApply.lean"
TRUST_PROBE = "Experiment/SimpEngineBoundaryTrust.lean"
METADATA_PROBE = "Experiment/SimpEngineBoundaryMetadataDifferential.lean"
APPLY_ROOT_MODULE = "ExplicitLean.SimpEngine.Boundary.Tactic"
APPLY_SOURCE_MODULES = (
    "ExplicitLean.SimpEngine.Boundary.Apply",
    "ExplicitLean.SimpEngine.Boundary.ModuleDataObservation",
    "ExplicitLean.SimpEngine.Boundary.Selector",
    "ExplicitLean.SimpEngine.Boundary.Tactic",
)


IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import\s+"
    r"((?:all\s+)?[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*$"
)
PROBE_MARKER = "SIMP_ENGINE_BOUNDARY_PROBE"
SELF_TEST_MARKER = "SIMP_ENGINE_BOUNDARY_COMPARATOR_SELF_TEST ok"
PROBE_MARKER_RE = re.compile(
    r"^SIMP_ENGINE_BOUNDARY_PROBE "
    r"outcome=(?P<outcome>transported|closed_true|closed_false) "
    r"evidence=(?P<evidence>equality|defeq|unchanged) "
    r"equivalent=(?P<equivalent>true|false)$"
)


def module_source(module: str, lean_prefix: Path) -> Path:
    relative = Path(*module.split(".")).with_suffix(".lean")
    candidates = [ROOT / relative, lean_prefix / "src" / "lean" / relative]
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise RuntimeError(f"cannot resolve imported module source: {module}")


def imports_of(source: Path) -> list[str]:
    imports: list[str] = []
    text = re.sub(r"/-.*?-/", "", source.read_text(), flags=re.DOTALL)
    for line in text.splitlines():
        line = line.split("--", 1)[0]
        match = IMPORT_RE.match(line)
        if match:
            modules = match.group(1).split()
            if modules and modules[0] == "all":
                modules = modules[1:]
            imports.extend(modules)
    return imports


def assert_apply_path_isolated() -> None:
    prefix_query = run(["lean", "--print-prefix"], 30)
    if prefix_query.returncode:
        raise RuntimeError(prefix_query.stdout)
    lean_prefix = Path(prefix_query.stdout.strip())
    pending = [APPLY_ROOT_MODULE]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        if module.startswith(("Lean.Meta.Tactic.Simp", "Lean.Elab.Tactic.Simp")):
            raise RuntimeError(
                f"apply-only import closure reaches simplifier module: {module}"
            )
        pending.extend(imports_of(module_source(module, lean_prefix)))

    forbidden_symbols = (
        "mkSimpContext",
        "simpGoal",
        "Meta.simp",
        "Simp.",
        "Simprocs",
        "DischargeWrapper",
    )
    apply_source = "\n".join(
        module_source(module, lean_prefix).read_text()
        for module in APPLY_SOURCE_MODULES
    )
    present = [symbol for symbol in forbidden_symbols if symbol in apply_source]
    if present:
        raise RuntimeError(f"apply-only source contains forbidden symbols: {present}")


def run(command: list[str], timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def compile_probe(dylib: str, source: str) -> str:
    probe = run(
        ["lake", "env", "lean", f"--load-dynlib={dylib}", source],
        300,
    )
    if probe.returncode:
        raise RuntimeError(probe.stdout)
    return probe.stdout


def query_json_string(output: str, label: str) -> str:
    """Read Lake's JSON result after any replayed dependency diagnostics."""
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if not lines:
        raise RuntimeError(f"{label} returned no JSON result")
    value = json.loads(lines[-1])
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"{label} returned an invalid value: {value!r}")
    return value


def parse_probe_markers(output: str) -> list[dict[str, str]]:
    markers = [
        line.strip() for line in output.splitlines() if PROBE_MARKER in line
    ]
    if len(markers) != 19:
        raise RuntimeError(
            f"expected 19 boundary markers, found {len(markers)}\n{output}"
        )
    parsed: list[dict[str, str]] = []
    for marker in markers:
        match = PROBE_MARKER_RE.fullmatch(marker)
        if match is None:
            raise RuntimeError(f"malformed boundary marker: {marker!r}\n{output}")
        parsed.append(match.groupdict())
    return parsed


def main() -> None:
    assert_apply_path_isolated()
    build = run(["lake", "build", "ExplicitLean:shared"], 300)
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = run(["lake", "query", "ExplicitLean:shared", "--json"], 30)
    if query.returncode:
        raise RuntimeError(query.stdout)
    dylib = query_json_string(query.stdout, "lake query ExplicitLean:shared")
    location_output = compile_probe(dylib, LOCATION_PROBE)
    if location_output.count(SELF_TEST_MARKER) != 1:
        raise RuntimeError(
            f"expected exactly one comparator self-test marker\n{location_output}"
        )
    parsed_markers = parse_probe_markers(location_output)
    failed = [
        fields
        for fields in parsed_markers
        if fields.get("equivalent") != "true"
    ]
    if failed:
        raise RuntimeError(
            "boundary comparison reported a non-equivalent result:\n"
            + "\n".join(str(fields) for fields in failed)
        )
    outcomes = {
        fields.get("outcome") for fields in parsed_markers
    }
    if outcomes != {"transported", "closed_true", "closed_false"}:
        raise RuntimeError(f"unexpected boundary outcomes: {outcomes}\n{location_output}")
    evidence = {
        fields.get("evidence") for fields in parsed_markers
    }
    if evidence != {"equality", "defeq", "unchanged"}:
        raise RuntimeError(f"unexpected boundary evidence: {evidence}\n{location_output}")

    apply_output = compile_probe(dylib, APPLY_PROBE)
    if apply_output.count("SIMP_ENGINE_BOUNDARY_APPLY_ONLY ok") != 1:
        raise RuntimeError(f"missing apply-only marker\n{apply_output}")
    trust_output = compile_probe(dylib, TRUST_PROBE)
    if trust_output.count("SIMP_ENGINE_BOUNDARY_TRUST") != 1:
        raise RuntimeError(f"missing declaration-trust marker\n{trust_output}")
    metadata_output = compile_probe(dylib, METADATA_PROBE)
    metadata_marker = (
        "BOUNDARY_METADATA_DIFFERENTIAL "
        "symbolFrequency=true sineQuaNon=true fullObserver=true "
        "missingRejected=true duplicateRejected=true cachePure=true"
    )
    if metadata_output.count(metadata_marker) != 1:
        raise RuntimeError(f"missing metadata differential marker\n{metadata_output}")
    print("boundary prototype: isolated apply, location matrix, trust, and metadata: ok")


if __name__ == "__main__":
    main()
