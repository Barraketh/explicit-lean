#!/usr/bin/env python3
"""Focused O5 check for operational source ownership inside `first`."""

from __future__ import annotations

import json
from pathlib import Path
import re

import simp_coverage as coverage


ROOT = coverage.ROOT
FIXTURE = ROOT / "Experiment" / "FirstOwnerProbe.lean"
FIXTURE_MODULE = "Experiment/FirstOwnerProbe.lean"
FORBIDDEN = re.compile(r"FVarId|Syntax\.mk|Expr\.mvar|mvarId|\?m\.[0-9]+")


def compile_copy(path: Path) -> tuple[bool, str]:
    code, output, _ = coverage.run(coverage.lean_command(path), timeout=180)
    return code == 0, output


def write_copy(path: Path, source: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    # apply_closure_candidates already injects ExplicitLean.SimpExplicit.
    path.write_bytes(source)


def main() -> None:
    original_code, original_output, _ = coverage.run(
        ["lake", "env", "lean", str(FIXTURE)], timeout=180
    )
    if original_code != 0:
        raise RuntimeError(f"first-owner fixture does not compile:\n{original_output}")

    entries = coverage.syntax_inventory_file(FIXTURE, FIXTURE_MODULE, 180)
    entries = [entry for entry in entries if entry["kind"] in coverage.SUPPORTED_KINDS]
    if len(entries) != 2:
        raise RuntimeError(f"expected two first-owner simp occurrences: {entries!r}")
    if any(
        entry.get("ownerKind") != "first" or entry.get("ownerRole") != "first_branch"
        for entry in entries
    ):
        raise RuntimeError(f"first-owner syntax metadata changed: {entries!r}")
    owner_ranges = {
        (entry.get("ownerStartByte"), entry.get("ownerEndByte")) for entry in entries
    }
    if len(owner_ranges) != 1:
        raise RuntimeError(f"expected one smallest enclosing first owner: {entries!r}")

    coverage.OUTPUT = ROOT / ".lake" / "f3-first-owner"
    coverage.RESULTS = coverage.OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = coverage.OUTPUT / "aggregate-results"
    record = coverage.run_closure_module(
        FIXTURE_MODULE,
        entries,
        coverage.mathlib_revision(),
        180,
        keep_copy=True,
        source_path=FIXTURE,
    )
    if not record["recording"]["compile"]:
        raise RuntimeError(f"first-owner passive recording failed: {record!r}")
    if record["recording"].get("first_owner_reports") != []:
        raise RuntimeError("first-owner proof report unexpectedly survived")
    serialized = json.dumps(record, ensure_ascii=False, sort_keys=True)
    if FORBIDDEN.search(serialized):
        raise RuntimeError("first-owner report contains a raw internal identity")

    occurrences = {occurrence["id"]: occurrence for occurrence in record["occurrences"]}
    if len(occurrences) != 2:
        raise RuntimeError(f"first-owner closure did not retain both occurrences: {record!r}")
    outcomes = {occurrence["terminal_outcome"] for occurrence in occurrences.values()}
    if outcomes != {"materialized", "attempted_backtracked"}:
        raise RuntimeError(f"unexpected first-branch closure outcomes: {record!r}")
    committed = [
        occurrence
        for occurrence in occurrences.values()
        if occurrence["terminal_outcome"] == "materialized"
    ]
    if len(committed) != 1:
        raise RuntimeError(f"expected one committed first branch: {record!r}")
    candidate = committed[0].get("candidate")
    if not isinstance(candidate, dict) or candidate.get("kind") != "occurrence":
        raise RuntimeError(f"committed first branch was not an occurrence candidate: {record!r}")
    committed_entry = next(entry for entry in entries if entry["id"] == committed[0]["id"])
    if (
        candidate.get("startByte") != committed_entry["startByte"]
        or candidate.get("endByte") != committed_entry["endByte"]
        or candidate.get("expected") != committed_entry["source"]
    ):
        raise RuntimeError(f"first branch candidate escaped its occurrence range: {candidate!r}")
    if record["aggregate"].get("closure_complete") is not True:
        raise RuntimeError(f"operational first-owner closure did not complete: {record!r}")

    source = FIXTURE.read_bytes()
    materialized = coverage.apply_closure_candidates(source, [candidate])
    materialized_path = coverage.OUTPUT / "materialized" / "first-owner.lean"
    write_copy(materialized_path, materialized)
    compiled, output = compile_copy(materialized_path)
    if not compiled:
        raise RuntimeError(f"operational first-owner materialization failed:\n{output}")
    if "exact " in candidate.get("replacement", ""):
        raise RuntimeError("first-owner candidate exported an enclosing proof")

    mutated_candidate = dict(candidate)
    mutated_candidate["replacement"] = "exact True.intro"
    mutated = coverage.apply_closure_candidates(source, [mutated_candidate])
    mutated_path = coverage.OUTPUT / "materialized" / "first-owner-mutated.lean"
    write_copy(mutated_path, mutated)
    mutated_compiled, _ = compile_copy(mutated_path)
    if mutated_compiled:
        raise RuntimeError("mutated first-owner operational candidate unexpectedly compiled")
    print("O5 first-owner operational source ownership passed")


if __name__ == "__main__":
    main()
