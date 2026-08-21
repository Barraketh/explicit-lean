#!/usr/bin/env python3
"""Focused F3 check for the smallest closed `first` owner fallback."""

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
    path.write_bytes(coverage.inject_import(source))


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
    owner = entries[0]
    owner_id = coverage.first_owner_id(owner)
    source = FIXTURE.read_bytes()
    if source[owner["ownerStartByte"] : owner["ownerEndByte"]].decode("utf-8") != owner[
        "ownerSource"
    ]:
        raise RuntimeError("first-owner inventory range is stale")

    coverage.OUTPUT = ROOT / ".lake" / "f3-first-owner"
    coverage.RESULTS = coverage.OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = coverage.OUTPUT / "aggregate-results"
    record = coverage.passive_module_recording(
        FIXTURE_MODULE,
        entries,
        timeout=180,
        keep_copy=True,
        source_path=FIXTURE,
    )
    if not record["compile"] or record["compile_count"] != 1:
        raise RuntimeError(f"first-owner passive recording failed: {record!r}")
    reports = {
        report.get("occurrenceId"): report
        for report in record.get("reports", [])
        if isinstance(report.get("occurrenceId"), str)
    }
    if len(reports) != 2:
        raise RuntimeError(f"first-owner reports were not retained: {record!r}")
    dispositions = {
        tuple(execution.get("disposition") for execution in report.get("executions", []))
        for report in reports.values()
    }
    if dispositions != {("backtracked",), ("committed",)}:
        raise RuntimeError(f"unexpected first-branch dispositions: {record!r}")

    owner_reports = record.get("first_owner_reports", [])
    if len(owner_reports) != 1 or owner_reports[0].get("ownerId") != owner_id:
        raise RuntimeError(f"closed first owner proof report missing: {owner_reports!r}")
    serialized = json.dumps(owner_reports, ensure_ascii=False, sort_keys=True)
    if FORBIDDEN.search(serialized):
        raise RuntimeError("first-owner proof report contains a raw internal identity")
    owner_report = owner_reports[0]
    replacement = coverage.first_owner_replacement(source, owner, owner_report)
    if re.search(r"(?<![A-Za-z0-9_])simp(?!_)", replacement):
        raise RuntimeError(f"first-owner replacement retained ambient simp: {replacement!r}")
    materialized = coverage.replace_range_bytes(
        source,
        owner["ownerStartByte"],
        owner["ownerEndByte"],
        owner["ownerSource"],
        replacement,
    )
    materialized_path = coverage.OUTPUT / "materialized" / "first-owner.lean"
    write_copy(materialized_path, materialized)
    compiled, output = compile_copy(materialized_path)
    if not compiled:
        raise RuntimeError(f"smallest first-owner materialization failed:\n{output}")

    bad_report = dict(owner_report)
    bad_report["proof"] = "True.intro"
    bad_replacement = coverage.first_owner_replacement(source, owner, bad_report)
    mutated = coverage.replace_range_bytes(
        source,
        owner["ownerStartByte"],
        owner["ownerEndByte"],
        owner["ownerSource"],
        bad_replacement,
    )
    mutated_path = coverage.OUTPUT / "materialized" / "first-owner-mutated.lean"
    write_copy(mutated_path, mutated)
    mutated_compiled, _ = compile_copy(mutated_path)
    if mutated_compiled:
        raise RuntimeError("mutated first-owner proof unexpectedly compiled")
    print("F3 smallest closed first-owner proof fallback passed")


if __name__ == "__main__":
    main()
