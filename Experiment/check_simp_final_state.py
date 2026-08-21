#!/usr/bin/env python3
"""Check that target certificates preserve `simp`'s exact final goal state."""

from __future__ import annotations

import simp_coverage as coverage


FIXTURE = coverage.ROOT / "Experiment" / "SimpFinalStateProbe.lean"
MODULE = "Experiment/SimpFinalStateProbe.lean"


def main() -> None:
    entries = coverage.syntax_inventory_file(FIXTURE, MODULE, 180)
    entries = [entry for entry in entries if entry["kind"] in coverage.SUPPORTED_KINDS]
    if len(entries) != 1:
        raise RuntimeError(f"expected one final-state occurrence: {entries!r}")

    output = coverage.ROOT / ".lake" / "simp-final-state-probe"
    original_output = coverage.OUTPUT
    original_results = coverage.RESULTS
    original_aggregate_results = coverage.AGGREGATE_RESULTS
    coverage.OUTPUT = output
    coverage.RESULTS = output / "results"
    coverage.AGGREGATE_RESULTS = output / "aggregate-results"
    try:
        record = coverage.run_closure_module(
            MODULE,
            entries,
            "fixture-rev",
            180,
            keep_copy=True,
            source_path=FIXTURE,
        )
    finally:
        coverage.OUTPUT = original_output
        coverage.RESULTS = original_results
        coverage.AGGREGATE_RESULTS = original_aggregate_results

    if record.get("recording", {}).get("compile") is not True:
        raise RuntimeError(f"passive final-state recording failed: {record!r}")
    occurrence = record.get("occurrences", [None])[0]
    if not isinstance(occurrence, dict) or occurrence.get("terminal_outcome") != "materialized":
        raise RuntimeError(f"final-state replacement did not materialize: {record!r}")
    execution = occurrence.get("execution_summaries", [None])[0]
    if not isinstance(execution, dict) or execution.get("closesGoal") is not False:
        raise RuntimeError(f"simp-only execution did not retain its open goal: {record!r}")
    candidate = occurrence.get("candidate")
    if not isinstance(candidate, dict) or "eq_self" in candidate.get("replacement", ""):
        raise RuntimeError(f"final-state replacement gained an ambient closure rule: {record!r}")
    if not candidate.get("replacement", "").startswith("simp_explicit leave_open ["):
        raise RuntimeError(f"final-state replacement lost its open-state marker: {record!r}")
    if record.get("aggregate", {}).get("closure_complete") is not True:
        raise RuntimeError(f"final-state fixture did not close as a module: {record!r}")
    print("simp final-state checks passed")


if __name__ == "__main__":
    main()
