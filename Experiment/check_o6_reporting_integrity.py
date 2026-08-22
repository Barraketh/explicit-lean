#!/usr/bin/env python3
"""Regression for O6 binder-safe reports and scope-less commitment."""

from __future__ import annotations

import simp_coverage as coverage


MODULE = "Mathlib/Algebra/Algebra/Subalgebra/Tower.lean"
SCOPELESS_ID = "f27035b0710b8604"
OUTPUT = coverage.ROOT / ".lake" / "o6-reporting-integrity"


def main() -> None:
    coverage.OUTPUT = OUTPUT
    coverage.RESULTS = OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = OUTPUT / "aggregate-results"

    entries = [
        entry
        for entry in coverage.syntax_inventory_file(
            coverage.MATHLIB / MODULE, MODULE, 600
        )
        if entry.get("kind") in coverage.SUPPORTED_KINDS
    ]
    by_id = {entry["id"]: entry for entry in entries}
    if len(entries) != 5 or SCOPELESS_ID not in by_id:
        raise RuntimeError(
            f"Tower reporting inventory changed: count={len(entries)}, ids={sorted(by_id)!r}"
        )

    record = coverage.run_closure_module(
        MODULE,
        entries,
        coverage.mathlib_revision(),
        180,
        keep_copy=True,
    )
    recording = record.get("recording") or {}
    validation = record.get("recording_validation") or {}
    if recording.get("compile") is not True or recording.get("compile_count") != 1:
        raise RuntimeError(
            "Tower reporting compile changed: "
            f"compile={recording.get('compile')!r}, "
            f"count={recording.get('compile_count')!r}"
        )
    if validation.get("malformed_result_ids"):
        raise RuntimeError(
            f"scope-less result remained malformed: {validation['malformed_result_ids']!r}"
        )

    occurrences = {item["id"]: item for item in record.get("occurrences", [])}
    occurrence = occurrences.get(SCOPELESS_ID) or {}
    report = occurrence.get("report") or {}
    executions = report.get("executions") or []
    execution = executions[0] if len(executions) == 1 else {}
    if (
        occurrence.get("terminal_outcome") != "materialized"
        or occurrence.get("failure_reason") is not None
        or occurrence.get("dispositions") != ["committed"]
        or report.get("bodyScopeId") is not None
        or execution.get("disposition") is not None
        or not report.get("acceptedCertificate")
        or report.get("legacyCertificate") is not None
    ):
        raise RuntimeError(
            "scope-less accepted execution did not materialize: "
            f"outcome={occurrence.get('terminal_outcome')!r}, "
            f"reason={occurrence.get('failure_reason')!r}, "
            f"effective={occurrence.get('dispositions')!r}, "
            f"body_scope={report.get('bodyScopeId')!r}, "
            f"raw_disposition={execution.get('disposition')!r}"
        )

    print("O6 binder-safe reporting and scope-less commitment passed")


if __name__ == "__main__":
    main()
