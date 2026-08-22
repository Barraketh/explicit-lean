#!/usr/bin/env python3
"""Regression for instance-heavy operational premise validation in O6."""

from __future__ import annotations

import simp_coverage as coverage


OUTPUT = coverage.ROOT / ".lake" / "o6-heartbeat-budget"
SITES = {
    "Mathlib/Algebra/Algebra/Subalgebra/Unitization.lean": {
        "9725589ca802bdbe",
        "1734864b48394331",
    },
    "Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean": {
        "55537790c87186fa",
        "b4d0e7a97f301530",
    },
    "Mathlib/Algebra/BigOperators/Expect.lean": {
        "25878f9f0cbe91d5",
    },
}


def main() -> None:
    coverage.OUTPUT = OUTPUT
    coverage.RESULTS = OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = OUTPUT / "aggregate-results"

    for module, expected_ids in SITES.items():
        source = coverage.MATHLIB / module
        entries = [
            entry
            for entry in coverage.syntax_inventory_file(source, module, 600)
            if entry.get("id") in expected_ids
        ]
        observed_inventory_ids = {entry["id"] for entry in entries}
        if observed_inventory_ids != expected_ids:
            raise RuntimeError(
                f"O6 heartbeat sites moved in {module}: "
                f"expected={sorted(expected_ids)!r}, "
                f"observed={sorted(observed_inventory_ids)!r}"
            )

        recording = coverage.passive_module_recording(
            module,
            entries,
            timeout=180,
            keep_copy=True,
        )
        if not recording.get("compile") or recording.get("compile_count") != 1:
            raise RuntimeError(
                f"O6 heartbeat recording failed for {module}: "
                f"compile={recording.get('compile')!r}, "
                f"compile_count={recording.get('compile_count')!r}"
            )
        if set(recording.get("represented_occurrence_ids", [])) != expected_ids:
            raise RuntimeError(
                f"O6 heartbeat reports were incomplete for {module}: "
                f"represented={sorted(recording.get('represented_occurrence_ids', []))!r}"
            )

        reports = {
            report.get("occurrenceId"): report
            for report in recording.get("reports", [])
            if report.get("occurrenceId") in expected_ids
        }
        if set(reports) != expected_ids:
            raise RuntimeError(
                f"O6 heartbeat report identities changed for {module}: "
                f"reported={sorted(reports)!r}"
            )
        for identifier, report in reports.items():
            admissibility = report.get("operationalAdmissibility") or {}
            if (
                not report.get("traceAvailable")
                or not admissibility.get("code")
                or admissibility.get("code") == "unclassified_recorder_failure"
                or report.get("legacyCertificate") is not None
            ):
                raise RuntimeError(
                    f"O6 heartbeat site {identifier} in {module} was not recorded: "
                    f"admissibility={admissibility.get('code')!r}, "
                    f"trace={report.get('traceAvailable')!r}, "
                    f"legacy={report.get('legacyCertificate') is not None}"
                )

    print("O6 instance-heavy premise validation stayed bounded and recorded")


if __name__ == "__main__":
    main()
