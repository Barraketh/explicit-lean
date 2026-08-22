#!/usr/bin/env python3
"""Check the focused O3 exact-origin attribution fixtures."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "O3AttributionProbe.lean"


def report_events(report: dict) -> list[dict]:
    return [
        event
        for execution in report.get("executions", [])
        for event in execution.get("trace", [])
    ]


def origin_names(event: dict) -> list[str]:
    return [
        origin.get("name")
        for origin in event.get("origins", [])
        if origin.get("kind") == "decl"
    ]


def find_event(reports: list[dict], name: str) -> dict:
    matches = [
        event
        for report in reports
        for event in report_events(report)
        if origin_names(event) == [name]
    ]
    if len(matches) != 1:
        raise RuntimeError(
            f"expected one exact {name} event, found {len(matches)}: {matches!r}"
        )
    return matches[0]


def main() -> None:
    code, output, _ = coverage.run(
        ["lake", "env", "lean", str(PROBE)], timeout=180
    )
    reports = coverage.parse_recording_reports(output)
    if code != 0 or len(reports) != 4:
        raise RuntimeError(
            f"O3 attribution probe failed or emitted an unexpected report count: "
            f"exit={code}, reports={len(reports)}\n{output}"
        )

    for report in reports:
        if report.get("schema") != "explicitLean.simpRecording":
            raise RuntimeError(f"unexpected O3 report schema: {report!r}")
        if report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION:
            raise RuntimeError(f"unexpected O3 report version: {report!r}")
        encoding = report.get("encoding") or {}
        if encoding.get("mode") != "event":
            raise RuntimeError(f"O3 fixture used a non-event encoding: {report!r}")
        if encoding.get("generatedProofEvents", 0) != 0:
            raise RuntimeError(f"O3 fixture used generated event proofs: {report!r}")
        if encoding.get("wholeResultProofCount", 0) != 0:
            raise RuntimeError(f"O3 fixture used whole-result proof fallback: {report!r}")
        for event in report_events(report):
            if len(event.get("origins", [])) > 1:
                raise RuntimeError(f"O3 event retained multiple origins: {event!r}")
            if event.get("encodingKind") == "generated_proof":
                raise RuntimeError(f"O3 event used generated proof encoding: {event!r}")

    nat_sub_zero = find_event(reports, "Nat.sub_zero")
    if len(nat_sub_zero.get("origins", [])) != 1:
        raise RuntimeError(f"Nat.sub_zero was not an exact single-origin event: {nat_sub_zero!r}")

    take_length = find_event(reports, "List.take_length_add_append")
    if len(take_length.get("origins", [])) != 1:
        raise RuntimeError(
            f"List.take_length_add_append was not an exact single-origin event: {take_length!r}"
        )

    sup_of_le_right = find_event(reports, "sup_of_le_right")
    premise_origins = [
        origin.get("name")
        for premise in sup_of_le_right.get("premises", [])
        for origin in premise.get("origins", [])
        if origin.get("kind") == "decl"
    ]
    if premise_origins != ["bot_le"]:
        raise RuntimeError(
            f"sup_of_le_right did not retain its exact bot_le premise: {sup_of_le_right!r}"
        )

    index_false_reports = [
        report
        for report in reports
        if (report.get("configuration") or {}).get("normalized", {}).get("index") is False
    ]
    if len(index_false_reports) != 1:
        raise RuntimeError(
            f"expected one index=false report, found {len(index_false_reports)}"
        )
    add_zero = find_event(index_false_reports, "add_zero")
    if len(add_zero.get("origins", [])) != 1:
        raise RuntimeError(f"index=false add_zero was not exact: {add_zero!r}")

    print("O3 attribution fixtures validated: schema 13, exact origins, bot_le premise, and index=false")


if __name__ == "__main__":
    main()
