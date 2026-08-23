#!/usr/bin/env python3
"""Focused O6f gate for declaration-faithful simp theorem elaboration."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
MODULE = "Mathlib/Algebra/Algebra/Spectrum/Basic.lean"
TARGET_ID = "a2c03aa81fb3fb0b"
FIXTURE = ROOT / "Experiment" / "O6fMemNegProbe.lean"
OUTPUT = ROOT / ".lake" / "o6f-declaration-elaboration"


def run_source(path: Path) -> tuple[int, str]:
    return coverage.run(["lake", "env", "lean", str(path)], timeout=180)[:2]


def check_operational_report(
    report: dict, *, label: str, expected_named_rule_events: int | None = None
) -> None:
    if (
        report.get("schema") != "explicitLean.simpRecording"
        or report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION
        or report.get("operationallyAdmissible") is not True
        or report.get("encodingStatus") != "validated"
        or report.get("legacyCertificate") is not None
        or report.get("encodingFallbackReason") is not None
    ):
        raise RuntimeError(f"{label} report is not an operational certificate: {report!r}")
    certificate = report.get("acceptedCertificate")
    if not isinstance(certificate, str) or "Set.mem_neg" not in certificate:
        raise RuntimeError(f"{label} certificate did not preserve Set.mem_neg: {report!r}")
    if report.get("certificate") != certificate:
        raise RuntimeError(f"{label} report did not preserve its accepted certificate")
    encoding = report.get("encoding") or {}
    if (
        encoding.get("reductionEvents") != 0
        or encoding.get("operationalProgramFailures") != 0
        or (
            expected_named_rule_events is not None
            and encoding.get("namedRuleEvents") != expected_named_rule_events
        )
    ):
        raise RuntimeError(f"{label} used a reduction or fallback path: {report!r}")


def check_focused_source() -> None:
    source = FIXTURE.read_text(encoding="utf-8")
    for needle in ("structure O6fMemNegType", "simp_explicit? [Set.mem_neg]"):
        if source.count(needle) != 1:
            raise RuntimeError(f"focused O6f fixture is missing unique `{needle}`")
    if "#print" in source:
        raise RuntimeError("focused O6f fixture still contains a diagnostic #print")

    code, output = run_source(FIXTURE)
    if code != 0:
        raise RuntimeError(f"focused polymorphic declaration source failed:\n{output}")
    reports = coverage.parse_recording_reports(output)
    if len(reports) != 1:
        raise RuntimeError(f"focused O6f fixture emitted {len(reports)} reports:\n{output}")
    report = reports[0]
    check_operational_report(
        report, label="focused polymorphic declaration", expected_named_rule_events=1
    )
    if "O6fMemNegType" not in output:
        raise RuntimeError("focused O6f goal did not retain its non-default type")


def check_production() -> None:
    coverage.OUTPUT = OUTPUT
    coverage.INVENTORY = OUTPUT / "inventory.json"
    coverage.RESULTS = OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = OUTPUT / "aggregate-results"
    coverage.inventory(SimpleNamespace(modules=[MODULE], timeout=600, batch_size=1000))
    document = coverage.load_inventory()
    entries = [
        entry
        for entry in document["entries"]
        if entry["kind"] in coverage.SUPPORTED_KINDS and entry["id"] == TARGET_ID
    ]
    if len(entries) != 1:
        raise RuntimeError(f"O6f target occurrence changed: {entries!r}")

    record = coverage.run_closure_module(
        MODULE,
        entries,
        document["mathlib_revision"],
        180,
        keep_copy=True,
    )
    if record.get("complete") is not True:
        raise RuntimeError(f"focused O6f closure did not complete: {record!r}")
    recording = record.get("recording") or {}
    aggregate = record.get("aggregate") or {}
    if recording.get("compile") is not True or recording.get("compile_count") != 1:
        raise RuntimeError(f"O6f passive recording was not singular: {record!r}")
    if (
        aggregate.get("compile") is not True
        or aggregate.get("materialization_compile_count") != 1
        or aggregate.get("closure_complete") is not True
    ):
        raise RuntimeError(f"O6f aggregate did not close operationally: {record!r}")

    occurrences = {item["id"]: item for item in record.get("occurrences", [])}
    target = occurrences.get(TARGET_ID)
    if (
        target is None
        or target.get("terminal_outcome") != "materialized"
        or target.get("materialized_compile") is not True
        or target.get("failure_reason") is not None
    ):
        raise RuntimeError(f"O6f target did not materialize: {record!r}")
    report = target.get("report") or {}
    check_operational_report(report, label="production target")


def main() -> None:
    check_focused_source()
    check_production()
    print("O6f declaration-faithful theorem elaboration gates passed")


if __name__ == "__main__":
    main()
