#!/usr/bin/env python3
"""Bounded O1 transition-gate check on the production Centralizer module."""

from __future__ import annotations

from types import SimpleNamespace
import time

import simp_coverage as coverage


MODULE = "Mathlib/Algebra/Algebra/Subalgebra/Centralizer.lean"
TARGET_ID = "161579b1c1009ed4"
TARGET_SOURCE = "simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,\n      Finset.sum_mul, mul_one] at hw"
EXPECTED_IDS = {
    "9dfed3d35b21d42b",
    "02c373b34fee842e",
    "161579b1c1009ed4",
    "6def84e0f5305e28",
    "1bae7dca4740eb52",
    "653b705b8d7fb19f",
    "6b715fedb8b1946f",
    "bdac2d92f098d472",
    "5a645f761cfac920",
    "46987a3107ce3007",
    "8a9d921fe307a652",
    TARGET_ID,
    "db06a893b3ae282f",
    "3653fb23244c9406",
}


def normalized_source(source: str) -> str:
    """Ignore pretty-printer indentation while preserving authored tokens."""
    return " ".join(source.split())


def configure_output() -> None:
    output = coverage.ROOT / ".lake" / "g-proof-export-scaling"
    coverage.OUTPUT = output
    coverage.INVENTORY = output / "inventory.json"
    coverage.RESULTS = output / "results"
    coverage.AGGREGATE_RESULTS = output / "aggregate-results"


def load_entries() -> tuple[dict, list[dict], str]:
    coverage.inventory(SimpleNamespace(modules=[MODULE], timeout=600, batch_size=1000))
    document = coverage.load_inventory()
    entries = [
        entry
        for entry in document["entries"]
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    by_id = {entry["id"]: entry for entry in entries}
    if set(by_id) != EXPECTED_IDS:
        raise RuntimeError(
            f"Centralizer supported occurrence IDs changed: {sorted(by_id)!r}"
        )
    target = by_id[TARGET_ID]
    if target.get("source") != TARGET_SOURCE:
        raise RuntimeError(f"Centralizer target source changed: {target!r}")
    return target, entries, document["mathlib_revision"]


def check_public_delta_seam(record: dict) -> None:
    reports = {
        report.get("occurrenceId"): report
        for report in record.get("reports", [])
        if isinstance(report, dict)
    }
    report = reports.get(TARGET_ID)
    if report is None:
        raise RuntimeError(f"Centralizer transition-gate report is missing: {record!r}")
    if normalized_source(report.get("originalSyntax", "")) != normalized_source(TARGET_SOURCE):
        raise RuntimeError(f"Centralizer target source changed: {report!r}")
    if report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION:
        raise RuntimeError(f"Centralizer report schema changed: {report!r}")
    # O2a deliberately stops at the public pre-method seam.  The trace is
    # evidence that the named delta was observed; O2b owns the pinned private
    # observer needed to validate/materialize the complete context sequence.
    committed = [
        execution
        for execution in report.get("executions", [])
        if execution.get("disposition") == "committed"
    ]
    if len(committed) != 1:
        raise RuntimeError(
            f"Centralizer public seam did not retain exactly one committed execution: {report!r}"
        )
    execution = committed[0]
    accepted, code = coverage.report_admissibility(execution)
    if accepted or code != "unidentified_theorem_application":
        raise RuntimeError(
            f"Centralizer public seam unexpectedly closed the O2b observer gap: {execution!r}"
        )
    if execution.get("encodingStatus") != "inadmissible":
        raise RuntimeError(f"Centralizer observer gap was not retained: {execution!r}")
    if execution.get("encodingFallbackReason") != "context_subject_encoding":
        raise RuntimeError(f"Centralizer observer-gap classification changed: {execution!r}")
    continuity = execution.get("transitionContinuity") or {}
    if (
        continuity.get("reasonCode") != "unidentified_theorem_application"
        or continuity.get("firstUnconsumedEventIndex") != 2
        or continuity.get("gapLocation") != "between_events"
    ):
        raise RuntimeError(f"Centralizer public-seam continuity changed: {execution!r}")
    trace = execution.get("trace") or []
    if len(trace) != 11:
        raise RuntimeError(f"Centralizer event count changed: {report!r}")
    reduction = trace[0]
    if reduction.get("reduction") != {
        "kind": "delta",
        "name": "Finsupp.sum",
        "field": None,
    }:
        raise RuntimeError(f"Centralizer first event is not named delta: {reduction!r}")
    if reduction.get("origins"):
        raise RuntimeError(f"Centralizer delta carried theorem provenance: {reduction!r}")
    if any(event.get("encodingKind") is not None for event in trace):
        raise RuntimeError(f"Centralizer diagnostic events were mislabeled as encoded: {trace!r}")
    encoding = execution.get("encoding") or {}
    if any(
        encoding.get(field) != 0
        for field in ("reductionEvents", "deltaReductionEvents", "namedRuleEvents")
    ):
        raise RuntimeError(f"Centralizer diagnostic trace leaked into encoding metrics: {report!r}")
    if report.get("acceptedCertificate") is not None or report.get("certificate"):
        raise RuntimeError(f"O2a unexpectedly materialized the Centralizer context: {report!r}")
    validation = report.get("validation") or {}
    if validation.get("certificate") is not None:
        raise RuntimeError(f"O2a unexpectedly exported a Centralizer certificate: {report!r}")


def check_module_recording(entries: list[dict], revision: str) -> dict:
    started = time.monotonic()
    record = coverage.passive_module_recording(
        MODULE,
        entries,
        timeout=180,
        keep_copy=True,
    )
    elapsed = time.monotonic() - started
    if record.get("compile") is not True:
        raise RuntimeError(f"Centralizer passive recording failed: {record!r}")
    if record.get("compile_count") != 1:
        raise RuntimeError(f"Centralizer passive recording was not one-copy: {record!r}")
    if record.get("elapsed_seconds", 180) >= 180 or elapsed >= 180:
        raise RuntimeError(f"Centralizer passive recording exceeded the 180s gate: {record!r}")
    expected = {entry["id"] for entry in entries}
    observed = set(record.get("observed_occurrence_ids", []))
    reported = {
        report.get("occurrenceId")
        for report in record.get("reports", [])
        if isinstance(report, dict)
    }
    if observed != expected or reported != expected:
        raise RuntimeError(
            f"Centralizer passive occurrence coverage changed: "
            f"observed={sorted(observed)!r}, reported={sorted(reported)!r}"
        )
    if record.get("module") != MODULE or record.get("expected_occurrence_count") != 13:
        raise RuntimeError(f"Centralizer passive inventory count changed: {record!r}")
    if revision != coverage.load_inventory()["mathlib_revision"]:
        raise RuntimeError("Centralizer Mathlib revision changed during the check")
    return record


def main() -> None:
    configure_output()
    target, entries, revision = load_entries()
    record = check_module_recording(entries, revision)
    check_public_delta_seam(record)
    print(
        "O2a public seam passed: Centralizer observed named Finsupp.sum delta "
        "with the complete context observer gap retained for O2b"
    )


if __name__ == "__main__":
    main()
