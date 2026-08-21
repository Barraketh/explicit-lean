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


def check_transition_gate(record: dict) -> None:
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
    accepted, code = coverage.report_admissibility(report)
    if accepted or code != "missing_transition":
        raise RuntimeError(f"Centralizer transition was not rejected as missing_transition: {report!r}")
    continuity = report.get("transitionContinuity")
    if not isinstance(continuity, dict):
        raise RuntimeError(f"Centralizer continuity diagnostic is missing: {report!r}")
    if continuity.get("firstUnconsumedEventIndex") != 0:
        raise RuntimeError(f"Centralizer gap index was not zero: {continuity!r}")
    if continuity.get("gapLocation") != "before_event":
        raise RuntimeError(f"Centralizer gap location changed: {continuity!r}")
    if continuity.get("operationHint") != "delta Finsupp.sum":
        raise RuntimeError(f"Centralizer delta hint changed: {continuity!r}")
    if continuity.get("operationKind") != "delta":
        raise RuntimeError(f"Centralizer operation kind changed: {continuity!r}")
    if not continuity.get("matchedSubexpressionPath"):
        raise RuntimeError(f"Centralizer matched-subexpression path is missing: {continuity!r}")
    if not continuity.get("matchedSubexpressionFingerprint"):
        raise RuntimeError(
            f"Centralizer matched-subexpression fingerprint is missing: {continuity!r}"
        )
    if "Finset.mul_sum" not in (continuity.get("expectedEventOrigins") or []):
        raise RuntimeError(f"Centralizer first-event provenance changed: {continuity!r}")
    if report.get("acceptedCertificate") is not None or report.get("certificate"):
        raise RuntimeError(f"Centralizer emitted an accepted certificate: {report!r}")
    validation = report.get("validation") or {}
    if validation.get("certificate") is not None:
        raise RuntimeError(f"Centralizer validation exported a certificate: {report!r}")


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
    check_transition_gate(record)
    print(
        "O1 transition gate passed: Centralizer passive recording observed all 13 "
        "occurrences and rejected the Finsupp.sum gap before proof export"
    )


if __name__ == "__main__":
    main()
