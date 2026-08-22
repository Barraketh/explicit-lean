#!/usr/bin/env python3
"""Bounded O2b projection and materialization gate on Centralizer."""

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


def _event_label(event: dict) -> tuple[str, str | None]:
    reduction = event.get("reduction")
    if isinstance(reduction, dict):
        return "reduction", reduction.get("name") or reduction.get("kind")
    origins = event.get("origins") or []
    names = [origin.get("name") for origin in origins if isinstance(origin, dict)]
    return "named_rule", names[0] if len(names) == 1 else None


def check_public_delta_seam(record: dict, target: dict) -> dict:
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
    if not accepted or code != "accepted":
        raise RuntimeError(f"Centralizer O2b certificate was not accepted: {execution!r}")
    if execution.get("encodingStatus") != "validated":
        raise RuntimeError(f"Centralizer O2b certificate was not validated: {execution!r}")
    trace = execution.get("trace") or []
    if len(trace) != 12 or execution.get("certificateEventCount") != 12:
        raise RuntimeError(f"Centralizer raw event count changed: {report!r}")
    raw_expected = [
        ("reduction", "Finsupp.sum"),
        ("reduction", "beta"),
        ("named_rule", "Finset.mul_sum"),
        ("named_rule", "Algebra.TensorProduct.tmul_mul_tmul"),
        ("named_rule", "one_mul"),
        ("named_rule", "Algebra.TensorProduct.tmul_mul_tmul"),
        ("named_rule", "one_mul"),
        ("named_rule", "Finset.sum_mul"),
        ("named_rule", "Algebra.TensorProduct.tmul_mul_tmul"),
        ("named_rule", "mul_one"),
        ("named_rule", "Algebra.TensorProduct.tmul_mul_tmul"),
        ("named_rule", "mul_one"),
    ]
    raw_actual = [_event_label(event) for event in trace]
    if raw_actual != raw_expected:
        raise RuntimeError(f"Centralizer raw event sequence changed: {raw_actual!r}")
    selected_kinds = {"reduction", "named_rule"}
    selected = [event for event in trace if event.get("encodingKind") in selected_kinds]
    omitted = [
        event for event in trace
        if event.get("encodingKind") == "nonmaterial_internal_execution"
    ]
    if len(selected) != 8 or len(omitted) != 4:
        raise RuntimeError(
            f"Centralizer selected/raw projection counts changed: "
            f"selected={len(selected)} omitted={len(omitted)} trace={trace!r}"
        )
    selected_actual = [_event_label(event) for event in selected]
    selected_expected = [
        ("reduction", "Finsupp.sum"),
        ("reduction", "beta"),
        ("named_rule", "Finset.mul_sum"),
        ("named_rule", "Algebra.TensorProduct.tmul_mul_tmul"),
        ("named_rule", "one_mul"),
        ("named_rule", "Finset.sum_mul"),
        ("named_rule", "Algebra.TensorProduct.tmul_mul_tmul"),
        ("named_rule", "mul_one"),
    ]
    if selected_actual != selected_expected:
        raise RuntimeError(f"Centralizer selected event sequence changed: {selected_actual!r}")
    if any(
        event.get("encodingReason") != "nonmaterial_internal_execution"
        or event.get("selectorKind") is not None
        or event.get("selectorValue") is not None
        for event in omitted
    ):
        raise RuntimeError(f"Centralizer omitted event metadata is not aligned: {omitted!r}")
    if any(event.get("encodingKind") not in selected_kinds for event in selected):
        raise RuntimeError(f"Centralizer selected event metadata is invalid: {selected!r}")
    encoding = execution.get("encoding") or {}
    expected_metrics = {
        "reductionEvents": 2,
        "deltaReductionEvents": 1,
        "namedRuleEvents": 6,
        "nonmaterialInternalEvents": 4,
        "generatedProofEvents": 0,
        "generatedBindingCount": 0,
        "presentationChangeCount": 0,
        "wholeResultProofCount": 0,
    }
    for field, expected in expected_metrics.items():
        if encoding.get(field) != expected:
            raise RuntimeError(f"Centralizer metric {field} changed: {encoding!r}")
    certificate = execution.get("acceptedCertificate")
    if not isinstance(certificate, str) or not certificate.strip():
        raise RuntimeError(f"Centralizer accepted certificate is missing: {execution!r}")
    forbidden = ("change", "generated_proof", "whole_result_proof", "have ")
    if any(token in certificate for token in forbidden):
        raise RuntimeError(f"Centralizer certificate contains forbidden encoding: {certificate!r}")

    materialized_root = coverage.OUTPUT / "centralizer-materialized"
    materialized_path = coverage.write_copy(materialized_root, target, certificate)
    for suffix in (".olean", ".ilean", ".c", ".trace", ".hash"):
        materialized_path.with_suffix(suffix).unlink(missing_ok=True)
    code, output, elapsed = coverage.run(
        coverage.lean_command(materialized_path), timeout=180
    )
    if code != 0:
        raise RuntimeError(
            f"Centralizer accepted certificate failed full-module compilation "
            f"after {elapsed:.3f}s:\n{output}"
        )
    return {
        "rawEventCount": len(trace),
        "selectedEventCount": len(selected),
        "nonmaterialInternalEvents": len(omitted),
        "certificate": certificate,
        "materializedCompile": True,
        "materializedSeconds": round(elapsed, 3),
    }


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
    result = check_public_delta_seam(record, target)
    print(f"O2b Centralizer projection and full-module materialization passed: {result!r}")


if __name__ == "__main__":
    main()
