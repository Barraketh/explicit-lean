#!/usr/bin/env python3
"""Bounded proof-export scaling regression on a production Mathlib module.

The isolated target checks the proof-export path that previously spent most of
its time measuring a fully expanded proof.  The module check is intentionally
recording-only: it verifies that one passive compile observes the complete
supported inventory while leaving the separately classified context replay
gap to its own work package.
"""

from __future__ import annotations

from types import SimpleNamespace
import time

import simp_coverage as coverage


MODULE = "Mathlib/Algebra/Algebra/Subalgebra/Centralizer.lean"
TARGET_ID = "8a9d921fe307a652"
TARGET_SOURCE = "simp [includeRight]"
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
    TARGET_ID,
    "db06a893b3ae282f",
    "3653fb23244c9406",
}


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


def check_isolated_target(target: dict) -> None:
    result = coverage.run_trial(
        target,
        coverage.TrialConfig(timeout=30, keep_copies=True),
    )
    if result.get("recording_compile") is not True:
        raise RuntimeError(f"Centralizer target recording exceeded the 30s gate: {result!r}")
    if result.get("materialized_compile") is not True or result.get("status") != "passed":
        raise RuntimeError(f"Centralizer target did not materialize: {result!r}")
    if result.get("recording_seconds", 30) >= 30:
        raise RuntimeError(f"Centralizer target recording used the entire budget: {result!r}")
    encoding = result.get("encoding")
    if not isinstance(encoding, dict) or encoding.get("mode") != "whole_result_proof":
        raise RuntimeError(f"Centralizer target encoding changed: {result!r}")
    if result.get("encoding_fallback_reason") != "presentation_gap":
        raise RuntimeError(f"Centralizer target fallback changed: {result!r}")
    certificate = result.get("certificate")
    if not isinstance(certificate, str) or not certificate.strip():
        raise RuntimeError(f"Centralizer target certificate is empty: {result!r}")
    if TARGET_SOURCE in certificate or "simp +" in certificate:
        raise RuntimeError(f"Centralizer target certificate retained ambient simp syntax: {result!r}")


def check_module_recording(entries: list[dict], revision: str) -> None:
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


def main() -> None:
    configure_output()
    target, entries, revision = load_entries()
    check_isolated_target(target)
    check_module_recording(entries, revision)
    print(
        "proof-export scaling passed: isolated Centralizer target materialized "
        "and one passive compile observed all 13 supported occurrences"
    )


if __name__ == "__main__":
    main()
