#!/usr/bin/env python3
"""Focused O6c gate for exact traversal-local simp-rule replay."""

from __future__ import annotations

from collections import Counter
from pathlib import Path
from types import SimpleNamespace
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
MODULE = "Mathlib/Algebra/Algebra/Bilinear.lean"
TARGET_ID = "5795dc0135cc7db3"
FIXTURE = ROOT / "Experiment" / "O6cContextualLocalRuleProbe.lean"
OUTPUT = ROOT / ".lake" / "o6c-contextual-local-rule"

FORBIDDEN_METRICS = (
    "deferredSimprocEvents",
    "generatedBindingBytes",
    "generatedBindingCount",
    "generatedProofEvents",
    "generatedSimprocEvents",
    "generatedSpecialEvents",
    "nonmaterialInternalEvents",
    "operationalProgramFailures",
    "premiseBindingBytes",
    "premiseBindingCount",
    "premiseProgramFailures",
    "presentationChangeCount",
    "termPremiseBindings",
    "wholeResultProofCount",
)


def run_source(path: Path) -> tuple[int, str]:
    return coverage.run(["lake", "env", "lean", str(path)], timeout=180)[:2]


def check_focused_source() -> None:
    source = FIXTURE.read_text(encoding="utf-8")
    anchor = "simp_explicit [local_rule 1, implies_true]"
    if source.count(anchor) != 1:
        raise RuntimeError("focused O6c success anchor is not unique")
    code, output = run_source(FIXTURE)
    if code != 0:
        raise RuntimeError(f"focused local-rule source failed:\n{output}")

    mutated_source = source.replace(anchor, "simp_explicit [local_rule 2, implies_true]", 1)
    mutated = OUTPUT / "focused" / "O6cContextualLocalRuleProbe_wrong_slot.lean"
    mutated.parent.mkdir(parents=True, exist_ok=True)
    mutated.write_text(mutated_source, encoding="utf-8")
    code, output = run_source(mutated)
    if code == 0:
        raise RuntimeError("wrong traversal-local slot unexpectedly compiled")
    if "ordered simp rule did not match anywhere in the remaining traversal" not in output:
        raise RuntimeError(f"wrong-slot mutation lost its ordered-rule diagnostic:\n{output}")
    lowered = output.lower()
    for forbidden in ("unknown free variable", "panic", "unexpected token", "parser"):
        if forbidden in lowered:
            raise RuntimeError(
                f"wrong-slot mutation failed for {forbidden!r} instead of an ordered-rule mismatch:\n{output}"
            )


def check_report(report: dict) -> str:
    if report.get("schema") != "explicitLean.simpRecording":
        raise RuntimeError(f"target report schema changed: {report!r}")
    if report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION:
        raise RuntimeError(f"target report schema version changed: {report!r}")
    admissibility = report.get("operationalAdmissibility") or {}
    if (
        admissibility.get("code") != "accepted"
        or report.get("operationallyAdmissible") is not True
        or report.get("encodingStatus") != "validated"
        or report.get("legacyCertificate") is not None
        or report.get("encodingFallbackReason") is not None
    ):
        raise RuntimeError(f"target report is not an accepted operational certificate: {report!r}")
    certificate = report.get("acceptedCertificate")
    if not isinstance(certificate, str) or not certificate:
        raise RuntimeError(f"target report has no accepted certificate: {report!r}")
    if report.get("certificate") != certificate:
        raise RuntimeError("target report did not expose the accepted certificate")
    if certificate.count("local_rule 3") != 1 or certificate.count("local_rule 4") != 1:
        raise RuntimeError(f"target certificate lost the expected local-rule slots: {certificate!r}")
    if set(re.findall(r"local_rule (\d+)", certificate)) != {"3", "4"}:
        raise RuntimeError(f"target certificate contains an unexpected local-rule slot: {certificate!r}")

    encoding = report.get("encoding") or {}
    for metric in FORBIDDEN_METRICS:
        if encoding.get(metric, 0) != 0:
            raise RuntimeError(f"target certificate used forbidden metric {metric}: {encoding!r}")
    if (
        encoding.get("mode") != "event"
        or encoding.get("namedRuleEvents") != 29
        or encoding.get("nextSelectorCount") != 29
        or encoding.get("matchSelectorCount") != 0
        or encoding.get("tickSelectorCount") != 0
    ):
        raise RuntimeError(f"target certificate encoding changed: {encoding!r}")
    return certificate


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
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    if len(entries) != 10:
        raise RuntimeError(f"Bilinear supported inventory changed: {entries!r}")
    by_id = {entry["id"]: entry for entry in entries}
    if TARGET_ID not in by_id:
        raise RuntimeError(f"Bilinear target occurrence disappeared: {sorted(by_id)!r}")

    record = coverage.run_closure_module(
        MODULE,
        entries,
        document["mathlib_revision"],
        180,
        keep_copy=True,
    )
    recording = record.get("recording") or {}
    aggregate = record.get("aggregate") or {}
    if recording.get("compile") is not True or recording.get("compile_count") != 1:
        raise RuntimeError(f"Bilinear passive recording was not singular: {record!r}")
    if (
        aggregate.get("compile") is not True
        or aggregate.get("materialization_compile_count") != 1
        or aggregate.get("closure_complete") is not True
    ):
        raise RuntimeError(f"Bilinear operational aggregate did not close: {record!r}")
    outcomes = Counter(item.get("terminal_outcome") for item in record.get("occurrences", []))
    if outcomes != Counter({"materialized": 10}):
        raise RuntimeError(f"Bilinear terminal outcomes changed: {outcomes!r}")

    occurrences = {item["id"]: item for item in record.get("occurrences", [])}
    target = occurrences.get(TARGET_ID)
    if target is None or target.get("terminal_outcome") != "materialized":
        raise RuntimeError(f"Bilinear target did not materialize: {record!r}")
    certificate = check_report(target.get("report") or {})
    candidate = target.get("candidate") or {}
    if candidate.get("replacement") != certificate:
        raise RuntimeError("target candidate did not preserve the accepted certificate")


def main() -> None:
    check_focused_source()
    check_production()
    print("O6c contextual local-rule production and wrong-slot gates passed")


if __name__ == "__main__":
    main()
