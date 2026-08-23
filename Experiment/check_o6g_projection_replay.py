#!/usr/bin/env python3
"""Focused O6g gate for beta-dependent projection-function replay."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
MODULE = "Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean"
TARGET_ID = "226e61786984b7bc"
FIXTURE = ROOT / "Experiment" / "O6gProjectionCoercionProbe.lean"
OUTPUT = ROOT / ".lake" / "o6g-projection-replay"
PROJECTION_LINE = "  reduce projection_fn Units.val,\n"
FIRST_RULE_LINE = "  Unitization.toProd_add,\n"
WRONG_PROJECTION = "Subtype.val"

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
    anchors = (
        "reduce projection_fn O6gProjectionRecord.value, o6gPayload_eq",
        "reduce projection_fn O6gOtherProjection.value",
    )
    for anchor in anchors:
        if source.count(anchor) != 1:
            raise RuntimeError(f"focused O6g fixture is missing unique `{anchor}`")

    code, output = run_source(FIXTURE)
    if code != 0:
        raise RuntimeError(f"focused beta-dependent projection source failed:\n{output}")
    reports = coverage.parse_recording_reports(output)
    if len(reports) != 1:
        raise RuntimeError(f"focused O6g fixture emitted {len(reports)} reports")
    report = reports[0]
    certificate = report.get("acceptedCertificate")
    encoding = report.get("encoding") or {}
    if (
        report.get("schema") != "explicitLean.simpRecording"
        or report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION
        or report.get("operationallyAdmissible") is not True
        or report.get("encodingStatus") != "validated"
        or not isinstance(certificate, str)
        or certificate.count("reduce projection_fn O6gProjectionRecord.value") != 1
        or encoding.get("reductionEvents") != 1
        or encoding.get("operationalProgramFailures") != 0
    ):
        raise RuntimeError(f"focused O6g report is not operational: {report!r}")


def check_report(report: dict) -> str:
    admissibility = report.get("operationalAdmissibility") or {}
    certificate = report.get("acceptedCertificate")
    if (
        report.get("schema") != "explicitLean.simpRecording"
        or report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION
        or report.get("operationallyAdmissible") is not True
        or admissibility.get("code") != "accepted"
        or report.get("encodingStatus") != "validated"
        or report.get("legacyCertificate") is not None
        or report.get("encodingFallbackReason") is not None
        or not isinstance(certificate, str)
        or report.get("certificate") != certificate
    ):
        raise RuntimeError(f"production O6g report is not operational: {report!r}")
    if certificate.count(PROJECTION_LINE) != 2:
        raise RuntimeError(f"production certificate lost its two Units.val reductions: {certificate!r}")

    executions = report.get("executions", [])
    trace = executions[0].get("trace", []) if len(executions) == 1 else []
    reductions = [event.get("reduction") for event in trace if event.get("reduction")]
    expected_reduction = {
        "kind": "projection_function",
        "name": "Units.val",
        "field": None,
    }
    if (
        report.get("traceLength") != 9
        or report.get("certificateEventCount") != 8
        or len(trace) != 9
        or reductions != [expected_reduction, expected_reduction]
    ):
        raise RuntimeError(f"production O6g trace changed: {report!r}")

    encoding = report.get("encoding") or {}
    expected = {
        "mode": "event",
        "namedRuleEvents": 6,
        "reductionEvents": 2,
        "nextSelectorCount": 8,
        "matchSelectorCount": 0,
        "tickSelectorCount": 0,
        "totalCertificateBytes": 210,
    }
    if any(encoding.get(key) != value for key, value in expected.items()):
        raise RuntimeError(f"production O6g encoding changed: {encoding!r}")
    for metric in FORBIDDEN_METRICS:
        if encoding.get(metric, 0) != 0:
            raise RuntimeError(f"production O6g used forbidden metric {metric}: {encoding!r}")
    return certificate


def check_mutation(name: str, candidate: dict, source: bytes, replacement: str) -> None:
    if replacement == candidate.get("replacement"):
        raise RuntimeError(f"{name} mutation did not change the certificate")
    mutated = candidate.copy()
    mutated["replacement"] = replacement
    attempt = coverage.compile_closure_candidates(
        MODULE,
        source,
        [mutated],
        180,
        label=f"mutation-{name}",
        keep_copy=True,
    )
    if attempt.get("compile") is True:
        raise RuntimeError(f"{name} mutation unexpectedly compiled: {attempt!r}")
    log_path = OUTPUT / "closure-attempts" / MODULE / f"mutation-{name}.log"
    output = log_path.read_text(encoding="utf-8") if log_path.exists() else ""
    if not any(
        needle in output
        for needle in (
            "ordered simp rule did not match",
            "without an explicit reduction command",
        )
    ):
        raise RuntimeError(f"{name} mutation bypassed the reduction guard:\n{output}")


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
        raise RuntimeError(f"O6g target occurrence changed: {entries!r}")

    record = coverage.run_closure_module(
        MODULE, entries, document["mathlib_revision"], 180, keep_copy=True
    )
    occurrences = {item["id"]: item for item in record.get("occurrences", [])}
    target = occurrences.get(TARGET_ID)
    if (
        record.get("complete") is not True
        or (record.get("recording") or {}).get("compile_count") != 1
        or (record.get("aggregate") or {}).get("materialization_compile_count") != 1
        or target is None
        or target.get("terminal_outcome") != "materialized"
        or target.get("materialized_compile") is not True
        or target.get("failure_reason") is not None
    ):
        raise RuntimeError(f"O6g target did not materialize singularly: {record!r}")

    certificate = check_report(target.get("report") or {})
    candidate = target.get("candidate") or {}
    if candidate.get("replacement") != certificate:
        raise RuntimeError("O6g candidate did not preserve the accepted certificate")
    source = (coverage.MATHLIB / MODULE).read_bytes()
    check_mutation(
        "delete-projection",
        candidate,
        source,
        certificate.replace(PROJECTION_LINE, "", 1),
    )
    check_mutation(
        "swap-order",
        candidate,
        source,
        certificate.replace(
            PROJECTION_LINE + FIRST_RULE_LINE,
            FIRST_RULE_LINE + PROJECTION_LINE,
            1,
        ),
    )
    check_mutation(
        "wrong-projection",
        candidate,
        source,
        certificate.replace("Units.val", WRONG_PROJECTION, 1),
    )


def main() -> None:
    check_focused_source()
    check_production()
    print("O6g beta-dependent projection replay gates passed")


if __name__ == "__main__":
    main()
