#!/usr/bin/env python3
"""Focused O6e gate for projection-function reductions and bridge reconstruction."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
MODULE = "Mathlib/Algebra/Algebra/NonUnitalSubalgebra.lean"
TARGET_ID = "add0ff7c330214e4"
FIXTURE = ROOT / "Experiment" / "O6eProjectionFunctionProbe.lean"
OUTPUT = ROOT / ".lake" / "o6e-projection-function"
PROJECTION = "NonUnitalSubring.toNonUnitalSubsemiring"
WRONG_PROJECTION = "NonUnitalSubalgebra.toNonUnitalSubsemiring"
ZETA_LINE = "  ↓ reduce zeta,\n"
PROJECTION_LINE = f"  ↓ reduce projection_fn {PROJECTION},\n"
BRIDGE = ZETA_LINE + PROJECTION_LINE

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
    for anchor in (
        "reduce projection_fn O6eProjectionRecord.value",
        "fail_if_success simp_explicit []",
        "fail_if_success simp_explicit [reduce projection_fn O6eOtherProjection.value]",
    ):
        if source.count(anchor) != 1:
            raise RuntimeError(f"focused O6e fixture is missing unique `{anchor}`")

    code, output = run_source(FIXTURE)
    if code != 0:
        raise RuntimeError(f"focused projection-function source failed:\n{output}")
    reports = coverage.parse_recording_reports(output)
    if len(reports) != 1:
        raise RuntimeError(f"focused O6e fixture emitted {len(reports)} reports")
    report = reports[0]
    if (
        report.get("schema") != "explicitLean.simpRecording"
        or report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION
        or report.get("operationallyAdmissible") is not True
        or report.get("encodingStatus") != "validated"
    ):
        raise RuntimeError(f"focused projection report is not schema-15 operational: {report!r}")
    certificate = report.get("acceptedCertificate")
    if not isinstance(certificate, str) or "reduce projection_fn O6eProjectionRecord.value" not in certificate:
        raise RuntimeError(f"focused projection certificate changed: {report!r}")
    reductions = [
        event.get("reduction")
        for execution in report.get("executions", [])
        for event in execution.get("trace", [])
        if event.get("reduction") is not None
    ]
    if reductions != [{"kind": "projection_function", "name": "O6eProjectionRecord.value", "field": None}]:
        raise RuntimeError(f"focused projection reduction identity changed: {report!r}")


def check_report(report: dict) -> str:
    if (
        report.get("schema") != "explicitLean.simpRecording"
        or report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION
    ):
        raise RuntimeError(f"target report schema changed: {report!r}")
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
    if certificate.count(BRIDGE) != 1:
        raise RuntimeError(f"target certificate lost the adjacent zeta/projection bridge: {certificate!r}")
    if certificate.count("reduce zeta") != 1 or certificate.count("reduce projection_fn ") != 1:
        raise RuntimeError(f"target certificate has an unexpected reduction sequence: {certificate!r}")
    if PROJECTION not in certificate:
        raise RuntimeError(f"target certificate has the wrong projection identity: {certificate!r}")

    executions = report.get("executions", [])
    trace = executions[0].get("trace", []) if len(executions) == 1 else []
    if (
        report.get("traceLength") != 7
        or report.get("certificateEventCount") != 6
        or len(trace) != 7
        or any(event.get("reduction") is not None for event in trace)
        or any(event.get("encodingKind") != "named_rule" for event in trace)
    ):
        raise RuntimeError(
            f"certificate-only bridge changed raw trace alignment: {report!r}"
        )

    encoding = report.get("encoding") or {}
    for metric in FORBIDDEN_METRICS:
        if encoding.get(metric, 0) != 0:
            raise RuntimeError(f"target certificate used forbidden metric {metric}: {encoding!r}")
    expected = {
        "mode": "event",
        "namedRuleEvents": 7,
        "reductionEvents": 2,
        "nextSelectorCount": 9,
        "matchSelectorCount": 0,
        "tickSelectorCount": 0,
        "totalCertificateBytes": 304,
    }
    if any(encoding.get(key) != value for key, value in expected.items()):
        raise RuntimeError(f"target certificate encoding changed: {encoding!r}")
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
        raise RuntimeError(f"{name} mutation did not fail through the fixed reduction guard:\n{output}")
    lowered = output.lower()
    for forbidden in ("panic", "unknown free variable", "unknown identifier", "unexpected token", "parser"):
        if forbidden in lowered:
            raise RuntimeError(f"{name} mutation failed for {forbidden!r}:\n{output}")


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
        raise RuntimeError(f"O6e target occurrence changed: {entries!r}")

    record = coverage.run_closure_module(
        MODULE,
        entries,
        document["mathlib_revision"],
        180,
        keep_copy=True,
    )
    if record.get("complete") is not True:
        raise RuntimeError(f"focused O6e closure did not complete: {record!r}")
    recording = record.get("recording") or {}
    aggregate = record.get("aggregate") or {}
    if recording.get("compile") is not True or recording.get("compile_count") != 1:
        raise RuntimeError(f"O6e passive recording was not singular: {record!r}")
    if (
        aggregate.get("compile") is not True
        or aggregate.get("materialization_compile_count") != 1
        or aggregate.get("closure_complete") is not True
    ):
        raise RuntimeError(f"O6e aggregate did not close operationally: {record!r}")

    occurrences = {item["id"]: item for item in record.get("occurrences", [])}
    target = occurrences.get(TARGET_ID)
    if (
        target is None
        or target.get("terminal_outcome") != "materialized"
        or target.get("materialized_compile") is not True
        or target.get("failure_reason") is not None
    ):
        raise RuntimeError(f"O6e target did not materialize: {record!r}")
    report = target.get("report") or {}
    certificate = check_report(report)
    candidate = target.get("candidate") or {}
    if candidate.get("replacement") != certificate:
        raise RuntimeError("target candidate did not preserve the accepted certificate")

    source = (coverage.MATHLIB / MODULE).read_bytes()
    check_mutation("delete-zeta", candidate, source, certificate.replace(ZETA_LINE, "", 1))
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
        certificate.replace(BRIDGE, PROJECTION_LINE + ZETA_LINE, 1),
    )
    check_mutation(
        "wrong-projection",
        candidate,
        source,
        certificate.replace(PROJECTION, WRONG_PROJECTION, 1),
    )


def main() -> None:
    check_focused_source()
    check_production()
    print("O6e projection-function and certificate-bridge gates passed")


if __name__ == "__main__":
    main()
