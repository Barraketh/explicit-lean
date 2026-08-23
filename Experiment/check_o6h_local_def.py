#!/usr/bin/env python3
"""Focused O6h gate for exact ambient local-let expansion replay."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
MODULE = "Mathlib/Algebra/Algebra/Subalgebra/Directed.lean"
TARGET_ID = "26c72cb4c4292d08"
FIXTURE = ROOT / "Experiment" / "O6hLocalDefProbe.lean"
OUTPUT = ROOT / ".lake" / "o6h-local-def"
LOCAL_DEF_LINE = "  ↓ reduce local_def s,\n"
ZETA_LINE = "  ↓ reduce zeta,\n"

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


def check_focused_source() -> None:
    source = FIXTURE.read_text(encoding="utf-8")
    for anchor in (
        "reduce local_def s, reduce zeta",
        "reduce local_def other, reduce zeta",
        "reduce zeta, reduce local_def s",
        "reduce local_def n, reduce zeta",
    ):
        if source.count(anchor) != 1:
            raise RuntimeError(f"focused O6h fixture is missing unique `{anchor}`")
    code, output, _ = coverage.run(
        ["lake", "env", "lean", str(FIXTURE)], timeout=180
    )
    if code != 0:
        raise RuntimeError(f"focused local-definition source failed:\n{output}")


def check_report(report: dict) -> str:
    admissibility = report.get("operationalAdmissibility") or {}
    certificate = report.get("acceptedCertificate")
    if (
        report.get("schema") != "explicitLean.simpRecording"
        or report.get("schemaVersion")
        != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION
        or report.get("operationallyAdmissible") is not True
        or admissibility.get("code") != "accepted"
        or report.get("encodingStatus") != "validated"
        or report.get("legacyCertificate") is not None
        or report.get("encodingFallbackReason") is not None
        or not isinstance(certificate, str)
        or report.get("certificate") != certificate
    ):
        raise RuntimeError(f"production O6h report is not operational: {report!r}")
    expected_commands = (
        LOCAL_DEF_LINE,
        ZETA_LINE,
        "  match 3 => Subalgebra.coe_mk,\n",
    )
    if any(certificate.count(command) != 1 for command in expected_commands):
        raise RuntimeError(f"production O6h certificate changed: {certificate!r}")
    if certificate.index(LOCAL_DEF_LINE) >= certificate.index(ZETA_LINE):
        raise RuntimeError(f"local-definition expansion moved after zeta: {certificate!r}")

    executions = report.get("executions", [])
    trace = executions[0].get("trace", []) if len(executions) == 1 else []
    reductions = [event.get("reduction") for event in trace if event.get("reduction")]
    if (
        report.get("traceLength") != 6
        or len(trace) != 6
        or reductions != [{"kind": "zeta", "name": None, "field": None}]
    ):
        raise RuntimeError(f"O6h changed the raw recorder trace: {report!r}")

    encoding = report.get("encoding") or {}
    expected = {
        "mode": "event",
        "namedRuleEvents": 5,
        "reductionEvents": 2,
        "nextSelectorCount": 6,
        "matchSelectorCount": 1,
        "tickSelectorCount": 0,
        "totalCertificateBytes": 168,
    }
    if any(encoding.get(key) != value for key, value in expected.items()):
        raise RuntimeError(f"production O6h encoding changed: {encoding!r}")
    for metric in FORBIDDEN_METRICS:
        if encoding.get(metric, 0) != 0:
            raise RuntimeError(f"production O6h used forbidden metric {metric}: {encoding!r}")
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
    expected_errors = (
        "ordered simp rule did not match",
        "without an explicit reduction command",
        "requires a local let declaration",
    )
    if not any(message in output for message in expected_errors):
        raise RuntimeError(f"{name} mutation did not fail closed:\n{output}")


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
        raise RuntimeError(f"O6h target occurrence changed: {entries!r}")

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
        raise RuntimeError(f"O6h target did not materialize singularly: {record!r}")

    certificate = check_report(target.get("report") or {})
    candidate = target.get("candidate") or {}
    if candidate.get("replacement") != certificate:
        raise RuntimeError("O6h candidate did not preserve the accepted certificate")
    source = (coverage.MATHLIB / MODULE).read_bytes()
    check_mutation(
        "delete-local-def", candidate, source, certificate.replace(LOCAL_DEF_LINE, "", 1)
    )
    check_mutation(
        "swap-with-zeta",
        candidate,
        source,
        certificate.replace(LOCAL_DEF_LINE + ZETA_LINE, ZETA_LINE + LOCAL_DEF_LINE, 1),
    )
    check_mutation(
        "wrong-local", candidate, source, certificate.replace("local_def s", "local_def this", 1)
    )


def main() -> None:
    check_focused_source()
    check_production()
    print("O6h exact local-definition replay gates passed")


if __name__ == "__main__":
    main()
