#!/usr/bin/env python3
"""Focused O6j gate for nested local-definition bridge candidates."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
MODULE = "Mathlib/Algebra/Algebra/Subalgebra/Unitization.lean"
TARGETS = {
    "9725589ca802bdbe": {
        "local": "algHom",
        "firstRule": "AlgHom.val_comp_codRestrict",
        "bytes": 200,
    },
    "1734864b48394331": {
        "local": "starAlgHom",
        "firstRule": "StarAlgHom.subtype_comp_codRestrict",
        "bytes": 216,
    },
}
FIXTURE = ROOT / "Experiment" / "O6jNestedLocalDefProbe.lean"
OUTPUT = ROOT / ".lake" / "o6j-nested-local-def"

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
        "reduce local_def other, o6jWrap_payload",
        "o6jWrap_payload, reduce local_def s",
        "reduce local_def s, o6jWrap_payload",
    ):
        if source.count(anchor) != 1:
            raise RuntimeError(f"focused O6j fixture is missing unique `{anchor}`")
    code, output, _ = coverage.run(
        ["lake", "env", "lean", str(FIXTURE)], timeout=180
    )
    if code != 0:
        raise RuntimeError(f"focused nested-local source failed:\n{output}")
    reports = coverage.parse_recording_reports(output)
    if len(reports) != 1:
        raise RuntimeError(f"focused O6j fixture emitted {len(reports)} reports")
    report = reports[0]
    certificate = report.get("acceptedCertificate")
    encoding = report.get("encoding") or {}
    if (
        report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION
        or report.get("operationallyAdmissible") is not True
        or not isinstance(certificate, str)
        or certificate.count("reduce local_def s") != 1
        or encoding.get("reductionEvents") != 1
        or encoding.get("operationalProgramFailures") != 0
    ):
        raise RuntimeError(f"focused O6j report is not operational: {report!r}")


def check_report(target_id: str, report: dict) -> str:
    spec = TARGETS[target_id]
    local = spec["local"]
    local_line = f"  ↓ reduce local_def {local},\n"
    first_rule_line = f"  {spec['firstRule']},\n"
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
        or certificate.count(local_line) != 1
        or certificate.count(first_rule_line) != 1
    ):
        raise RuntimeError(f"production O6j report is not operational: {report!r}")

    executions = report.get("executions", [])
    trace = executions[0].get("trace", []) if len(executions) == 1 else []
    if (
        report.get("traceLength") != 7
        or len(trace) != 7
        or any(event.get("reduction") is not None for event in trace)
        or any(event.get("encodingKind") != "named_rule" for event in trace)
    ):
        raise RuntimeError(f"O6j changed the raw recorder trace: {report!r}")

    encoding = report.get("encoding") or {}
    expected = {
        "mode": "event",
        "namedRuleEvents": 7,
        "reductionEvents": 1,
        "nextSelectorCount": 8,
        "matchSelectorCount": 0,
        "tickSelectorCount": 0,
        "totalCertificateBytes": spec["bytes"],
    }
    if any(encoding.get(key) != value for key, value in expected.items()):
        raise RuntimeError(f"production O6j encoding changed: {encoding!r}")
    for metric in FORBIDDEN_METRICS:
        if encoding.get(metric, 0) != 0:
            raise RuntimeError(f"production O6j used forbidden metric {metric}: {encoding!r}")
    return certificate


def check_mutation(
    target_id: str, name: str, candidate: dict, source: bytes, replacement: str
) -> None:
    if replacement == candidate.get("replacement"):
        raise RuntimeError(f"{target_id} {name} mutation did not change the certificate")
    mutated = candidate.copy()
    mutated["replacement"] = replacement
    label = f"mutation-{target_id}-{name}"
    attempt = coverage.compile_closure_candidates(
        MODULE, source, [mutated], 180, label=label, keep_copy=True
    )
    if attempt.get("compile") is True:
        raise RuntimeError(f"{target_id} {name} mutation unexpectedly compiled: {attempt!r}")
    log_path = OUTPUT / "closure-attempts" / MODULE / f"{label}.log"
    output = log_path.read_text(encoding="utf-8") if log_path.exists() else ""
    if not any(
        message in output
        for message in (
            "ordered simp rule did not match",
            "without an explicit reduction command",
            "requires a local let declaration",
        )
    ):
        raise RuntimeError(f"{target_id} {name} mutation did not fail closed:\n{output}")


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
        if entry["kind"] in coverage.SUPPORTED_KINDS and entry["id"] in TARGETS
    ]
    if {entry["id"] for entry in entries} != set(TARGETS):
        raise RuntimeError(f"O6j target occurrences changed: {entries!r}")

    record = coverage.run_closure_module(
        MODULE, entries, document["mathlib_revision"], 180, keep_copy=True
    )
    occurrences = {item["id"]: item for item in record.get("occurrences", [])}
    if (
        record.get("complete") is not True
        or (record.get("recording") or {}).get("compile_count") != 1
        or (record.get("aggregate") or {}).get("materialization_compile_count") != 1
    ):
        raise RuntimeError(f"O6j targets did not materialize in one module pass: {record!r}")

    source = (coverage.MATHLIB / MODULE).read_bytes()
    for target_id, spec in TARGETS.items():
        target = occurrences.get(target_id)
        if (
            target is None
            or target.get("terminal_outcome") != "materialized"
            or target.get("materialized_compile") is not True
            or target.get("failure_reason") is not None
        ):
            raise RuntimeError(f"O6j target {target_id} did not materialize: {record!r}")
        certificate = check_report(target_id, target.get("report") or {})
        candidate = target.get("candidate") or {}
        if candidate.get("replacement") != certificate:
            raise RuntimeError(f"O6j candidate {target_id} changed its certificate")
        local_line = f"  ↓ reduce local_def {spec['local']},\n"
        first_rule_line = f"  {spec['firstRule']},\n"
        check_mutation(
            target_id,
            "delete-local-def",
            candidate,
            source,
            certificate.replace(local_line, "", 1),
        )
        check_mutation(
            target_id,
            "swap-order",
            candidate,
            source,
            certificate.replace(
                local_line + first_rule_line, first_rule_line + local_line, 1
            ),
        )
        check_mutation(
            target_id,
            "wrong-local",
            candidate,
            source,
            certificate.replace(f"local_def {spec['local']}", "local_def h1", 1),
        )


def main() -> None:
    check_focused_source()
    check_production()
    print("O6j nested local-definition bridge gates passed")


if __name__ == "__main__":
    main()
