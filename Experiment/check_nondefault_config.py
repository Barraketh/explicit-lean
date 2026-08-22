#!/usr/bin/env python3
"""Regression for recording nondefault simp configuration provenance."""

from __future__ import annotations

from collections import Counter
from types import SimpleNamespace
import textwrap

import simp_coverage as coverage


MODULE = "Mathlib/Algebra/Algebra/Bilinear.lean"
FIXTURE = coverage.ROOT / "Experiment" / "NondefaultConfigProbe.lean"
CONTEXTUAL_ID = "af1f3238d87dcae6"
CONTEXT_LOCAL_REPORT_ID = "5795dc0135cc7db3"
MISSING_TRANSITION_ID = "a532105822c38f91"
TARGET_ID = "nd-target"
HYPOTHESIS_ID = "nd-hyp"
MULTI_GOAL_ID = "nd-multi"
MULTI_BODY_ID = "nd-multi-body"
EXPECTED_SOURCES = {
    CONTEXTUAL_ID: "simp +contextual [mul', smul_tmul', mul_assoc]",
    CONTEXT_LOCAL_REPORT_ID: "simp +contextual [mul_add]",
}


def check_configuration(report: dict, identifier: str) -> None:
    if report.get("schema") != "explicitLean.simpRecording":
        raise RuntimeError(f"{identifier} report schema changed: {report!r}")
    if report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION:
        raise RuntimeError(f"{identifier} report schema version changed: {report!r}")
    configuration = report.get("configuration")
    normalized = configuration.get("normalized") if isinstance(configuration, dict) else None
    if not isinstance(configuration, dict) or configuration.get("optConfig") != "+contextual":
        raise RuntimeError(f"{identifier} optConfig provenance changed: {report!r}")
    if not isinstance(normalized, dict) or normalized.get("contextual") is not True:
        raise RuntimeError(f"{identifier} normalized contextual configuration missing: {report!r}")


def check_validated_certificates(report: dict, identifier: str) -> list[str]:
    certificates: list[str] = []
    for execution in report.get("executions", []):
        if not isinstance(execution, dict):
            continue
        if execution.get("result") != "succeeded":
            continue
        if execution.get("encodingStatus") != "validated":
            continue
        certificate = execution.get("certificate")
        if not isinstance(certificate, str) or not certificate:
            raise RuntimeError(f"{identifier} validated execution has no certificate: {report!r}")
        if "+contextual" in certificate:
            raise RuntimeError(f"{identifier} certificate retained configuration mode: {report!r}")
        certificates.append(certificate)
    if not certificates:
        raise RuntimeError(f"{identifier} has no validated certificate: {report!r}")
    return certificates


def check_fixture() -> None:
    code, output, _ = coverage.run(
        ["lake", "env", "lean", str(FIXTURE)], timeout=180
    )
    if code != 0:
        raise RuntimeError(f"nondefault configuration fixture failed:\n{output}")
    reports = coverage.parse_recording_reports(output)
    by_id = {report.get("occurrenceId"): report for report in reports}
    expected_ids = {TARGET_ID, HYPOTHESIS_ID, MULTI_GOAL_ID}
    if set(by_id) != expected_ids:
        raise RuntimeError(f"nondefault fixture occurrence IDs changed: {sorted(by_id)!r}")

    target = by_id[TARGET_ID]
    check_configuration(target, TARGET_ID)
    if target.get("closesGoal") is not True:
        raise RuntimeError(f"target configuration fixture did not close: {target!r}")
    target_certificates = check_validated_certificates(target, TARGET_ID)

    hypothesis = by_id[HYPOTHESIS_ID]
    check_configuration(hypothesis, HYPOTHESIS_ID)
    subjects = hypothesis.get("executions", [{}])[0].get("subjects", [])
    subject = subjects[0].get("subject") if len(subjects) == 1 else None
    if (
        not isinstance(subject, dict)
        or subject.get("kind") != "local"
        or subject.get("name") != "h"
        or not isinstance(subject.get("contextIndex"), int)
    ):
        raise RuntimeError(f"named-hypothesis subject changed: {hypothesis!r}")
    hypothesis_certificates = check_validated_certificates(hypothesis, HYPOTHESIS_ID)

    multi = by_id[MULTI_GOAL_ID]
    check_configuration(multi, MULTI_GOAL_ID)
    if multi.get("bodyScopeId") != MULTI_BODY_ID:
        raise RuntimeError(f"multi-goal body scope changed: {multi!r}")
    executions = multi.get("executions", [])
    if [execution.get("disposition") for execution in executions] != [
        "committed",
        "committed",
    ]:
        raise RuntimeError(f"multi-goal configuration executions changed: {multi!r}")
    multi_certificates = check_validated_certificates(multi, MULTI_GOAL_ID)
    if len(multi_certificates) != 2:
        raise RuntimeError(f"multi-goal did not retain two validated certificates: {multi!r}")

    source = FIXTURE.read_text(encoding="utf-8")
    replacements = (
        (
            '    set_option explicitLean.simpExplicit.occurrenceId "nd-target" in\n'
            "      simp_explicit? +contextual [Nat.add_zero]\n",
            target_certificates[0],
        ),
        (
            '    set_option explicitLean.simpExplicit.occurrenceId "nd-hyp" in\n'
            "      simp_explicit? +contextual [Nat.add_zero] at h\n",
            hypothesis_certificates[0],
        ),
    )
    for anchor, certificate in replacements:
        if source.count(anchor) != 1:
            raise RuntimeError(f"fixture materialization anchor is not unique: {anchor!r}")
        option_line = anchor.splitlines(keepends=True)[0]
        source = source.replace(
            anchor, option_line + textwrap.indent(certificate, "      ") + "\n", 1
        )
    materialized = coverage.OUTPUT / "fixture" / "NondefaultConfigMaterialized.lean"
    materialized.parent.mkdir(parents=True, exist_ok=True)
    materialized.write_text(source, encoding="utf-8")
    code, materialized_output, _ = coverage.run(
        ["lake", "env", "lean", str(materialized)], timeout=180
    )
    if code != 0:
        raise RuntimeError(
            f"target/named configuration certificates did not materialize:\n{materialized_output}"
        )


def check_production() -> None:
    coverage.OUTPUT = coverage.ROOT / ".lake" / "g-nondefault-config"
    coverage.INVENTORY = coverage.OUTPUT / "inventory.json"
    coverage.RESULTS = coverage.OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = coverage.OUTPUT / "aggregate-results"


def main() -> None:
    check_fixture()
    check_production()
    coverage.inventory(
        SimpleNamespace(modules=[MODULE], timeout=600, batch_size=1000)
    )
    document = coverage.load_inventory()
    entries = [
        entry
        for entry in document["entries"]
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    if len(entries) != 10:
        raise RuntimeError(f"Bilinear supported inventory changed: {entries!r}")
    by_id = {entry["id"]: entry for entry in entries}
    if set(EXPECTED_SOURCES) - set(by_id):
        raise RuntimeError(f"Bilinear contextual IDs changed: {sorted(by_id)!r}")
    for identifier, source in EXPECTED_SOURCES.items():
        if by_id[identifier].get("source") != source:
            raise RuntimeError(
                f"Bilinear source changed for {identifier}: {by_id[identifier]!r}"
            )

    record = coverage.run_closure_module(
        MODULE,
        entries,
        document["mathlib_revision"],
        180,
        keep_copy=True,
    )
    aggregate = record.get("aggregate", {})
    if aggregate.get("compile") is not True:
        raise RuntimeError(f"Bilinear aggregate did not compile: {record!r}")
    if aggregate.get("closure_complete") is not False:
        raise RuntimeError(f"Bilinear unexpectedly passed the O1 operational gate: {record!r}")
    if aggregate.get("terminal_classification_complete") is not False:
        raise RuntimeError(f"Bilinear terminal gate unexpectedly completed: {record!r}")

    occurrences = {occurrence["id"]: occurrence for occurrence in record["occurrences"]}
    outcomes = Counter(
        occurrence.get("terminal_outcome")
        for occurrence in record["occurrences"]
    )
    if outcomes != Counter({"materialized": 9, "coverage_failure": 1}):
        raise RuntimeError(f"Bilinear terminal outcomes changed: {outcomes!r}")

    contextual = occurrences.get(CONTEXTUAL_ID)
    if contextual is None or contextual.get("terminal_outcome") != "materialized":
        raise RuntimeError(f"contextual named-delta occurrence regressed: {record!r}")
    report = contextual.get("report") or {}
    certificate = report.get("acceptedCertificate") or report.get("certificate")
    if (
        contextual.get("failure_reason") is not None
        or not isinstance(contextual.get("candidate"), dict)
        or not isinstance(certificate, str)
        or "reduce delta LinearMap.mul'" not in certificate
        or report.get("legacyCertificate") is not None
    ):
        raise RuntimeError(f"contextual named-delta materialization changed: {contextual!r}")
    check_configuration(report, CONTEXTUAL_ID)

    context_local = occurrences.get(CONTEXT_LOCAL_REPORT_ID)
    if (
        context_local is None
        or context_local.get("terminal_outcome") != "coverage_failure"
        or context_local.get("failure_reason") != "unidentified_theorem_application"
    ):
        raise RuntimeError(
            "context-local report classification changed: "
            f"outcome={context_local and context_local.get('terminal_outcome')!r}, "
            f"reason={context_local and context_local.get('failure_reason')!r}"
        )
    context_local_report = context_local.get("report") or {}
    if context_local_report.get("acceptedCertificate") is not None:
        raise RuntimeError(f"conservative contextual report was accepted: {context_local!r}")
    if (
        context_local_report.get("traceAvailable") is not True
        or not context_local_report.get("traceLength")
        or context_local_report.get("failureCategory") is not None
    ):
        raise RuntimeError("context-local raw trace was not retained and classified")
    check_configuration(context_local_report, CONTEXT_LOCAL_REPORT_ID)

    missing = occurrences.get(MISSING_TRANSITION_ID)
    if (
        missing is None
        or missing.get("terminal_outcome") != "materialized"
        or missing.get("failure_reason") is not None
    ):
        raise RuntimeError(f"Bilinear named-delta closure changed: {record!r}")
    missing_report = missing.get("report") or {}
    missing_certificate = missing_report.get("acceptedCertificate") or missing_report.get("certificate")
    if (
        not isinstance(missing.get("candidate"), dict)
        or not isinstance(missing_certificate, str)
        or "reduce delta LinearMap.mul'" not in missing_certificate
        or missing_report.get("operationalAdmissibility", {}).get("code") != "accepted"
    ):
        raise RuntimeError(f"Bilinear named-delta certificate changed: {missing!r}")

    print("nondefault configuration provenance and Bilinear O2a named-delta gate passed")


if __name__ == "__main__":
    main()
