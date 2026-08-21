#!/usr/bin/env python3
"""Check one named-hypothesis location recording and materialization."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import textwrap

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "ContextRecordProbe.lean"
OUTPUT = ROOT / ".lake" / "simp-explicit-context-record"


def main() -> None:
    code, output, _ = coverage.run(
        ["lake", "env", "lean", str(PROBE)], timeout=180
    )
    if code != 0:
        raise RuntimeError(f"context recording probe failed: exit={code}\n{output}")
    reports = coverage.parse_recording_reports(output)
    if len(reports) != 1:
        raise RuntimeError(f"expected one context report, found {len(reports)}\n{output}")
    report = reports[0]
    if report.get("schema") != "explicitLean.simpRecording":
        raise RuntimeError(f"unexpected report schema: {report.get('schema')!r}")
    if report.get("schemaVersion") != 8:
        raise RuntimeError(f"unexpected report schema version: {report.get('schemaVersion')!r}")
    certificate = report.get("certificate", "")
    if "simp_explicit_context" not in certificate or "at h" not in certificate:
        raise RuntimeError(f"report did not emit a named context certificate: {certificate!r}")
    if report.get("localRenames") != []:
        raise RuntimeError("accessible named-hypothesis case unexpectedly renamed locals")

    serialized = json.dumps(report, ensure_ascii=False)
    for forbidden in (
        "✝",
        "FVarId",
        "Syntax.mk",
        "Expr.mvar",
        "mvarId",
        "_fvar.",
        "?m.",
        "«",
        "»",
    ):
        if forbidden in serialized:
            raise RuntimeError(f"persistent report leaked forbidden marker {forbidden!r}")

    executions = report.get("executions", [])
    if len(executions) != 1:
        raise RuntimeError("expected one recording execution")
    execution = executions[0]
    subjects = execution.get("subjects", [])
    if len(subjects) != 1:
        raise RuntimeError(f"expected one named subject summary, found {len(subjects)}")
    summary = subjects[0]
    subject = summary.get("subject", {})
    if subject != {"kind": "local", "name": "h", "contextIndex": 2}:
        raise RuntimeError(f"unexpected subject identity: {subject!r}")
    if not summary.get("initial", {}).get("fingerprint"):
        raise RuntimeError("subject summary omitted its initial fingerprint")
    if not summary.get("result", {}).get("fingerprint"):
        raise RuntimeError("subject summary omitted its result fingerprint")
    transport = summary.get("transport")
    if not transport or transport.get("originalContextIndex") != 2:
        raise RuntimeError(f"missing original transport identity: {transport!r}")
    if transport.get("originalName") != "h" or not transport.get("originalCleared"):
        raise RuntimeError(f"unexpected original transport: {transport!r}")
    if transport.get("resultingContextIndex") is None or transport.get("resultingName") != "h":
        raise RuntimeError(f"missing resulting transport identity: {transport!r}")

    trace = execution.get("trace", [])
    if len(trace) != 2 or any(event.get("subject") != subject for event in trace):
        raise RuntimeError(f"trace was not flattened with local subject identity: {trace!r}")
    if any(event.get("encodingKind") != "named_rule" for event in trace):
        raise RuntimeError(f"expected named-rule event encodings: {trace!r}")
    if any(event.get("selectorKind") != "next" for event in trace):
        raise RuntimeError(f"expected position-free next selectors: {trace!r}")
    validation = report.get("validation")
    if not validation or validation.get("schemaVersion") != 8:
        raise RuntimeError("missing schema-v7 validation envelope")

    OUTPUT.mkdir(parents=True, exist_ok=True)
    source = PROBE.read_text(encoding="utf-8")
    anchor = """  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, eq_self] at h"""
    if source.count(anchor) != 1:
        raise RuntimeError("context recording probe materialization anchor is not unique")
    materialized = source.replace(anchor, textwrap.indent(certificate, "  "), 1)
    destination = OUTPUT / "ContextRecordMaterialized.lean"
    destination.write_text(materialized, encoding="utf-8")
    code, materialized_output, _ = coverage.run(
        ["lake", "env", "lean", str(destination)], timeout=180
    )
    if code != 0:
        raise RuntimeError(
            f"materialized named context certificate failed: exit={code}\n{materialized_output}"
        )
    print("named-hypothesis context recording, schema-v7 transport, and materialization passed")


if __name__ == "__main__":
    main()
