#!/usr/bin/env python3
"""Check the Package E context-location recording/materialization matrix."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import textwrap

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "ContextLocationProbe.lean"
OUTPUT = ROOT / ".lake" / "simp-explicit-context-locations"


ANCHORS = [
    """  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, Nat.mul_one, eq_self] at hAdd hMul ⊢""",
    """  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, Nat.mul_one, eq_self] at hMul hAdd ⊢""",
    """  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, eq_self] at h k""",
    """  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [eq_self] at ⊢""",
    """  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, eq_self] at *""",
    """example (h : False) : True := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? only [] at h""",
    """example (h : True) : True := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? only [] at h""",
    """      set_option explicitLean.simpExplicit.report true in
        simp_explicit? [List.drop_append, IH] at *""",
]


def check_subjects(report: dict, expected: list[tuple[str, str]]) -> None:
    execution = report.get("executions", [])[0]
    subjects = execution.get("subjects", [])
    actual = [
        (subject.get("subject", {}).get("kind"), subject.get("subject", {}).get("name"))
        for subject in subjects
    ]
    if actual != expected:
        raise RuntimeError(f"unexpected subject order: expected {expected!r}, got {actual!r}")
    for summary in subjects:
        if not summary.get("initial", {}).get("fingerprint"):
            raise RuntimeError("subject summary omitted initial fingerprint")
        if not summary.get("result", {}).get("fingerprint"):
            raise RuntimeError("subject summary omitted result fingerprint")
        if summary.get("subject", {}).get("kind") == "local":
            transport = summary.get("transport")
            if not transport or transport.get("originalContextIndex") is None:
                raise RuntimeError(f"local subject omitted transport identity: {summary!r}")
            if transport.get("originalName") != summary["subject"].get("name"):
                raise RuntimeError(f"transport name does not match subject: {summary!r}")


def main() -> None:
    code, output, _ = coverage.run(["lake", "env", "lean", str(PROBE)], timeout=300)
    reports = coverage.parse_recording_reports(output)
    if code != 0 or len(reports) != len(ANCHORS):
        raise RuntimeError(
            f"context location probe failed or emitted {len(reports)} reports "
            f"instead of {len(ANCHORS)}: exit={code}\n{output}"
        )
    source = PROBE.read_text(encoding="utf-8")
    for anchor in ANCHORS:
        if source.count(anchor) != 1:
            raise RuntimeError(f"context location anchor is not unique: {anchor!r}")

    expected_subjects = [
        [("local", "hAdd"), ("local", "hMul"), ("target", "target")],
        [("local", "hMul"), ("local", "hAdd"), ("target", "target")],
        [("local", "h"), ("local", "k")],
        [("target", "target")],
        [("local", "h"), ("target", "target")],
        [("local", "h")],
        [("local", "h")],
        [("local", "IH"), ("local", "h_explicit_1"), ("target", "target")],
    ]
    for index, (report, expected) in enumerate(zip(reports, expected_subjects)):
        if report.get("schema") != "explicitLean.simpRecording" or report.get("schemaVersion") != 5:
            raise RuntimeError(f"report {index} is not schema-v5: {report!r}")
        check_subjects(report, expected)
        certificate = report.get("certificate", "")
        if "at *" in certificate or "simp_explicit_context" not in certificate:
            raise RuntimeError(f"report {index} printed an invalid context certificate")
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
                raise RuntimeError(f"report {index} leaked forbidden marker {forbidden!r}")
        if report.get("positionsNeeded") != (
            report.get("encoding", {}).get("tickSelectorCount", 0) > 0
        ):
            raise RuntimeError(f"report {index} has inconsistent position metrics")
        if index == 3 and expected != [("target", "target")]:
            raise RuntimeError("target-only fixture was not selected")
        if index == 5 and not report.get("closesGoal"):
            raise RuntimeError("local-closure fixture did not report closure")
        if index == 6:
            summary = report["executions"][0]["subjects"][0]
            if summary.get("eventCount") != 0:
                raise RuntimeError("zero-event fixture recorded a semantic event")
        if index == 7:
            renames = report.get("localRenames")
            if renames != [{"contextIndex": 7, "generatedName": "h_explicit_2"}]:
                raise RuntimeError(f"stable context rename plan changed: {renames!r}")
            if not certificate.startswith("rename_i h_explicit_2\n"):
                raise RuntimeError("stable context certificate omitted rename_i prefix")

    OUTPUT.mkdir(parents=True, exist_ok=True)
    for index, (anchor, report) in enumerate(zip(ANCHORS, reports)):
        set_option_line = next(
            line for line in anchor.splitlines() if "set_option" in line
        )
        indent = set_option_line[: len(set_option_line) - len(set_option_line.lstrip())]
        replacement = textwrap.indent(report["certificate"], indent)
        if anchor.startswith("example "):
            prefix = anchor.split("set_option", 1)[0].rstrip()
            replacement = prefix + "\n" + replacement
        materialized = source.replace(anchor, replacement, 1)
        destination = OUTPUT / f"ContextLocation_{index}.lean"
        destination.write_text(materialized, encoding="utf-8")
        replay_code, replay_output, _ = coverage.run(
            ["lake", "env", "lean", str(destination)], timeout=300
        )
        if replay_code != 0:
            raise RuntimeError(
                f"materialized context report {index} failed closed compilation:\n"
                + replay_output
            )
    print("context location order, dependent transport, closure, rename, and materialization passed")


if __name__ == "__main__":
    main()
