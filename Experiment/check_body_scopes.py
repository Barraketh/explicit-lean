#!/usr/bin/env python3
"""Focused schema-v6 checks for dynamic body-scope execution ownership."""

from __future__ import annotations

import json
import re

import simp_coverage as coverage


EXPECTED = {
    "f1-shared": ["committed", "committed"],
    "f1-all-goals": ["committed", "committed"],
    "f1-repeat": ["committed", "committed"],
    "f1-first": ["backtracked", "committed"],
}


def main() -> None:
    code, output, elapsed = coverage.run(
        [
            "lake",
            "env",
            "lean",
            "-DmaxHeartbeats=0",
            "Experiment/BodyScopeProbe.lean",
        ],
        timeout=180,
    )
    if code != 0:
        raise RuntimeError(f"body-scope fixture failed after {elapsed:.2f}s:\n{output}")
    reports = coverage.parse_recording_reports(output)
    if len(reports) != len(EXPECTED):
        raise RuntimeError(f"expected one report per body-scoped occurrence: {reports!r}")
    by_id = {report.get("occurrenceId"): report for report in reports}
    if set(by_id) != set(EXPECTED):
        raise RuntimeError(f"unexpected body-scope occurrence IDs: {sorted(by_id)!r}")
    serialized = json.dumps(reports, ensure_ascii=False, sort_keys=True)
    forbidden = re.compile(r"FVarId|Syntax\.mk|Expr\.mvar|mvarId|\?m\.[0-9]+")
    if forbidden.search(serialized):
        raise RuntimeError("body-scope report contains a raw internal identity")
    for occurrence_id, dispositions in EXPECTED.items():
        report = by_id[occurrence_id]
        if report.get("schema") != "explicitLean.simpRecording":
            raise RuntimeError(f"unexpected report schema: {report!r}")
        if report.get("schemaVersion") != 6:
            raise RuntimeError(f"unexpected report version: {report!r}")
        if not isinstance(report.get("bodyScopeId"), str) or not report["bodyScopeId"]:
            raise RuntimeError(f"missing body scope identity: {report!r}")
        executions = report.get("executions", [])
        if [item.get("disposition") for item in executions] != dispositions:
            raise RuntimeError(f"unexpected dispositions for {occurrence_id}: {report!r}")
        if [item.get("executionIndex") for item in executions] != list(range(len(executions))):
            raise RuntimeError(f"execution indexes are not contiguous: {report!r}")
        if any(not item.get("attemptToken") for item in executions):
            raise RuntimeError(f"missing deterministic attempt token: {report!r}")
        for execution in executions:
            for field in (
                "certificate",
                "certificateBytes",
                "encodingStatus",
                "encoding",
                "initialState",
                "finalState",
                "subjects",
                "trace",
            ):
                if field not in execution:
                    raise RuntimeError(f"execution missing owned field {field}: {report!r}")
        if len(executions) > 1:
            if report.get("certificate") != "" or report.get("certificateBytes") != 0:
                raise RuntimeError(f"multi-execution report fabricated a top certificate: {report!r}")
            if report.get("encodingStatus") != "body_rewrite_required":
                raise RuntimeError(f"multi-execution status is not body rewrite: {report!r}")
            if report.get("recordingReason") != "multiple_dynamic_executions":
                raise RuntimeError(f"missing multiple-execution reason: {report!r}")
            if report.get("traceLength") != sum(len(item.get("trace", [])) for item in executions):
                raise RuntimeError(f"trace aggregate is not a sum: {report!r}")
    print("body-scope execution checks passed")


if __name__ == "__main__":
    main()
