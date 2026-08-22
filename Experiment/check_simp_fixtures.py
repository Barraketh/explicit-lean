#!/usr/bin/env python3
"""Check the Package B simproc recording and closed replay fixture."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "SimprocFallbackProbe.lean"
OUTPUT = ROOT / ".lake" / "simp-explicit-fixtures"
MATERIALIZED = OUTPUT / "SimprocFallbackMaterialized.lean"


def main() -> None:
    code, output, _ = coverage.run(
        ["lake", "env", "lean", str(PROBE)], timeout=180
    )
    reports = coverage.parse_recording_reports(output)
    if code != 0 or len(reports) != 1:
        raise RuntimeError(
            f"simproc probe failed or emitted an unexpected report count: "
            f"exit={code}, reports={len(reports)}\n{output}"
        )
    report = reports[0]
    if report.get("schema") != "explicitLean.simpRecording":
        raise RuntimeError(f"unexpected simproc report schema: {report!r}")
    if report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION:
        raise RuntimeError(f"unexpected simproc report version: {report!r}")
    if report.get("localRenames") != []:
        raise RuntimeError(f"ordinary simproc encoding unexpectedly renamed locals: {report!r}")
    if report.get("encodingStatus") != "deferred":
        raise RuntimeError(f"simproc recording was not deferred: {report!r}")
    if report.get("operationallyAdmissible") is not False:
        raise RuntimeError(f"simproc fallback was marked operationally admissible: {report!r}")
    admissibility = report.get("operationalAdmissibility") or {}
    if admissibility.get("code") != "deferred_simproc":
        raise RuntimeError(f"simproc fallback classification changed: {report!r}")
    if report.get("acceptedCertificate") is not None or report.get("certificate"):
        raise RuntimeError(f"simproc fallback exposed an accepted certificate: {report!r}")
    if (report.get("validation") or {}).get("certificate") is not None:
        raise RuntimeError(f"simproc fallback exposed validation certificate metadata: {report!r}")
    if report.get("legacyCertificate") is not None:
        raise RuntimeError(f"simproc fallback retained a proof source: {report!r}")
    encoding = report.get("encoding") or {}
    if encoding.get("deferredSimprocEvents") != 1 or encoding.get("generatedSimprocEvents") != 0:
        raise RuntimeError(f"simproc fallback was not deferred before proof encoding: {report!r}")
    events = [
        event
        for execution in report.get("executions", [])
        for event in execution.get("trace", [])
    ]
    simproc_events = [
        event
        for event in events
        if event.get("encodingKind") == "deferred_simproc"
        and event.get("encodingReason") == "simproc"
    ]
    if len(simproc_events) != 1:
        raise RuntimeError(f"simproc fallback event encoding was not reported: {report!r}")
    if simproc_events[0].get("selectorKind") is not None or simproc_events[0].get("selectorValue") is not None:
        raise RuntimeError(f"deferred simproc event exposed an executable selector: {report!r}")
    source = PROBE.read_text(encoding="utf-8")
    needle = "simp_explicit? [↓pushFun]"
    if source.count(needle) != 1:
        raise RuntimeError("simproc probe tactic occurrence was not unique")
    print("simproc fallback was classified deferred and withheld from materialization")


if __name__ == "__main__":
    main()
