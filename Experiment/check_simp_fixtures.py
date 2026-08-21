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
    if report.get("schemaVersion") != 7:
        raise RuntimeError(f"unexpected simproc report version: {report!r}")
    if report.get("localRenames") != []:
        raise RuntimeError(f"ordinary simproc encoding unexpectedly renamed locals: {report!r}")
    if report.get("encodingStatus") != "validated":
        raise RuntimeError(f"simproc recording was not validated: {report!r}")
    encoding = report.get("encoding") or {}
    if encoding.get("generatedSimprocEvents") != 1:
        raise RuntimeError(f"simproc fallback count was not one: {report!r}")
    if (
        encoding.get("nextSelectorCount", 0) < 1
        or encoding.get("matchSelectorCount") != 0
        or encoding.get("tickSelectorCount") != 0
    ):
        raise RuntimeError(f"simproc certificate did not report a selector-free next event: {report!r}")
    events = [
        event
        for execution in report.get("executions", [])
        for event in execution.get("trace", [])
    ]
    simproc_events = [
        event
        for event in events
        if event.get("encodingKind") == "generated_proof"
        and event.get("encodingReason") == "simproc"
    ]
    if len(simproc_events) != 1:
        raise RuntimeError(f"simproc fallback event encoding was not reported: {report!r}")
    if simproc_events[0].get("selectorKind") != "next" or simproc_events[0].get("selectorValue") is not None:
        raise RuntimeError(f"simproc event did not report a nullable next selector: {report!r}")
    if any(event.get("selectorKind") != "next" or event.get("selectorValue") is not None for event in events):
        raise RuntimeError(f"simple certificate did not report next selectors for every event: {report!r}")
    certificate = report.get("certificate")
    if not isinstance(certificate, str) or not certificate:
        raise RuntimeError(f"simproc report did not contain a certificate: {report!r}")
    if "match " in certificate or "tick " in certificate:
        raise RuntimeError(f"simple simproc certificate unexpectedly emitted a positional selector: {report!r}")
    if "pushFun" in certificate:
        raise RuntimeError("simproc certificate still depends on ambient pushFun")

    source = PROBE.read_text(encoding="utf-8")
    needle = "simp_explicit? [↓pushFun]"
    if source.count(needle) != 1:
        raise RuntimeError("simproc probe tactic occurrence was not unique")
    replacement = certificate.replace("\n", "\n  ")
    materialized = source.replace(needle, replacement, 1)
    OUTPUT.mkdir(parents=True, exist_ok=True)
    MATERIALIZED.write_text(materialized, encoding="utf-8")
    replay_code, replay_output, _ = coverage.run(
        ["lake", "env", "lean", str(MATERIALIZED)], timeout=180
    )
    if replay_code != 0:
        raise RuntimeError(
            "materialized simproc certificate failed closed replay compilation:\n"
            + replay_output
        )
    print("simproc fallback recording and closed replay passed")


if __name__ == "__main__":
    main()
