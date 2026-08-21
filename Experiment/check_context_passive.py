#!/usr/bin/env python3
"""Check passive location recording is isolated from the real simp run."""

from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "ContextPassiveProbe.lean"


def main() -> None:
    code, output, _ = coverage.run(["lake", "env", "lean", str(PROBE)], timeout=180)
    if code != 0:
        raise RuntimeError(f"passive context probe failed: exit={code}\n{output}")
    reports = coverage.parse_recording_reports(output)
    if len(reports) != 1:
        raise RuntimeError(f"passive context emitted {len(reports)} reports instead of one")
    if "Try this deterministic replay" in output:
        raise RuntimeError("passive context emitted a suggestion")
    report = reports[0]
    if report.get("schema") != "explicitLean.simpRecording" or report.get("schemaVersion") != 5:
        raise RuntimeError("passive context report is not schema-v5")
    if report.get("encodingStatus") != "validated":
        raise RuntimeError(f"passive context report was not validated: {report!r}")
    execution = report.get("executions", [])[0]
    subjects = execution.get("subjects", [])
    if [(s.get("subject", {}).get("kind"), s.get("subject", {}).get("name")) for s in subjects] != [
        ("local", "h")
    ]:
        raise RuntimeError(f"unexpected passive subject summary: {subjects!r}")
    transport = subjects[0].get("transport", {})
    if not transport.get("originalCleared") or transport.get("resultingName") != "h":
        raise RuntimeError(f"passive transport did not describe the real simp mutation: {transport!r}")
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
            raise RuntimeError(f"passive report leaked forbidden marker {forbidden!r}")
    print("passive context recording rolled back, reported once, and executed original simp once")


if __name__ == "__main__":
    main()
