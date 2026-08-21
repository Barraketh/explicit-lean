#!/usr/bin/env python3
"""Check local-name planning on a simproc-deferred migration source."""

from __future__ import annotations

from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "LocalRenameProbe.lean"


def main() -> None:
    code, output, _ = coverage.run(
        ["lake", "env", "lean", str(PROBE)], timeout=180
    )
    reports = coverage.parse_recording_reports(output)
    if code != 0 or len(reports) != 1:
        raise RuntimeError(
            f"local-rename probe failed or emitted an unexpected report count: "
            f"exit={code}, reports={len(reports)}\n{output}"
        )
    report = reports[0]
    if report.get("schema") != "explicitLean.simpRecording":
        raise RuntimeError(f"unexpected local-rename report schema: {report!r}")
    if report.get("schemaVersion") != 10:
        raise RuntimeError(f"unexpected local-rename report version: {report!r}")
    renames = report.get("localRenames")
    if renames != [{"contextIndex": 7, "generatedName": "h_explicit_8_1"}]:
        raise RuntimeError(f"local rename order/collision plan changed: {report!r}")
    if report.get("acceptedCertificate") is not None or report.get("certificate"):
        raise RuntimeError(f"deferred local-rename report exposed accepted source: {report!r}")
    admissibility = report.get("operationalAdmissibility") or {}
    if admissibility.get("code") != "deferred_simproc":
        raise RuntimeError(f"local-rename fixture was not deferred as a simproc: {report!r}")
    certificate = report.get("legacyCertificate")
    if not isinstance(certificate, str) or not certificate.startswith(
        "simp_explicit_rename [7 => h_explicit_8_1]\n"
    ):
        raise RuntimeError(
            "local-rename migration source did not contain the literal rename prefix: "
            f"{report!r}"
        )
    serialized = json.dumps(report, ensure_ascii=False, sort_keys=True)
    forbidden_markers = ("✝", "FVarId", "Syntax.mk", "Expr.mvar", "mvarId")
    leaked = [marker for marker in forbidden_markers if marker in serialized]
    if leaked:
        raise RuntimeError(
            "local-rename report leaked unstable or inaccessible implementation "
            f"identifiers: {leaked!r}"
        )

    print("local rename collision/order planning retained in deferred simproc diagnostics")


if __name__ == "__main__":
    main()
