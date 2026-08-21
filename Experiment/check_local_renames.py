#!/usr/bin/env python3
"""Check Package E local-name planning and literal closed replay."""

from __future__ import annotations

from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "LocalRenameProbe.lean"
OUTPUT = ROOT / ".lake" / "simp-explicit-local-renames"
MATERIALIZED = OUTPUT / "LocalRenameMaterialized.lean"


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
    if report.get("schemaVersion") != 7:
        raise RuntimeError(f"unexpected local-rename report version: {report!r}")
    renames = report.get("localRenames")
    if renames != [{"contextIndex": 7, "generatedName": "h_explicit_2"}]:
        raise RuntimeError(f"local rename order/collision plan changed: {report!r}")
    certificate = report.get("certificate")
    if not isinstance(certificate, str) or not certificate.startswith(
        "rename_i h_explicit_2\n"
    ):
        raise RuntimeError(
            "local-rename certificate did not contain the literal rename prefix: "
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

    source = PROBE.read_text(encoding="utf-8")
    needle = "simp_explicit? [List.drop_append, IH]"
    if source.count(needle) != 1:
        raise RuntimeError("local-rename probe tactic occurrence was not unique")
    materialized = source.replace(needle, certificate.replace("\n", "\n        "), 1)
    OUTPUT.mkdir(parents=True, exist_ok=True)
    MATERIALIZED.write_text(materialized, encoding="utf-8")
    replay_code, replay_output, _ = coverage.run(
        ["lake", "env", "lean", str(MATERIALIZED)], timeout=180
    )
    if replay_code != 0:
        raise RuntimeError(
            "literal rename prefix plus certificate failed closed replay compilation:\n"
            + replay_output
        )
    print("local rename collision/order planning and closed replay passed")


if __name__ == "__main__":
    main()
