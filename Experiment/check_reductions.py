#!/usr/bin/env python3
"""Check O2a reduction replay and mutation fixtures."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "ReductionProbe.lean"
OUTPUT = ROOT / ".lake" / "simp-explicit-reduction-fixtures"


def run_probe(path: Path) -> tuple[int, str]:
    code, output, _ = coverage.run(["lake", "env", "lean", str(path)], timeout=180)
    return code, output


def expect_failure(name: str, source: str, needle: str | None = None) -> None:
    path = OUTPUT / f"Reduction_{name}.lean"
    path.write_text(source, encoding="utf-8")
    code, output = run_probe(path)
    if code == 0:
        raise RuntimeError(f"{name} mutation unexpectedly compiled")
    if needle is not None and needle not in output:
        raise RuntimeError(
            f"{name} mutation lost its diagnostic {needle!r}:\n{output}"
        )


def main() -> None:
    source = PROBE.read_text(encoding="utf-8")
    required = [
        "reduce delta reductionDelta",
        "reduce beta",
        "reduce zeta",
        "reduce iota",
        "reduce projection ReductionInductive 0",
        "reduce eta",
        "match 99 => reduce delta reductionDelta",
        "reduce delta reductionDelta, reduce delta reductionDelta",
        "simp_explicit leave_open []",
        "guard_target =ₛ (fun x : Nat => x + 1) n = 1 + n",
        "fail_if_success simp_explicit leave_open []",
    ]
    for needle in required:
        if needle not in source:
            raise RuntimeError(f"reduction fixture is missing `{needle}`")

    code, output = run_probe(PROBE)
    if code != 0:
        raise RuntimeError(f"reduction fixture failed: exit={code}\n{output}")
    reports = coverage.parse_recording_reports(output)
    if len(reports) != 2:
        raise RuntimeError(f"reduction recorder fixtures emitted {len(reports)} reports")
    for report in reports:
        if report.get("schema") != "explicitLean.simpRecording":
            raise RuntimeError(f"unexpected reduction report schema: {report!r}")
        if report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION:
            raise RuntimeError(f"unexpected reduction report version: {report!r}")

    delta_reports = [
        report for report in reports if "reductionDelta" in report.get("originalSyntax", "")
    ]
    if len(delta_reports) != 1:
        raise RuntimeError(f"named-delta recorder fixture was not unique: {reports!r}")
    delta_report = delta_reports[0]
    delta_events = [
        event
        for execution in delta_report.get("executions", [])
        for event in execution.get("trace", [])
        if event.get("reduction") is not None
    ]
    if len(delta_events) != 1 or delta_events[0].get("reduction") != {
        "kind": "delta",
        "name": "reductionDelta",
        "field": None,
    }:
        raise RuntimeError(f"named-delta recorder event changed: {delta_report!r}")
    if delta_events[0].get("origins"):
        raise RuntimeError(f"named-delta recorder invented theorem provenance: {delta_report!r}")
    if "reduce delta reductionDelta" not in delta_report.get("certificate", ""):
        raise RuntimeError(f"named-delta source printer omitted the reduction: {delta_report!r}")
    delta_encoding = delta_report.get("encoding") or {}
    if (
        delta_encoding.get("reductionEvents") != 1
        or delta_encoding.get("deltaReductionEvents") != 1
        or delta_encoding.get("namedRuleEvents") != 0
    ):
        raise RuntimeError(f"named-delta metrics changed: {delta_report!r}")

    report = next(
        report for report in reports if report is not delta_report
    )
    # Lean 4.32.2's pinned private reduceStep still has no eta branch.  The
    # replay command is covered above; recording must not invent an eta event.
    events = [
        event
        for execution in report.get("executions", [])
        for event in execution.get("trace", [])
    ]
    if any((event.get("reduction") or {}).get("kind") == "eta" for event in events):
        raise RuntimeError(f"pinned recorder unexpectedly observed eta: {report!r}")
    encoding = report.get("encoding") or {}
    if encoding.get("reductionEvents") != 0 or encoding.get("deltaReductionEvents") != 0:
        raise RuntimeError(f"eta-only recorder report invented reduction metrics: {report!r}")

    OUTPUT.mkdir(parents=True, exist_ok=True)
    expect_failure(
        "wrong-name",
        source.replace(
            "simp_explicit [reduce delta reductionDelta]",
            "simp_explicit [reduce delta notReductionDelta]",
            1,
        ),
        "ordered simp rule did not match",
    )
    expect_failure(
        "wrong-kind",
        source.replace(
            "simp_explicit [reduce beta]",
            "simp_explicit [reduce zeta]",
            1,
        ),
        "ordered simp rule did not match",
    )
    expect_failure(
        "wrong-selector",
        source.replace(
            "simp_explicit [reduce delta reductionDelta]",
            "simp_explicit [match 99 => reduce delta reductionDelta]",
            1,
        ),
        "match ordinal 99 not reached",
    )
    expect_failure(
        "malformed-projection-field",
        source.replace(
            "reduce projection ReductionInductive 0",
            "reduce projection ReductionInductive bad",
            1,
        ),
    )
    print("O2a reduction replay, rollback mutations, and pinned eta observation passed")


if __name__ == "__main__":
    main()
