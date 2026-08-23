#!/usr/bin/env python3
"""Check O2b reduction observation, replay, and mutation fixtures."""

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
    if len(reports) != 7:
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

    def trace(report: dict) -> list[dict]:
        return [
            event
            for execution in report.get("executions", [])
            for event in execution.get("trace", [])
        ]

    def reduction_events(report: dict) -> list[dict]:
        return [event for event in trace(report) if event.get("reduction") is not None]

    exposed_iota = next(
        report for report in reports if "[h]" in report.get("originalSyntax", "")
    )
    exposed_trace = trace(exposed_iota)
    if [
        event.get("reduction", {}).get("kind")
        if event.get("reduction") is not None
        else (event.get("origins") or [{}])[0].get("name")
        for event in exposed_trace[:-1]
    ] != ["syntax", "iota"]:
        raise RuntimeError(f"pre-rewrite iota sequence changed: {exposed_iota!r}")
    exposed_certificate = exposed_iota.get("acceptedCertificate") or ""
    if "↓ h" not in exposed_certificate or "reduce iota" not in exposed_certificate:
        raise RuntimeError(f"pre-rewrite iota certificate was not validated: {exposed_iota!r}")

    observed_reports = {
        (reduction_events(report)[0].get("reduction") or {}).get("kind"): report
        for report in reports
        if report is not exposed_iota and reduction_events(report)
    }
    expected_kinds = {"beta", "zeta", "iota", "projection", "delta"}
    if set(observed_reports) != expected_kinds:
        raise RuntimeError(f"reduction observer kinds changed: {observed_reports!r}")

    expected_sequences = {
        "delta": ["delta"],
        "beta": ["beta"],
        "zeta": ["zeta"],
        "iota": ["iota", "beta", "beta"],
        "projection": ["projection"],
    }
    for kind, report in observed_reports.items():
        events = reduction_events(report)
        sequence = [(event.get("reduction") or {}).get("kind") for event in events]
        if sequence != expected_sequences[kind]:
            raise RuntimeError(f"{kind} reduction ordering changed: {report!r}")
        ticks = [event.get("tick") for event in events]
        if ticks != sorted(ticks) or len(set(ticks)) != len(ticks):
            raise RuntimeError(f"{kind} reduction ticks are not ordered: {report!r}")
        for event in events:
            if event.get("phase") != "pre" or event.get("step") != "visit":
                raise RuntimeError(f"{kind} reduction phase/step changed: {report!r}")
            if event.get("origins") or event.get("premises") or event.get("proof") is not None:
                raise RuntimeError(f"{kind} reduction carried semantic provenance: {report!r}")
        encoding = report.get("encoding") or {}
        if encoding.get("reductionEvents") != len(events):
            raise RuntimeError(f"{kind} reduction metrics changed: {report!r}")
        if encoding.get("deltaReductionEvents") != (1 if kind == "delta" else 0):
            raise RuntimeError(f"{kind} delta metrics changed: {report!r}")

    projection = observed_reports["projection"]
    projection_event = reduction_events(projection)[0].get("reduction")
    if projection_event != {
        "kind": "projection",
        "name": "ReductionInductive",
        "field": 0,
    }:
        raise RuntimeError(f"native projection identity changed: {projection!r}")

    iota = observed_reports["iota"]
    if not iota.get("acceptedCertificate"):
        raise RuntimeError(f"iota recording did not validate its replay certificate: {iota!r}")

    # The eta fixture remains replay-only: pinned reduceStep has no eta branch.
    eta_report = next(
        report
        for report in reports
        if not reduction_events(report) and "reductionDelta" not in report.get("originalSyntax", "")
    )
    if any((event.get("reduction") or {}).get("kind") == "eta" for event in trace(eta_report)):
        raise RuntimeError(f"pinned recorder unexpectedly observed eta: {eta_report!r}")
    eta_encoding = eta_report.get("encoding") or {}
    if eta_encoding.get("reductionEvents") != 0 or eta_encoding.get("deltaReductionEvents") != 0:
        raise RuntimeError(f"eta-only recorder report invented reduction metrics: {eta_report!r}")

    # Each recorder execution must agree with its replay validation envelope.
    for report in reports:
        execution = (report.get("executions") or [None])[0]
        validation = report.get("validation") or {}
        if execution is None or execution.get("initialState") != validation.get("initialState"):
            raise RuntimeError(f"recording validation initial state changed: {report!r}")
        if execution.get("finalState") != validation.get("finalState"):
            raise RuntimeError(f"recording validation final state changed: {report!r}")

    OUTPUT.mkdir(parents=True, exist_ok=True)
    expect_failure(
        "wrong-name",
        source.replace(
            "simp_explicit [reduce delta reductionDelta]",
            "simp_explicit [reduce delta notReductionDelta]",
            1,
        ),
        "Unknown constant `notReductionDelta`",
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
    print("O2b reduction observation, replay, rollback mutations, and pinned eta observation passed")


if __name__ == "__main__":
    main()
