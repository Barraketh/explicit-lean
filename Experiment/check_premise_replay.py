#!/usr/bin/env python3
"""Check Package C premise provenance, encoding, and closed materialization."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
PROBE = ROOT / "Experiment" / "PremiseReplayProbe.lean"
OUTPUT = ROOT / ".lake" / "simp-explicit-fixtures"
MATERIALIZED = OUTPUT / "PremiseReplayMaterialized.lean"
GUARDED_PROBE = ROOT / "Experiment" / "GuardedPremiseProbe.lean"
GUARDED_MATERIALIZED = OUTPUT / "GuardedPremiseMaterialized.lean"
TERM_PROBE = ROOT / "Experiment" / "TermPremiseProbe.lean"
TERM_MATERIALIZED = OUTPUT / "TermPremiseMaterialized.lean"


def main() -> None:
    code, output, _ = coverage.run(
        ["lake", "env", "lean", str(PROBE)], timeout=180
    )
    reports = coverage.parse_recording_reports(output)
    if code != 0 or len(reports) != 1:
        raise RuntimeError(
            f"premise probe failed or emitted an unexpected report count: "
            f"exit={code}, reports={len(reports)}\n{output}"
        )
    report = reports[0]
    if report.get("schema") != "explicitLean.simpRecording":
        raise RuntimeError(f"unexpected premise report schema: {report!r}")
    if report.get("schemaVersion") != 6:
        raise RuntimeError(f"unexpected premise report version: {report!r}")
    if report.get("localRenames") != []:
        raise RuntimeError(f"ordinary premise encoding unexpectedly renamed locals: {report!r}")
    encoding = report.get("encoding") or {}
    if encoding.get("mode") != "event":
        raise RuntimeError(f"premise recording unexpectedly used whole-result mode: {report!r}")
    if encoding.get("nestedPremiseBindings") != 1:
        raise RuntimeError(f"premise nested-binding count was not one: {report!r}")
    events = [
        event
        for execution in report.get("executions", [])
        for event in execution.get("trace", [])
    ]
    premise_events = [event for event in events if event.get("premises")]
    if len(premise_events) != 1:
        raise RuntimeError(f"expected one premise-bearing event: {report!r}")
    event = premise_events[0]
    origins = event.get("origins") or []
    if [origin.get("name") for origin in origins] != ["Nat.sub_eq_zero_of_le"]:
        raise RuntimeError(f"outer premise origins were not separated: {report!r}")
    premise = event["premises"][0]
    premise_origins = premise.get("origins") or []
    if [origin.get("name") for origin in premise_origins] != ["Nat.zero_le"]:
        raise RuntimeError(f"premise origins were not retained: {report!r}")
    if event.get("encodingKind") != "named_rule":
        raise RuntimeError(f"premise event lost named-rule encoding: {report!r}")
    if premise.get("encodingKind") != "premise_nested":
        raise RuntimeError(f"premise did not use nested encoding: {report!r}")
    if premise.get("bindingName") != "h_premise_1":
        raise RuntimeError(f"premise binding name was not deterministic: {report!r}")
    certificate = report.get("certificate")
    if not isinstance(certificate, str) or " using [h_premise_1]" not in certificate:
        raise RuntimeError(f"premise certificate did not use the explicit provider: {report!r}")

    source = PROBE.read_text(encoding="utf-8")
    needle = "simp_explicit?"
    if source.count(needle) != 1:
        raise RuntimeError("premise probe tactic occurrence was not unique")
    materialized = source.replace(needle, certificate.replace("\n", "\n  "), 1)
    OUTPUT.mkdir(parents=True, exist_ok=True)
    MATERIALIZED.write_text(materialized, encoding="utf-8")
    replay_code, replay_output, _ = coverage.run(
        ["lake", "env", "lean", str(MATERIALIZED)], timeout=180
    )
    if replay_code != 0:
        raise RuntimeError(
            "materialized premise certificate failed closed replay compilation:\n"
            + replay_output
        )

    guarded_code, guarded_output, _ = coverage.run(
        ["lake", "env", "lean", str(GUARDED_PROBE)], timeout=180
    )
    guarded_reports = coverage.parse_recording_reports(guarded_output)
    if guarded_code != 0 or len(guarded_reports) != 1:
        raise RuntimeError(
            f"guarded premise probe failed: exit={guarded_code}, "
            f"reports={len(guarded_reports)}\n{guarded_output}"
        )
    guarded_report = guarded_reports[0]
    if guarded_report.get("localRenames") != []:
        raise RuntimeError(f"guarded premise encoding unexpectedly renamed locals: {guarded_report!r}")
    guarded_events = [
        event
        for execution in guarded_report.get("executions", [])
        for event in execution.get("trace", [])
        if event.get("premises")
    ]
    if len(guarded_events) != 1:
        raise RuntimeError(f"guarded theorem did not record one premise event: {guarded_report!r}")
    guarded_event = guarded_events[0]
    if [origin.get("name") for origin in guarded_event.get("origins", [])] != ["guardedSub"]:
        raise RuntimeError(f"guarded theorem was not the recorded outer rule: {guarded_report!r}")
    guarded_certificate = guarded_report.get("certificate")
    if not isinstance(guarded_certificate, str) or "guardedSub using [h_premise_1]" not in guarded_certificate:
        raise RuntimeError(f"guarded theorem certificate did not use the closed premise: {guarded_report!r}")
    guarded_source = GUARDED_PROBE.read_text(encoding="utf-8")
    guarded_needle = "simp_explicit? only [guardedSub, Nat.zero_le]"
    if guarded_source.count(guarded_needle) != 1:
        raise RuntimeError("guarded premise probe tactic occurrence was not unique")
    guarded_materialized = guarded_source.replace(
        guarded_needle, guarded_certificate.replace("\n", "\n  "), 1
    )
    GUARDED_MATERIALIZED.write_text(guarded_materialized, encoding="utf-8")
    guarded_replay_code, guarded_replay_output, _ = coverage.run(
        ["lake", "env", "lean", str(GUARDED_MATERIALIZED)], timeout=180
    )
    if guarded_replay_code != 0:
        raise RuntimeError(
            "materialized guarded premise certificate failed closed replay compilation:\n"
            + guarded_replay_output
        )

    term_code, term_output, _ = coverage.run(
        ["lake", "env", "lean", str(TERM_PROBE)], timeout=180
    )
    term_reports = coverage.parse_recording_reports(term_output)
    if term_code != 0 or len(term_reports) != 1:
        raise RuntimeError(
            f"term-premise probe failed: exit={term_code}, "
            f"reports={len(term_reports)}\n{term_output}"
        )
    term_report = term_reports[0]
    if term_report.get("localRenames") != []:
        raise RuntimeError(f"term premise encoding unexpectedly renamed locals: {term_report!r}")
    term_encoding = term_report.get("encoding") or {}
    if (
        term_encoding.get("mode") != "event"
        or term_encoding.get("premiseBindingCount") != 1
        or term_encoding.get("termPremiseBindings") != 1
        or term_encoding.get("nestedPremiseBindings") != 0
    ):
        raise RuntimeError(f"term-premise binding metrics were not selected: {term_report!r}")
    term_events = [
        event
        for execution in term_report.get("executions", [])
        for event in execution.get("trace", [])
        if event.get("premises")
    ]
    if len(term_events) != 1:
        raise RuntimeError(f"term-premise probe did not record one premise event: {term_report!r}")
    term_event = term_events[0]
    if [origin.get("name") for origin in term_event.get("origins", [])] != ["guardedEqConj"]:
        raise RuntimeError(f"term-premise outer origin was not guardedEqConj: {term_report!r}")
    term_premise = term_event["premises"][0]
    term_origin_names = {origin.get("name") for origin in term_premise.get("origins", [])}
    if not {"eq_self", "and_self"}.issubset(term_origin_names):
        raise RuntimeError(f"term-premise provenance did not retain eq_self/and_self: {term_report!r}")
    if term_premise.get("encodingKind") != "premise_term":
        raise RuntimeError(f"term-premise binding did not use ProofExport: {term_report!r}")
    if term_premise.get("bindingName") != "h_premise_1":
        raise RuntimeError(f"term-premise binding name was not deterministic: {term_report!r}")
    term_certificate = term_report.get("certificate")
    if not isinstance(term_certificate, str) or "guardedEqConj using [h_premise_1]" not in term_certificate:
        raise RuntimeError(f"term-premise certificate omitted explicit premise syntax: {term_report!r}")
    term_source = TERM_PROBE.read_text(encoding="utf-8")
    term_needle = "simp_explicit? only [guardedEqConj, eq_self, and_self]"
    if term_source.count(term_needle) != 1:
        raise RuntimeError("term-premise probe tactic occurrence was not unique")
    term_materialized = term_source.replace(
        term_needle, term_certificate.replace("\n", "\n  "), 1
    )
    TERM_MATERIALIZED.write_text(term_materialized, encoding="utf-8")
    term_replay_code, term_replay_output, _ = coverage.run(
        ["lake", "env", "lean", str(TERM_MATERIALIZED)], timeout=180
    )
    if term_replay_code != 0:
        raise RuntimeError(
            "materialized term-premise certificate failed closed replay compilation:\n"
            + term_replay_output
        )
    print("premise provenance, guarded nested/term encodings, mutations, and closed replay passed")


if __name__ == "__main__":
    main()
