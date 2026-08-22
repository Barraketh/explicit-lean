#!/usr/bin/env python3
"""Check O4 premise terminals, hierarchy, passive custom dischargers, and replay."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
OUTPUT = ROOT / ".lake" / "simp-explicit-fixtures"
TERMINAL_PROBE = ROOT / "Experiment" / "O4TerminalProbe.lean"
TERMINAL_MATERIALIZED = OUTPUT / "O4TerminalMaterialized.lean"
CUSTOM_PROBE = ROOT / "Experiment" / "CustomDischargerProbe.lean"
RECURSIVE_PROBE = ROOT / "Experiment" / "RecursivePremiseProbe.lean"
RECURSIVE_MATERIALIZED = OUTPUT / "RecursivePremiseMaterialized.lean"
NESTED_SELECTOR_PROBE = ROOT / "Experiment" / "NestedPremiseSelectorProbe.lean"
NESTED_SELECTOR_MATERIALIZED = OUTPUT / "NestedPremiseSelectorMaterialized.lean"


def trace_events(report: dict) -> list[dict]:
    return [
        event
        for execution in report.get("executions", [])
        for event in execution.get("trace", [])
    ]


def origin_names(event: dict) -> list[str]:
    return [
        origin.get("name")
        for origin in event.get("origins", [])
        if origin.get("kind") == "decl"
    ]


def all_premises(events: list[dict]):
    for event in events:
        for premise in event.get("premises", []):
            yield premise
            yield from all_premises(premise.get("commands", []))


def check_common(report: dict) -> None:
    if report.get("schema") != "explicitLean.simpRecording":
        raise RuntimeError(f"unexpected O4 report schema: {report!r}")
    if report.get("schemaVersion") != coverage.EXPECTED_SIMP_REPORT_SCHEMA_VERSION:
        raise RuntimeError(f"unexpected O4 report version: {report!r}")
    for execution in report.get("executions", []):
        if execution.get("encoding", {}).get("wholeResultProofCount", 0):
            raise RuntimeError(f"whole-result proof fallback appeared: {report!r}")
    for premise in all_premises(trace_events(report)):
        if "proof" in premise or "premise_term" in str(premise):
            raise RuntimeError(f"premise proof/term leaked into JSON: {premise!r}")


def accepted_report(report: dict) -> None:
    check_common(report)
    if report.get("encodingStatus") != "validated":
        raise RuntimeError(f"O4 terminal report was not validated: {report!r}")
    if report.get("operationallyAdmissible") is not True:
        raise RuntimeError(f"O4 terminal report was not admissible: {report!r}")
    if report.get("acceptedCertificate") is None:
        raise RuntimeError(f"O4 terminal report has no accepted certificate: {report!r}")
    encoding = report.get("encoding") or {}
    if encoding.get("mode") != "event" or encoding.get("generatedProofEvents", 0):
        raise RuntimeError(f"O4 terminal used non-operational event encoding: {report!r}")


def replace_certificate(source: str, needle: str, certificate: str) -> str:
    if source.count(needle) != 1:
        raise RuntimeError(f"expected exactly one source occurrence: {needle!r}")
    return source.replace(needle, certificate.replace("\n", "\n  "), 1)


def compile_materialized(path: Path, source: str) -> None:
    OUTPUT.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    code, output, _ = coverage.run(["lake", "env", "lean", str(path)], timeout=180)
    if code != 0:
        raise RuntimeError(f"materialized O4 certificate failed: {path}\n{output}")


def main() -> None:
    code, output, _ = coverage.run(["lake", "env", "lean", str(TERMINAL_PROBE)], timeout=180)
    if "PANIC" in output or "backtrace" in output.lower():
        raise RuntimeError(f"terminal mutation produced a panic/backtrace:\n{output}")
    reports = coverage.parse_recording_reports(output)
    if code != 0 or len(reports) != 3:
        raise RuntimeError(f"terminal probe failed: exit={code}, reports={len(reports)}\n{output}")
    for report in reports:
        accepted_report(report)

    expected = [
        ("localTerminalRule", "localAssumption"),
        ("equationTerminalRule", "equationHypothesis"),
        ("rflTerminalRule", "dischargeRfl"),
    ]
    for report, (rule_name, terminal_kind) in zip(reports, expected):
        events = trace_events(report)
        outer = [event for event in events if origin_names(event) == [rule_name]]
        if len(outer) != 1 or len(outer[0].get("premises", [])) != 1:
            raise RuntimeError(f"missing exact {rule_name} premise event: {report!r}")
        premise = outer[0]["premises"][0]
        if (premise.get("terminal") or {}).get("kind") != terminal_kind:
            raise RuntimeError(f"{rule_name} terminal mismatch: {premise!r}")
        if premise.get("bindingName") != "h_premise_1":
            raise RuntimeError(f"{rule_name} premise binding was not deterministic: {premise!r}")
        if premise.get("encodingKind") not in {
            "premise_local_assumption",
            "premise_equation_hypothesis",
            "premise_dischargeRfl",
        }:
            raise RuntimeError(f"{rule_name} terminal encoding changed: {premise!r}")

    source = TERMINAL_PROBE.read_text(encoding="utf-8")
    needles = [
        "simp_explicit? only [localTerminalRule, eq_self]",
        "simp_explicit? only [equationTerminalRule, eq_self]",
        "simp_explicit? only [rflTerminalRule, eq_self]",
    ]
    for needle, report in zip(needles, reports):
        source = replace_certificate(source, needle, report["certificate"])
    compile_materialized(TERMINAL_MATERIALIZED, source)

    code, output, _ = coverage.run(["lake", "env", "lean", str(CUSTOM_PROBE)], timeout=180)
    if "PANIC" in output or "backtrace" in output.lower():
        raise RuntimeError(f"custom discharger probe produced a panic/backtrace:\n{output}")
    custom_reports = coverage.parse_recording_reports(output)
    if code != 0 or len(custom_reports) != 1:
        raise RuntimeError(f"custom discharger probe failed: exit={code}, reports={len(custom_reports)}\n{output}")
    custom = custom_reports[0]
    check_common(custom)
    if custom.get("encodingStatus") != "deferred":
        raise RuntimeError(f"custom discharger was not deferred: {custom!r}")
    if custom.get("failureCategory") != "deferred_custom_discharger":
        raise RuntimeError(f"custom discharger category changed: {custom!r}")
    if custom.get("acceptedCertificate") is not None or custom.get("certificate"):
        raise RuntimeError(f"custom discharger exposed a certificate: {custom!r}")
    if custom.get("legacyCertificate") is not None:
        raise RuntimeError(f"custom discharger retained a proof source: {custom!r}")

    code, output, _ = coverage.run(["lake", "env", "lean", str(RECURSIVE_PROBE)], timeout=180)
    if "PANIC" in output or "backtrace" in output.lower():
        raise RuntimeError(f"recursive premise probe produced a panic/backtrace:\n{output}")
    recursive_reports = coverage.parse_recording_reports(output)
    if code != 0 or len(recursive_reports) != 1:
        raise RuntimeError(f"recursive premise probe failed: exit={code}, reports={len(recursive_reports)}\n{output}")
    recursive = recursive_reports[0]
    accepted_report(recursive)
    recursive_encoding = recursive.get("encoding") or {}
    for field, expected_value in {
        "generatedBindingCount": 2,
        "premiseBindingCount": 2,
        "nestedPremiseBindings": 2,
        "namedRuleEvents": 4,
        "nextSelectorCount": 4,
        "matchSelectorCount": 0,
        "tickSelectorCount": 0,
    }.items():
        if recursive_encoding.get(field) != expected_value:
            raise RuntimeError(
                f"recursive metric {field} changed: expected {expected_value}, "
                f"got {recursive_encoding.get(field)!r}: {recursive!r}"
            )
    outer = [event for event in trace_events(recursive) if origin_names(event) == ["recursiveOuter"]]
    if len(outer) != 1 or len(outer[0].get("premises", [])) != 1:
        raise RuntimeError(f"recursive outer hierarchy missing: {recursive!r}")
    if outer[0].get("encodingKind") != "named_rule" or outer[0].get("selectorKind") != "next":
        raise RuntimeError(f"recursive outer encoding metadata changed: {outer[0]!r}")
    p_premise = outer[0]["premises"][0]
    if (p_premise.get("terminal") or {}).get("kind") != "isTrue":
        raise RuntimeError(f"recursive outer premise terminal changed: {p_premise!r}")
    if p_premise.get("encodingKind") != "premise_nested" or p_premise.get("bindingName") != "h_premise_1":
        raise RuntimeError(f"recursive P premise encoding metadata changed: {p_premise!r}")
    p_commands = p_premise.get("commands", [])
    if len(p_commands) != 1 or origin_names(p_commands[0]) != ["recursivePToTrue"]:
        raise RuntimeError(f"recursive child command was not nested: {p_premise!r}")
    if p_commands[0].get("encodingKind") != "named_rule" or p_commands[0].get("selectorKind") != "next":
        raise RuntimeError(f"recursive P command encoding metadata changed: {p_commands[0]!r}")
    q_premises = p_commands[0].get("premises", [])
    if len(q_premises) != 1 or origin_names(q_premises[0]) != ["recursiveQToTrue"]:
        raise RuntimeError(f"recursive Q premise hierarchy changed: {p_commands[0]!r}")
    if q_premises[0].get("encodingKind") != "premise_nested" or q_premises[0].get("bindingName") != "h_premise_1":
        raise RuntimeError(f"recursive Q premise encoding metadata changed: {q_premises[0]!r}")
    q_commands = q_premises[0].get("commands", [])
    if len(q_commands) != 1 or origin_names(q_commands[0]) != ["recursiveQToTrue"]:
        raise RuntimeError(f"recursive Q command was not retained: {q_premises[0]!r}")
    if q_commands[0].get("encodingKind") != "named_rule" or q_commands[0].get("selectorKind") != "next":
        raise RuntimeError(f"recursive Q command encoding metadata changed: {q_commands[0]!r}")
    top_names = [name for event in trace_events(recursive) for name in origin_names(event)]
    if "recursiveQToTrue" in top_names:
        raise RuntimeError(f"recursive Q theorem leaked into top-level trace: {recursive!r}")
    recursive_source = RECURSIVE_PROBE.read_text(encoding="utf-8")
    recursive_needle = "simp_explicit? only [recursiveOuter, recursivePToTrue, recursiveQToTrue, eq_self]"
    recursive_source = replace_certificate(recursive_source, recursive_needle, recursive["certificate"])
    compile_materialized(RECURSIVE_MATERIALIZED, recursive_source)

    code, output, _ = coverage.run(["lake", "env", "lean", str(NESTED_SELECTOR_PROBE)], timeout=180)
    if "PANIC" in output or "backtrace" in output.lower():
        raise RuntimeError(f"nested selector probe produced a panic/backtrace:\n{output}")
    nested_reports = coverage.parse_recording_reports(output)
    if code != 0 or len(nested_reports) != 1:
        raise RuntimeError(f"nested selector probe failed: exit={code}, reports={len(nested_reports)}\n{output}")
    nested = nested_reports[0]
    accepted_report(nested)
    nested_encoding = nested.get("encoding") or {}
    for field, expected_value in {
        "generatedBindingCount": 1,
        "premiseBindingCount": 1,
        "nestedPremiseBindings": 1,
        "namedRuleEvents": 4,
        "nextSelectorCount": 3,
        "matchSelectorCount": 1,
        "tickSelectorCount": 0,
        "nonmaterialInternalEvents": 1,
    }.items():
        if nested_encoding.get(field) != expected_value:
            raise RuntimeError(
                f"nested selector metric {field} changed: expected {expected_value}, "
                f"got {nested_encoding.get(field)!r}: {nested!r}"
            )
    nested_outer = [
        event for event in trace_events(nested) if origin_names(event) == ["selectorOuter"]
    ]
    if len(nested_outer) != 1 or len(nested_outer[0].get("premises", [])) != 1:
        raise RuntimeError(f"nested selector outer hierarchy missing: {nested!r}")
    nested_premise = nested_outer[0]["premises"][0]
    if nested_premise.get("encodingKind") != "premise_nested":
        raise RuntimeError(f"nested selector premise encoding changed: {nested_premise!r}")
    nested_commands = nested_premise.get("commands", [])
    if len(nested_commands) != 3:
        raise RuntimeError(f"nested selector command projection changed: {nested_premise!r}")
    if (
        origin_names(nested_commands[0]) != ["eq_self"]
        or nested_commands[0].get("encodingKind") != "named_rule"
        or nested_commands[0].get("selectorKind") != "next"
    ):
        raise RuntimeError(f"nested selector first command changed: {nested_commands[0]!r}")
    if (
        nested_commands[1].get("encodingKind") != "nonmaterial_internal_execution"
        or nested_commands[1].get("selectorKind") is not None
    ):
        raise RuntimeError(f"nested selector nonmaterial command changed: {nested_commands[1]!r}")
    if (
        origin_names(nested_commands[2]) != ["and_self"]
        or nested_commands[2].get("encodingKind") != "named_rule"
        or nested_commands[2].get("selectorKind") != "match"
        or nested_commands[2].get("selectorValue") != 2
    ):
        raise RuntimeError(f"nested selector match command changed: {nested_commands[2]!r}")
    nested_source = NESTED_SELECTOR_PROBE.read_text(encoding="utf-8")
    nested_needle = "simp_explicit? only [selectorOuter, eq_self, and_self]"
    nested_source = replace_certificate(nested_source, nested_needle, nested["certificate"])
    if "match 2 => and_self" not in nested["certificate"]:
        raise RuntimeError("nested selector certificate omitted the recorded match ordinal")
    compile_materialized(NESTED_SELECTOR_MATERIALIZED, nested_source)
    mutated = nested_source.replace("match 2 => and_self", "match 1 => and_self", 1)
    mutated_path = OUTPUT / "NestedPremiseSelectorMutated.lean"
    mutated_path.write_text(mutated, encoding="utf-8")
    mutation_code, mutation_output, _ = coverage.run(
        ["lake", "env", "lean", str(mutated_path)], timeout=180
    )
    if mutation_code == 0 or "PANIC" in mutation_output or "backtrace" in mutation_output.lower():
        raise RuntimeError(
            "nested selector ordinal mutation was accepted or panicked:\n" + mutation_output
        )

    print("O4 premise terminals and recursive selector metadata passed")


if __name__ == "__main__":
    main()
