#!/usr/bin/env python3
"""Run a bounded end-to-end check of the Mathlib simp coverage harness."""

from types import SimpleNamespace
import json
import re

import simp_coverage as coverage


def main() -> None:
    smoke = coverage.ROOT / ".lake" / "simp-coverage-smoke"
    coverage.OUTPUT = smoke
    coverage.INVENTORY = smoke / "inventory.json"
    coverage.RESULTS = smoke / "results"
    coverage.AGGREGATE_RESULTS = smoke / "aggregate-results"

    modules = [
        "Mathlib/Data/List/DropRight.lean",
        "Mathlib/RepresentationTheory/Induced.lean",
    ]
    coverage.inventory(
        SimpleNamespace(modules=modules, timeout=600, batch_size=1000)
    )
    document = coverage.load_inventory()
    expected = {
        "simp": 37,
        "simp_all": 1,
        "simp_only": 7,
        "simp_rw": 4,
        "simpa": 4,
    }
    if document["counts"] != expected:
        raise RuntimeError(
            f"unexpected syntax inventory counts: {document['counts']!r} != {expected!r}"
        )
    drop_entries = [
        entry
        for entry in document["entries"]
        if entry["module"] == modules[0]
        and entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    if len(drop_entries) != 24:
        raise RuntimeError(
            f"expected 24 supported DropRight occurrences, got {len(drop_entries)}"
        )
    passive = coverage.passive_module_recording(
        modules[0], drop_entries, timeout=180, keep_copy=True
    )
    expected_ids = {entry["id"] for entry in drop_entries}
    represented_ids = set(passive["represented_occurrence_ids"])
    if not passive["compile"] or passive["compile_count"] != 1:
        raise RuntimeError(f"passive DropRight compile failed: {passive!r}")
    if represented_ids != expected_ids:
        raise RuntimeError(
            "passive DropRight report coverage mismatch: "
            f"missing={sorted(expected_ids - represented_ids)!r}, "
            f"unexpected={sorted(represented_ids - expected_ids)!r}"
        )
    if passive["report_count"] < len(expected_ids):
        raise RuntimeError(f"passive recorder emitted too few reports: {passive!r}")
    if passive.get("schema") != "explicitLean.simpModuleRecording":
        raise RuntimeError(f"unexpected module recording schema: {passive!r}")
    if passive.get("schema_version") != 3:
        raise RuntimeError(f"unexpected module recording schema version: {passive!r}")
    if len(passive.get("occurrences", [])) != len(expected_ids):
        raise RuntimeError(f"passive reports were not grouped per occurrence: {passive!r}")
    for occurrence in passive["occurrences"]:
        executions = occurrence["executions"]
        if occurrence["executionCount"] != len(executions):
            raise RuntimeError(f"incorrect execution count: {occurrence!r}")
        if [execution["executionIndex"] for execution in executions] != list(range(len(executions))):
            raise RuntimeError(f"non-contiguous execution indexes: {occurrence!r}")
        for execution in executions:
            ticks = [
                event["tick"]
                for event in execution.get("trace", [])
            ]
            if any(previous >= current for previous, current in zip(ticks, ticks[1:])):
                raise RuntimeError(
                    "semantic-event ticks must be strictly increasing within an execution: "
                    f"{occurrence!r}"
                )

    multiple_origins = 0
    discharged_premises = 0
    for report in passive["reports"]:
        if report.get("schema") != "explicitLean.simpRecording":
            raise RuntimeError(f"unexpected recording schema: {report!r}")
        if report.get("schemaVersion") != 4:
            raise RuntimeError(f"unexpected recording schema version: {report!r}")
        if report.get("terminalOutcome") is not None:
            raise RuntimeError(
                "passive reports must not infer terminal outcomes: " f"{report!r}"
            )
        for execution in report.get("executions", []):
            for event in execution.get("trace", []):
                if len(event.get("origins", [])) > 1:
                    multiple_origins += 1
                if event.get("premises"):
                    discharged_premises += 1
                for field in ("input", "result", "proof"):
                    fingerprint = event.get(field)
                    if fingerprint is not None and len(fingerprint.get("printable", "")) > 513:
                        raise RuntimeError(f"unbounded diagnostic rendering: {fingerprint!r}")

    if multiple_origins == 0:
        raise RuntimeError("DropRight passive trace did not retain a multiple-origin event")
    if discharged_premises == 0:
        raise RuntimeError("DropRight passive trace did not retain a discharged-premise event")

    raw_markers = re.compile(r"\?m\.[0-9]+|FVarId|Syntax\.mk|Expr\.mvar|mvarId")
    serialized = json.dumps(passive["reports"], sort_keys=True)
    if raw_markers.search(serialized):
        raise RuntimeError("passive report contains a raw Expr/Syntax/metavariable identity")
    package_b_ids = [
        "df0c0dff00516f2a",
        "f582f1aac3e05ab2",
        "22c673bcce0f227e",
        "220c8550c1042081",
    ]
    package_b_entries = [
        next(entry for entry in drop_entries if entry["id"] == identifier)
        for identifier in package_b_ids
    ]
    package_b_results = {}
    for entry in package_b_entries:
        trial = coverage.run_trial(
            entry, coverage.TrialConfig(timeout=180, keep_copies=True)
        )
        package_b_results[entry["id"]] = trial
        if trial.get("status") != "passed" or not trial.get("materialized_compile"):
            raise RuntimeError(f"Package B isolated materialization failed: {trial!r}")
        encoding = trial.get("encoding") or {}
        kinds = set(trial.get("trace_encoding_kinds", []))
        if encoding.get("mode") == "whole_result_proof":
            if (
                trial.get("encoding_fallback_reason") != "presentation_gap"
                or encoding.get("wholeResultProofCount") != 1
                or kinds
            ):
                raise RuntimeError(f"invalid Package B presentation encoding: {trial!r}")
        elif encoding.get("mode") == "event":
            if (
                trial.get("encoding_fallback_reason") is not None
                or encoding.get("wholeResultProofCount", 0) != 0
                or encoding.get("generatedProofEvents", 0) < 1
                or "generated_proof" not in kinds
            ):
                raise RuntimeError(f"invalid Package B event encoding: {trial!r}")
        else:
            raise RuntimeError(f"unknown Package B encoding mode: {trial!r}")
    package_b_aggregate = coverage.aggregate_module(
        modules[0], package_b_entries, package_b_results, timeout=180
    )
    if not package_b_aggregate["compile"]:
        raise RuntimeError(f"Package B aggregate module failed: {package_b_aggregate!r}")

    package_c_ids = [
        "03210e4a7b3567e3",
        "aaf54961bf787d28",
        "739c7ac9dd3cd521",
        "90925e8b6e53287f",
    ]
    package_c_entries = [
        next(entry for entry in drop_entries if entry["id"] == identifier)
        for identifier in package_c_ids
    ]
    package_c_results = {}
    for entry in package_c_entries:
        trial = coverage.run_trial(
            entry, coverage.TrialConfig(timeout=180, keep_copies=True)
        )
        package_c_results[entry["id"]] = trial
        if trial.get("status") != "passed" or not trial.get("materialized_compile"):
            raise RuntimeError(f"Package C isolated materialization failed: {trial!r}")
        encoding = trial.get("encoding") or {}
        # These four old premise-classified occurrences also have an earlier
        # source-level definition unfolding that is not a semantic event. The
        # event encoder deliberately defers that presentation gap to Package
        # F; retain the premise provenance and compile-verify the current
        # whole-result fallback here.
        if (
            encoding.get("mode") != "whole_result_proof"
            or trial.get("encoding_fallback_reason") != "presentation_gap"
            or encoding.get("wholeResultProofCount") != 1
        ):
            raise RuntimeError(f"Package C presentation-gap encoding changed: {trial!r}")
        if trial.get("premise_event_count") != 1:
            raise RuntimeError(f"Package C did not retain one premise-bearing event: {trial!r}")
        if trial.get("premise_event_outer_origin_kinds") != [["decl"]]:
            raise RuntimeError(f"Package C outer premise origin was not one named declaration: {trial!r}")
        outer_names = trial.get("premise_event_outer_origin_names") or []
        if len(outer_names) != 1 or len(outer_names[0]) != 1 or not outer_names[0][0]:
            raise RuntimeError(f"Package C outer premise declaration name was missing: {trial!r}")
        if any(
            count == 0
            for event_counts in trial.get("premise_event_premise_origin_counts", [])
            for count in event_counts
        ):
            raise RuntimeError(f"Package C premise provenance was empty: {trial!r}")
    package_c_aggregate = coverage.aggregate_module(
        modules[0], package_c_entries, package_c_results, timeout=180
    )
    if not package_c_aggregate["compile"]:
        raise RuntimeError(f"Package C aggregate module failed: {package_c_aggregate!r}")

    package_d_ids = [
        "bdfebd4de6e5f543",
        "f578fdc66fc0399a",
        "e72c0cbdffdb90b1",
        "7a1c618c3a39b1cb",
        "3acd3e1c76ad7f24",
        "e0e91bd09649e027",
    ]
    package_d_entries = [
        next(entry for entry in drop_entries if entry["id"] == identifier)
        for identifier in package_d_ids
    ]
    package_d_results = {}
    for entry in package_d_entries:
        trial = coverage.run_trial(
            entry, coverage.TrialConfig(timeout=180, keep_copies=True)
        )
        package_d_results[entry["id"]] = trial
        if trial.get("status") != "passed" or not trial.get("materialized_compile"):
            raise RuntimeError(f"Package D isolated materialization failed: {trial!r}")
        if trial.get("recording_schema") != "explicitLean.simpRecording":
            raise RuntimeError(f"Package D recording schema changed: {trial!r}")
        if trial.get("recording_schema_version") != 4:
            raise RuntimeError(f"Package D recording schema version changed: {trial!r}")
        if trial.get("trace_length", 0) <= 0:
            raise RuntimeError(f"Package D presentation trace was not retained: {trial!r}")
        encoding = trial.get("encoding") or {}
        if (
            encoding.get("mode") != "whole_result_proof"
            or trial.get("encoding_fallback_reason") != "presentation_gap"
            or encoding.get("wholeResultProofCount") != 1
        ):
            raise RuntimeError(f"Package D presentation-gap encoding changed: {trial!r}")
        selector_counts = {
            key: encoding.get(key)
            for key in ("nextSelectorCount", "matchSelectorCount", "tickSelectorCount")
        }
        if any(not isinstance(value, int) or value < 0 for value in selector_counts.values()):
            raise RuntimeError(f"Package D selector metrics were not schema-consistent: {trial!r}")
        if any(value != 0 for value in selector_counts.values()):
            raise RuntimeError(
                "Package D whole-result fallback falsely claims an event selector: "
                f"{trial!r}"
            )
        if trial.get("positions_needed"):
            raise RuntimeError(f"Package D whole-result fallback emitted an absolute tick: {trial!r}")
        if trial.get("trace_selector_kinds") != [None] * trial["trace_length"]:
            raise RuntimeError(f"Package D trace selector kinds were not nullable: {trial!r}")
        if trial.get("trace_selector_values") != [None] * trial["trace_length"]:
            raise RuntimeError(f"Package D trace selector values were not nullable: {trial!r}")
    package_d_aggregate = coverage.aggregate_module(
        modules[0], package_d_entries, package_d_results, timeout=180
    )
    if not package_d_aggregate["compile"]:
        raise RuntimeError(f"Package D aggregate module failed: {package_d_aggregate!r}")

    target = next(
        entry
        for entry in document["entries"]
        if entry["module"] == modules[0]
        and entry["source"] == "simp [rdrop_eq_reverse_drop_reverse]"
    )
    result = coverage.run_trial(
        target, coverage.TrialConfig(timeout=180, keep_copies=True)
    )
    if result["status"] != "passed" or result["trace_length"] != 10:
        raise RuntimeError(f"unexpected isolated trial result: {result!r}")
    aggregate = coverage.aggregate_module(
        modules[0], [target], {target["id"]: result}, timeout=180
    )
    if not aggregate["compile"]:
        raise RuntimeError(f"aggregate smoke module failed: {aggregate!r}")
    coverage.write_summary()
    print("simp coverage smoke test passed")


if __name__ == "__main__":
    main()
