#!/usr/bin/env python3
"""Run a bounded end-to-end check of the Mathlib simp coverage harness."""

from types import SimpleNamespace
import json
import re

import simp_coverage as coverage


def assert_rejected_fallback(trial: dict, *, deferred: bool = False) -> None:
    expected_status = "deferred" if deferred else "rejected"
    if trial.get("status") != expected_status or trial.get("materialized_compile"):
        raise RuntimeError(f"inadmissible fallback was materialized: {trial!r}")
    if trial.get("accepted_certificate") is not None:
        raise RuntimeError(f"inadmissible fallback retained an accepted certificate: {trial!r}")
    if trial.get("operationally_admissible") is not False:
        raise RuntimeError(f"inadmissible fallback has an admissible status: {trial!r}")
    if not trial.get("legacy_certificate"):
        raise RuntimeError(f"fallback migration source was not retained for audit: {trial!r}")
    if not isinstance(trial.get("operational_admissibility"), dict):
        raise RuntimeError(f"fallback omitted structured admissibility: {trial!r}")


def assert_aggregate_rejected(
    module: str,
    entries: list[dict],
    results: dict[str, dict],
) -> None:
    try:
        coverage.aggregate_module(module, entries, results, timeout=180)
    except RuntimeError:
        return
    raise RuntimeError(
        "aggregate unexpectedly accepted an inadmissible fallback certificate: "
        f"entries={[entry['id'] for entry in entries]!r}"
    )


def main() -> None:
    smoke = coverage.ROOT / ".lake" / "simp-coverage-smoke"
    coverage.OUTPUT = smoke
    coverage.INVENTORY = smoke / "inventory.json"
    coverage.RESULTS = smoke / "results"
    coverage.AGGREGATE_RESULTS = smoke / "aggregate-results"

    copied_mathlib = smoke / "module-recording" / "Mathlib" / "Example.lean"
    copied_command = coverage.lean_command(copied_mathlib)
    expected_root = str(smoke / "module-recording")
    if "-R" not in copied_command or copied_command[copied_command.index("-R") + 1] != expected_root:
        raise RuntimeError(f"copied Mathlib module lost its module root: {copied_command!r}")

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
    if passive.get("schema_version") != coverage.PASSIVE_RECORDING_SCHEMA_VERSION:
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
        if report.get("schemaVersion") != 10:
            raise RuntimeError(f"unexpected recording schema version: {report!r}")
        if not isinstance(report.get("bodyScopeId"), str) or not report["bodyScopeId"]:
            raise RuntimeError(f"passive report is missing body-scope ownership: {report!r}")
        if report.get("terminalOutcome") is not None:
            raise RuntimeError(
                "passive reports must not infer terminal outcomes: " f"{report!r}"
            )
        for execution in report.get("executions", []):
            if not execution.get("attemptToken"):
                raise RuntimeError(f"passive execution is missing an attempt token: {report!r}")
            if execution.get("disposition") not in {"committed", "backtracked"}:
                raise RuntimeError(f"passive execution has no scoped disposition: {report!r}")
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
        assert_rejected_fallback(trial)
        if trial.get("local_renames") != []:
            raise RuntimeError(f"Package B ordinary encoding renamed locals: {trial!r}")
        encoding = trial.get("encoding") or {}
        if encoding.get("mode") not in {"event", "presentation_change", "whole_result_proof"}:
            raise RuntimeError(f"unknown Package B encoding mode: {trial!r}")
        trace_length = trial.get("trace_length")
        if (
            not isinstance(trace_length, int)
            or trace_length < 0
            or len(trial.get("trace_selector_kinds") or []) != trace_length
        ):
            raise RuntimeError(f"Package B trace audit was malformed: {trial!r}")
    assert_aggregate_rejected(modules[0], package_b_entries, package_b_results)

    # A zero-event, non-closing simplification can still change the target's
    # presentation through proofless unfolding.  The replacement must retain
    # that presentation for the following `rw`, rather than validating an
    # inert `simp_explicit []` only up to definitional equality.
    zero_event_id = "7fc5f61da8b87de6"
    zero_event_entry = next(
        entry for entry in drop_entries if entry["id"] == zero_event_id
    )
    zero_event_trial = coverage.run_trial(
        zero_event_entry, coverage.TrialConfig(timeout=180, keep_copies=True)
    )
    zero_event_encoding = zero_event_trial.get("encoding") or {}
    assert_rejected_fallback(zero_event_trial)
    if (
        zero_event_encoding.get("mode") != "presentation_change"
        or zero_event_encoding.get("presentationChangeCount") != 1
        or zero_event_encoding.get("namedRuleEvents") != 0
        or zero_event_trial.get("encoding_fallback_reason") != "presentation_gap"
    ):
        raise RuntimeError(f"zero-event presentation audit changed: {zero_event_trial!r}")

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
        admissibility = trial.get("operational_admissibility") or {}
        if admissibility.get("code") != "accepted":
            assert_rejected_fallback(trial)
            continue
        if trial.get("status") != "passed" or not trial.get("materialized_compile"):
            raise RuntimeError(f"accepted Package C nested premise failed materialization: {trial!r}")
        if trial.get("local_renames") != []:
            raise RuntimeError(f"Package C ordinary encoding renamed locals: {trial!r}")
        encoding = trial.get("encoding") or {}
        # The premise-bearing cases may now use either a compact event
        # certificate or the bounded presentation-change prepass.  A
        # whole-result presentation-gap fallback is no longer accepted for
        # this Package F gate.
        mode = encoding.get("mode")
        if mode == "event":
            if (
                trial.get("encoding_fallback_reason") is not None
                or encoding.get("wholeResultProofCount", 0) != 0
            ):
                raise RuntimeError(f"Package C event encoding changed: {trial!r}")
        elif mode == "presentation_change":
            if (
                trial.get("encoding_fallback_reason") != "presentation_gap"
                or encoding.get("presentationChangeCount") != 1
                or encoding.get("wholeResultProofCount", 0) != 0
            ):
                raise RuntimeError(f"Package C presentation encoding changed: {trial!r}")
        else:
            raise RuntimeError(f"accepted Package C emitted an unknown encoding mode: {trial!r}")
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
    assert_aggregate_rejected(modules[0], package_c_entries, package_c_results)

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
        assert_rejected_fallback(trial)
        if trial.get("local_renames") != []:
            raise RuntimeError(f"Package D ordinary encoding renamed locals: {trial!r}")
        if trial.get("recording_schema") != "explicitLean.simpRecording":
            raise RuntimeError(f"Package D recording schema changed: {trial!r}")
        if trial.get("recording_schema_version") != 10:
            raise RuntimeError(f"Package D recording schema version changed: {trial!r}")
        if trial.get("trace_length", 0) <= 0:
            raise RuntimeError(f"Package D presentation trace was not retained: {trial!r}")
        encoding = trial.get("encoding") or {}
        if (
            encoding.get("mode") != "presentation_change"
            or trial.get("encoding_fallback_reason") != "presentation_gap"
            or encoding.get("presentationChangeCount") != 1
            or encoding.get("wholeResultProofCount", 0) != 0
        ):
            raise RuntimeError(f"Package D presentation-change encoding changed: {trial!r}")
        selector_counts = {
            key: encoding.get(key)
            for key in ("nextSelectorCount", "matchSelectorCount", "tickSelectorCount")
        }
        if any(not isinstance(value, int) or value < 0 for value in selector_counts.values()):
            raise RuntimeError(f"Package D selector metrics were not schema-consistent: {trial!r}")
        selector_kinds = trial.get("trace_selector_kinds") or []
        observed_selector_counts = {
            "nextSelectorCount": selector_kinds.count("next"),
            "matchSelectorCount": selector_kinds.count("match"),
            "tickSelectorCount": selector_kinds.count("tick"),
        }
        if selector_counts != observed_selector_counts:
            raise RuntimeError(
                f"Package D selector metrics disagree with the trace: {trial!r}"
            )
        if selector_counts["tickSelectorCount"] != 0:
            raise RuntimeError(f"Package D presentation replay emitted a tick: {trial!r}")
        if trial.get("positions_needed"):
            raise RuntimeError(f"Package D presentation replay emitted an absolute tick: {trial!r}")
        if len(selector_kinds) != trial["trace_length"]:
            raise RuntimeError(f"Package D trace selector kinds changed length: {trial!r}")
        selector_values = trial.get("trace_selector_values") or []
        if len(selector_values) != trial["trace_length"]:
            raise RuntimeError(f"Package D trace selector values changed length: {trial!r}")
        if any(value is not None for value in selector_values):
            raise RuntimeError(f"Package D next selectors unexpectedly carry values: {trial!r}")
    assert_aggregate_rejected(modules[0], package_d_entries, package_d_results)

    presentation_ids = package_c_ids + package_d_ids
    presentation_results = {**package_c_results, **package_d_results}
    assert_aggregate_rejected(
        modules[0], [*package_c_entries, *package_d_entries], presentation_results
    )
    for identifier in presentation_ids:
        trial = presentation_results[identifier]
        mode = (trial.get("encoding") or {}).get("mode")
        if mode == "whole_result_proof":
            raise RuntimeError(f"Package F3 retained whole-result fallback: {trial!r}")
        if mode == "presentation_change":
            if (trial.get("encoding") or {}).get("presentationChangeCount") != 1:
                raise RuntimeError(f"Package F3 change metric missing: {trial!r}")
        elif mode != "event":
            raise RuntimeError(f"Package F3 emitted unknown compact mode: {trial!r}")

    package_e_ids = [
        "f3d6dce9ae772ce2",
        "54d6b0e3b2ad8e41",
    ]
    package_e_entries = [
        next(entry for entry in drop_entries if entry["id"] == identifier)
        for identifier in package_e_ids
    ]
    package_e_results = {}
    for entry in package_e_entries:
        trial = coverage.run_trial(
            entry, coverage.TrialConfig(timeout=180, keep_copies=True)
        )
        package_e_results[entry["id"]] = trial
        assert_rejected_fallback(trial, deferred=True)
        encoding = trial.get("encoding") or {}
        if encoding.get("generatedSimprocEvents", 0) < 1:
            raise RuntimeError(f"Package E did not retain simproc audit metrics: {trial!r}")
    assert_aggregate_rejected(modules[0], package_e_entries, package_e_results)

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
    if (result.get("operational_admissibility") or {}).get("code") != "accepted":
        raise RuntimeError(f"direct named-rule certificate was not accepted: {result!r}")
    if not result.get("accepted_certificate") or result.get("legacy_certificate"):
        raise RuntimeError(f"direct named-rule certificate fields changed: {result!r}")
    target_encoding = result.get("encoding") or {}
    if (
        target_encoding.get("mode") != "event"
        or target_encoding.get("generatedProofEvents", 0) != 0
        or target_encoding.get("namedRuleEvents", 0) == 0
    ):
        raise RuntimeError(f"direct named-rule encoding changed: {result!r}")
    aggregate = coverage.aggregate_module(
        modules[0], [target], {target["id"]: result}, timeout=180
    )
    if not aggregate["compile"]:
        raise RuntimeError(f"aggregate smoke module failed: {aggregate!r}")
    coverage.write_summary()
    print("simp coverage smoke test passed")


if __name__ == "__main__":
    main()
