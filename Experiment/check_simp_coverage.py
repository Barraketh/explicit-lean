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
    if passive.get("schema_version") != 1:
        raise RuntimeError(f"unexpected module recording schema version: {passive!r}")
    if len(passive.get("occurrences", [])) != len(expected_ids):
        raise RuntimeError(f"passive reports were not grouped per occurrence: {passive!r}")
    for occurrence in passive["occurrences"]:
        executions = occurrence["executions"]
        if occurrence["executionCount"] != len(executions):
            raise RuntimeError(f"incorrect execution count: {occurrence!r}")
        if [execution["executionIndex"] for execution in executions] != list(range(len(executions))):
            raise RuntimeError(f"non-contiguous execution indexes: {occurrence!r}")

    multiple_origins = 0
    discharged_premises = 0
    for report in passive["reports"]:
        if report.get("schema") != "explicitLean.simpRecording":
            raise RuntimeError(f"unexpected recording schema: {report!r}")
        if report.get("schemaVersion") != 1:
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
