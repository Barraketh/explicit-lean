#!/usr/bin/env python3
"""Focused F2 structural owner materialization and terminal-outcome checks."""

from __future__ import annotations

from pathlib import Path
import re
from types import SimpleNamespace

import simp_coverage as coverage


ROOT = coverage.ROOT
FIXTURE = ROOT / "Experiment" / "BodyMaterializationProbe.lean"
FIXTURE_MODULE = "Experiment/BodyMaterializationProbe.lean"
DROP_MODULE = "Mathlib/Data/List/DropRight.lean"
DROP_IDS = {
    "754e9f44f095fc5d",
    "c485b5d0b1a08fac",
    "c9eca03fcd0280ed",
}


def compile_copy(path: Path, timeout: int = 180) -> tuple[bool, str]:
    code, output, _ = coverage.run(coverage.lean_command(path), timeout=timeout)
    return code == 0, output


def write_materialized(path: Path, source: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(coverage.inject_import(source))


def fixture_entries() -> list[dict]:
    entries = coverage.syntax_inventory_file(FIXTURE, FIXTURE_MODULE, 180)
    entries = [entry for entry in entries if entry["kind"] in coverage.SUPPORTED_KINDS]
    if len(entries) != 7:
        raise RuntimeError(f"expected seven syntax-inventoried fixture occurrences: {entries!r}")
    return entries


def check_owner_ranges(source: bytes, entries: list[dict]) -> None:
    for entry in entries:
        for start_field, end_field, source_field in (
            ("ownerStartByte", "ownerEndByte", "ownerSource"),
            ("ownerChildStartByte", "ownerChildEndByte", "ownerChildSource"),
        ):
            start = entry.get(start_field)
            end = entry.get(end_field)
            expected = entry.get(source_field)
            if not isinstance(start, int) or not isinstance(end, int) or not isinstance(expected, str):
                raise RuntimeError(f"owner metadata is incomplete: {entry!r}")
            if source[start:end].decode("utf-8") != expected:
                raise RuntimeError(f"owner metadata range is stale: {entry!r}")
        if not (
            entry["ownerStartByte"] <= entry["startByte"] < entry["ownerEndByte"]
            and entry["ownerChildStartByte"] <= entry["startByte"] < entry["ownerChildEndByte"]
        ):
            raise RuntimeError(f"owner metadata does not contain occurrence: {entry!r}")
        if entry.get("ownerKind") == "and_then":
            start = entry.get("ownerLeftStartByte")
            end = entry.get("ownerLeftEndByte")
            expected = entry.get("ownerLeftSource")
            if not isinstance(start, int) or not isinstance(end, int) or not isinstance(expected, str):
                raise RuntimeError(f"andThen left metadata is incomplete: {entry!r}")
            if source[start:end].decode("utf-8") != expected:
                raise RuntimeError(f"andThen left metadata range is stale: {entry!r}")


def report_by_id(record: dict) -> dict[str, dict]:
    result: dict[str, dict] = {}
    for report in record.get("reports", []):
        identifier = report.get("occurrenceId")
        if isinstance(identifier, str):
            result[identifier] = report
    return result


def check_terminal_helpers() -> None:
    if coverage.classify_terminal_outcome(None) != "not_reached":
        raise RuntimeError("not_reached classification regressed")
    backtracked = {
        "executions": [{"result": "succeeded", "disposition": "backtracked"}]
    }
    if coverage.classify_terminal_outcome(backtracked) != "attempted_backtracked":
        raise RuntimeError("attempted_backtracked classification regressed")
    failed = {"executions": [{"result": "failed", "disposition": "backtracked"}]}
    if coverage.classify_terminal_outcome(failed) != "original_failure":
        raise RuntimeError("original_failure classification regressed")
    committed = {
        "executions": [{"result": "succeeded", "disposition": "committed"}]
    }
    if coverage.classify_terminal_outcome(committed, materialized_compile=True) != "materialized":
        raise RuntimeError("materialized classification regressed")
    if coverage.classify_terminal_outcome(committed, materialized_compile=False) != "coverage_failure":
        raise RuntimeError("coverage_failure classification regressed")


def check_fixture() -> None:
    entries = fixture_entries()
    coverage.OUTPUT = ROOT / ".lake" / "f2-fixture"
    coverage.RESULTS = coverage.OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = coverage.OUTPUT / "aggregate-results"
    record = coverage.passive_module_recording(
        FIXTURE_MODULE,
        entries,
        timeout=180,
        keep_copy=True,
        source_path=FIXTURE,
    )
    if not record["compile"] or record["compile_count"] != 1:
        raise RuntimeError(f"F2 fixture passive compile failed: {record!r}")
    reports = report_by_id(record)
    if len(reports) != 6:
        raise RuntimeError(f"expected six reached fixture occurrences: {reports!r}")
    ordered = sorted(entries, key=lambda entry: entry["startByte"])
    check_owner_ranges(FIXTURE.read_bytes(), ordered)
    shared, all_goals, repeated, dead, abandoned, fallback, nested = ordered
    if shared["ownerKind"] != "and_then" or shared["ownerRole"] != "and_then_right":
        raise RuntimeError(f"shared fixture owner shape changed: {shared!r}")
    if all_goals["ownerKind"] != "all_goals" or all_goals["ownerRole"] != "all_goals_child":
        raise RuntimeError(f"all_goals fixture owner shape changed: {all_goals!r}")
    if repeated["ownerKind"] != "and_then" or repeated["ownerRole"] != "and_then_right":
        raise RuntimeError(f"repeat-under-andThen owner selection changed: {repeated!r}")
    if dead["ownerKind"] != "first" or dead["ownerRole"] != "first_branch":
        raise RuntimeError(f"dead branch owner shape changed: {dead!r}")
    if abandoned["ownerKind"] != "first" or fallback["ownerKind"] != "first":
        raise RuntimeError("backtracking fixture lost first owner metadata")
    if nested["ownerKind"] != "and_then" or nested["ownerRole"] != "and_then_right":
        raise RuntimeError(f"nested-semicolon owner shape changed: {nested!r}")

    if coverage.classify_terminal_outcome(reports.get(dead["id"])) != "not_reached":
        raise RuntimeError("dead branch was not classified as not_reached")
    abandoned_report = reports.get(abandoned["id"])
    if abandoned_report is None:
        raise RuntimeError("abandoned branch report was not retained")
    if coverage.classify_terminal_outcome(abandoned_report) != "attempted_backtracked":
        raise RuntimeError(f"abandoned branch outcome changed: {abandoned_report!r}")
    if [
        execution.get("disposition")
        for execution in abandoned_report.get("executions", [])
    ] != ["backtracked"]:
        raise RuntimeError(f"abandoned branch had unexpected dispositions: {abandoned_report!r}")
    fallback_report = reports.get(fallback["id"])
    if fallback_report is None or [
        execution.get("disposition")
        for execution in fallback_report.get("executions", [])
    ] != ["committed"]:
        raise RuntimeError(f"fallback branch was not committed: {fallback_report!r}")

    fixture_source = FIXTURE.read_bytes()
    materialized: list[tuple[dict, dict, str]] = []
    for label, entry in (
        ("shared", shared),
        ("all-goals", all_goals),
        ("repeat-rhs", repeated),
        ("nested-semicolon", nested),
    ):
        report = reports[entry["id"]]
        if len(coverage.committed_certificates(report)) != 2:
            raise RuntimeError(f"{label} did not retain two committed closing executions")
        replacement = coverage.owner_replacement(
            fixture_source, entry, report, sibling_entries=entries
        )
        if re.search(r"(?<![A-Za-z0-9_])simp(?!_)", replacement):
            raise RuntimeError(f"{label} owner retained ambient simp: {replacement!r}")
        if replacement.count("·") != 2:
            raise RuntimeError(f"{label} owner bullet count changed: {replacement!r}")
        if entry.get("ownerKind") == "and_then" and not replacement.startswith("focus\n"):
            raise RuntimeError(f"{label} owner was not focus-scoped: {replacement!r}")
        output_path = coverage.OUTPUT / "materialized" / f"{label}.lean"
        materialized_source = coverage.materialize_owner_source(
            fixture_source, entry, report, sibling_entries=entries
        )
        write_materialized(output_path, materialized_source)
        compiled, output = compile_copy(output_path)
        if not compiled:
            raise RuntimeError(f"{label} owner materialization failed:\n{output}")
        materialized.append((entry, report, replacement))

    aggregate = fixture_source
    for entry, report, _ in sorted(materialized, key=lambda item: item[0]["ownerStartByte"], reverse=True):
        aggregate = coverage.materialize_owner_source(
            aggregate, entry, report, sibling_entries=entries
        )
    aggregate_path = coverage.OUTPUT / "materialized" / "aggregate.lean"
    write_materialized(aggregate_path, aggregate)
    compiled, output = compile_copy(aggregate_path)
    if not compiled:
        raise RuntimeError(f"F2 fixture aggregate materialization failed:\n{output}")


def check_drop_right() -> None:
    coverage.OUTPUT = ROOT / ".lake" / "f2-drop-right"
    coverage.INVENTORY = coverage.OUTPUT / "inventory.json"
    coverage.RESULTS = coverage.OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = coverage.OUTPUT / "aggregate-results"
    coverage.inventory(SimpleNamespace(modules=[DROP_MODULE], timeout=600, batch_size=1000))
    document = coverage.load_inventory()
    entries = [
        entry
        for entry in document["entries"]
        if entry["module"] == DROP_MODULE and entry["id"] in DROP_IDS
    ]
    if {entry["id"] for entry in entries} != DROP_IDS:
        raise RuntimeError(f"F2 DropRight IDs missing from inventory: {entries!r}")
    source = (coverage.MATHLIB / DROP_MODULE).read_bytes()
    check_owner_ranges(source, entries)
    results: dict[str, dict] = {}
    for entry in sorted(entries, key=lambda item: item["startByte"]):
        if entry.get("ownerKind") != "and_then" or entry.get("ownerRole") != "and_then_right":
            raise RuntimeError(f"DropRight owner shape is not distributed andThen: {entry!r}")
        record = coverage.passive_module_recording(
            DROP_MODULE,
            [entry],
            timeout=180,
            keep_copy=True,
        )
        reports = report_by_id(record)
        report = reports.get(entry["id"])
        if report is None:
            raise RuntimeError(f"DropRight report missing for {entry['id']}: {record!r}")
        executions = report.get("executions", [])
        if [execution.get("disposition") for execution in executions] != ["committed", "committed"]:
            raise RuntimeError(f"DropRight dispositions changed: {report!r}")
        if len(coverage.committed_certificates(report)) != 2:
            raise RuntimeError(f"DropRight did not retain two closing certificates: {report!r}")
        if report.get("certificate") != "" or report.get("certificateBytes") != 0:
            raise RuntimeError(f"DropRight fabricated an aggregate certificate: {report!r}")
        if report.get("encodingStatus") != "body_rewrite_required":
            raise RuntimeError(f"DropRight aggregate status changed: {report!r}")
        top_mode = report.get("encoding", {}).get("mode")
        if entry["id"] != "c9eca03fcd0280ed":
            if top_mode != "event" or any(
                execution.get("encoding", {}).get("mode") != "event"
                for execution in executions
            ):
                raise RuntimeError(f"DropRight event encoding changed: {report!r}")
        if entry["id"] == "c9eca03fcd0280ed":
            if any(
                execution.get("encoding", {}).get("mode") != "whole_result_proof"
                or execution.get("encodingFallbackReason") != "presentation_gap"
                for execution in executions
            ):
                raise RuntimeError(f"DropRight c9 per-branch fallback changed: {report!r}")
        replacement = coverage.owner_replacement(source, entry, report, sibling_entries=[entry])
        materialized = coverage.materialize_owner_source(
            source, entry, report, sibling_entries=[entry]
        )
        output_path = coverage.OUTPUT / "materialized" / f"{entry['id']}.lean"
        write_materialized(output_path, materialized)
        compiled, output = compile_copy(output_path)
        if not compiled:
            raise RuntimeError(f"DropRight isolated materialization failed for {entry['id']}:\n{output}")
        if coverage.classify_terminal_outcome(report, materialized_compile=True) != "materialized":
            raise RuntimeError(f"DropRight terminal outcome was not materialized: {report!r}")
        results[entry["id"]] = report
        if replacement.count("·") != 2:
            raise RuntimeError(f"DropRight explicit bullet count changed: {replacement!r}")

    aggregate = source
    for entry in sorted(entries, key=lambda item: item["ownerStartByte"], reverse=True):
        aggregate = coverage.materialize_owner_source(
            aggregate, entry, results[entry["id"]], sibling_entries=[entry]
        )
    aggregate_path = coverage.OUTPUT / "materialized" / "aggregate.lean"
    write_materialized(aggregate_path, aggregate)
    compiled, output = compile_copy(aggregate_path)
    if not compiled:
        raise RuntimeError(f"DropRight F2 aggregate failed:\n{output}")


def main() -> None:
    check_terminal_helpers()
    check_fixture()
    check_drop_right()
    print("F2 structural owner materialization and terminal outcome checks passed")


if __name__ == "__main__":
    main()
