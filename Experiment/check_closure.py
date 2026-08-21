#!/usr/bin/env python3
"""Focused G1 checks for the resumable module closure path."""

from __future__ import annotations

import json
from pathlib import Path

import simp_coverage as coverage


ROOT = coverage.ROOT
FIXTURE = ROOT / "Experiment" / "ClosureProbe.lean"
MODULE = "Experiment/ClosureProbe.lean"
FORBIDDEN = ("FVarId", "Syntax.mk", "Expr.mvar", "mvarId")


def main() -> None:
    code, output, _ = coverage.run(["lake", "env", "lean", str(FIXTURE)], timeout=180)
    if code != 0:
        raise RuntimeError(f"closure fixture does not compile:\n{output}")
    entries = coverage.syntax_inventory_file(FIXTURE, MODULE, 180)
    entries = [entry for entry in entries if entry["kind"] in coverage.SUPPORTED_KINDS]
    if len(entries) != 6:
        raise RuntimeError(f"expected six closure fixture occurrences: {entries!r}")

    coverage.OUTPUT = ROOT / ".lake" / "g1-closure-fixture"
    coverage.RESULTS = coverage.OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = coverage.OUTPUT / "aggregate-results"
    record = coverage.run_closure_module(
        MODULE,
        entries,
        "fixture-rev",
        180,
        keep_copy=True,
        source_path=FIXTURE,
    )
    if record.get("schema") != coverage.CLOSURE_SCHEMA:
        raise RuntimeError(f"unexpected closure schema: {record!r}")
    if record.get("schemaVersion") != coverage.CLOSURE_SCHEMA_VERSION:
        raise RuntimeError(f"unexpected closure schema version: {record!r}")
    if record.get("recording", {}).get("compile_count") != 1:
        raise RuntimeError(f"closure recording was not singular: {record!r}")
    if not record.get("aggregate", {}).get("compile"):
        raise RuntimeError(f"closure fixture optimistic aggregate failed: {record!r}")
    if record.get("aggregate", {}).get("closure_complete") is not False:
        raise RuntimeError(f"fallback-dependent fixture was marked closure-complete: {record!r}")
    if record.get("aggregate", {}).get("materialization_compile_count") != 1:
        raise RuntimeError(f"closure fixture did not use one optimistic materialization: {record!r}")

    ordered = sorted(entries, key=lambda entry: entry["startByte"])
    ordinary, shared, dead, abandoned, committed_first, failed_first = ordered
    by_id = {occurrence["id"]: occurrence for occurrence in record["occurrences"]}
    if by_id[ordinary["id"]]["terminal_outcome"] != "materialized":
        raise RuntimeError("ordinary closure replacement was not materialized")
    if by_id[shared["id"]]["terminal_outcome"] != "materialized":
        raise RuntimeError("shared owner closure replacement was not materialized")
    if by_id[shared["id"]]["candidate"]["kind"] != "syntax_owner":
        raise RuntimeError("shared occurrence did not use the F2 owner materializer")
    if by_id[dead["id"]]["terminal_outcome"] != "not_reached":
        raise RuntimeError("dead first branch was not classified as not_reached")
    if by_id[abandoned["id"]]["terminal_outcome"] != "attempted_backtracked":
        raise RuntimeError("abandoned first branch was not classified as attempted_backtracked")
    if by_id[committed_first["id"]]["terminal_outcome"] != "coverage_failure":
        raise RuntimeError("closed first owner bypassed the operational completion gate")
    if by_id[committed_first["id"]].get("failure_reason") != "inadmissible_enclosing_body_proof":
        raise RuntimeError("closed first owner lost its fallback rejection reason")
    if by_id[committed_first["id"]].get("candidate") is not None:
        raise RuntimeError("closed first owner produced a materialization candidate")
    if by_id[failed_first["id"]]["terminal_outcome"] != "attempted_backtracked":
        raise RuntimeError("failed first candidate was not retained as backtracked")

    serialized = json.dumps(record, ensure_ascii=False, sort_keys=True)
    if any(marker in serialized for marker in FORBIDDEN):
        raise RuntimeError("closure record contains a raw internal identity")

    candidates = [
        occurrence["candidate"]
        for occurrence in record["occurrences"]
        if occurrence.get("candidate") is not None
    ]
    if len(candidates) != 2:
        raise RuntimeError(f"unexpected closure candidate count: {candidates!r}")
    mutated = [dict(candidate) for candidate in candidates]
    mutated[0]["replacement"] = "exact True.intro"
    source = FIXTURE.read_bytes()
    optimistic = coverage.compile_closure_candidates(
        MODULE,
        source,
        mutated,
        180,
        label="mutation-optimistic",
        keep_copy=True,
    )
    if optimistic.get("compile"):
        raise RuntimeError("mutated optimistic closure unexpectedly compiled")
    diagnostics = coverage.diagnose_closure_candidates(
        MODULE, source, mutated, 180, keep_copy=True
    )
    diagnostic_attempts = diagnostics.get("attempts", [])
    singleton_failures = diagnostics.get("singleton_failures", {})
    if not diagnostic_attempts:
        raise RuntimeError("mutation did not produce declaration diagnostics")
    mutated_id = mutated[0]["entry_ids"][0]
    if set(singleton_failures) != {mutated_id}:
        raise RuntimeError(f"mutation did not isolate exactly the failing singleton: {diagnostics!r}")
    if not singleton_failures[mutated_id]:
        raise RuntimeError(f"mutation singleton has no stable failure reason: {diagnostics!r}")
    if not any(attempt.get("compile") for attempt in diagnostic_attempts):
        raise RuntimeError(f"mutation diagnostics did not retain a passing subset: {diagnostics!r}")
    survivors = [candidate for candidate in mutated if mutated_id not in candidate["entry_ids"]]
    survivor = coverage.compile_closure_candidates(
        MODULE,
        source,
        survivors,
        180,
        label="mutation-survivor-optimistic",
        keep_copy=True,
    )
    if not survivor.get("compile"):
        raise RuntimeError(f"unmutated survivor aggregate did not compile: {survivor!r}")
    if set(survivor.get("candidate_ids", [])) != {
        identifier
        for candidate in survivors
        for identifier in candidate["entry_ids"]
    }:
        raise RuntimeError(f"survivor aggregate omitted an unmutated candidate: {survivor!r}")
    if singleton_failures.get(mutated_id) == "aggregate_interaction":
        raise RuntimeError(f"mutated singleton was misclassified as an interaction: {diagnostics!r}")
    mutation_aggregate_compile = bool(optimistic.get("compile"))
    mutation_complete = mutation_aggregate_compile and not singleton_failures
    if mutation_aggregate_compile or mutation_complete:
        raise RuntimeError("mutated module was incorrectly marked aggregate-complete")

    path = coverage.closure_module_path(MODULE)
    fixture_source_sha256 = coverage.closure_source_sha256(FIXTURE.read_bytes())
    fixture_ids_digest = coverage.closure_occurrence_ids_digest(entries)
    if not coverage.closure_record_complete(
        path,
        MODULE,
        "fixture-rev",
        source_sha256=fixture_source_sha256,
        expected_occurrence_ids_digest=fixture_ids_digest,
    ):
        raise RuntimeError("finished incomplete closure record was not resumable")
    if not coverage.closure_record_matches_inventory(
        record, MODULE, entries, "fixture-rev", source_path=FIXTURE
    ):
        raise RuntimeError("current incomplete closure record did not match its inventory")
    corrupted = dict(record)
    corrupted["occurrences"] = list(record["occurrences"][:-1])
    if coverage.closure_record_matches_inventory(
        corrupted, MODULE, entries, "fixture-rev", source_path=FIXTURE
    ):
        raise RuntimeError("corrupted occurrence array was accepted as current")
    incomplete = coverage.OUTPUT / "resume-incomplete.json"
    coverage.write_json_atomic(
        incomplete,
        {"schema": coverage.CLOSURE_SCHEMA, "schemaVersion": coverage.CLOSURE_SCHEMA_VERSION,
         "module": MODULE, "mathlib_revision": "fixture-rev", "complete": False},
    )
    if coverage.closure_record_complete(
        incomplete,
        MODULE,
        "fixture-rev",
        source_sha256=fixture_source_sha256,
        expected_occurrence_ids_digest=fixture_ids_digest,
    ):
        raise RuntimeError("incomplete closure record was incorrectly resumable")
    incomplete.unlink(missing_ok=True)

    # Exercise the production singleton path as well as the lower-level
    # mutation diagnostics above.  The planner hook is test-local: it changes
    # only one replacement text, while recording and all driver decisions stay
    # real.  A complete candidate plan must remain true even though the
    # materialized aggregate is incomplete after the singleton rejection.
    fixture_output = coverage.OUTPUT
    fixture_results = coverage.RESULTS
    fixture_aggregate_results = coverage.AGGREGATE_RESULTS
    mutation_output = ROOT / ".lake" / "g1-closure-mutation-driver"
    coverage.OUTPUT = mutation_output
    coverage.RESULTS = mutation_output / "results"
    coverage.AGGREGATE_RESULTS = mutation_output / "aggregate-results"
    original_candidate_plan = coverage.closure_candidate_plan

    def mutated_candidate_plan(source_bytes, plan_entries, recording):
        planned_candidates, planned_results = original_candidate_plan(
            source_bytes, plan_entries, recording
        )
        if planned_candidates:
            planned_candidates = [dict(candidate) for candidate in planned_candidates]
            planned_candidates[0]["replacement"] = "exact True.intro"
        return planned_candidates, planned_results

    coverage.closure_candidate_plan = mutated_candidate_plan
    try:
        mutation_record = coverage.run_closure_module(
            MODULE,
            entries,
            "mutation-driver-rev",
            180,
            keep_copy=True,
            source_path=FIXTURE,
        )
    finally:
        coverage.closure_candidate_plan = original_candidate_plan
        coverage.OUTPUT = fixture_output
        coverage.RESULTS = fixture_results
        coverage.AGGREGATE_RESULTS = fixture_aggregate_results
    mutation_aggregate = mutation_record["aggregate"]
    if mutation_aggregate.get("candidate_plan_complete") is not False:
        raise RuntimeError(f"body-proof rejection was lost from planning completeness: {mutation_record!r}")
    if mutation_aggregate.get("closure_complete") is not False:
        raise RuntimeError(f"singleton rejection was marked closure-complete: {mutation_record!r}")
    if mutation_aggregate.get("compile") is not False:
        raise RuntimeError(f"mutated singleton aggregate unexpectedly compiled: {mutation_record!r}")
    if mutation_aggregate.get("survivor_compile") is not True:
        raise RuntimeError(f"mutated singleton survivor aggregate did not compile: {mutation_record!r}")
    driver_mutated_ids = set(mutation_aggregate.get("singleton_failures", {}))
    if len(driver_mutated_ids) != 1:
        raise RuntimeError(f"driver did not retain the mutated singleton: {mutation_record!r}")
    driver_mutated_id = next(iter(driver_mutated_ids))
    mutation_outcomes = {
        occurrence["id"]: occurrence["terminal_outcome"]
        for occurrence in mutation_record["occurrences"]
    }
    if mutation_outcomes.get(driver_mutated_id) != "coverage_failure":
        raise RuntimeError(f"driver did not classify the mutated occurrence: {mutation_record!r}")
    if sum(outcome == "materialized" for outcome in mutation_outcomes.values()) != 1:
        raise RuntimeError(f"driver did not materialize the operational survivor: {mutation_record!r}")

    rewrite_failure = coverage.compile_closure_candidates(
        MODULE,
        source,
        [mutated[0], dict(mutated[0])],
        180,
        label="mutation-source-rewrite-failure",
        keep_copy=True,
    )
    if rewrite_failure.get("compile_invoked") is not False:
        raise RuntimeError(f"source rewrite failure was counted as a compile: {rewrite_failure!r}")
    if rewrite_failure.get("failure_reason") != "source_rewrite_failure":
        raise RuntimeError(f"source rewrite failure lost its stable reason: {rewrite_failure!r}")

    # A valid candidate must remain materialized when another occurrence has
    # an independent planning failure.  Change the shared owner's metadata to
    # an unsupported first-owner shape while retaining its real occurrence
    # identity/source range; this exercises candidate_plan_complete without
    # changing the copied source or recorder.
    planning_output = ROOT / ".lake" / "g1-closure-planning-fixture"
    coverage.OUTPUT = planning_output
    coverage.RESULTS = planning_output / "results"
    coverage.AGGREGATE_RESULTS = planning_output / "aggregate-results"
    planned_failure = dict(shared)
    planned_failure["ownerKind"] = "first"
    planning_record = coverage.run_closure_module(
        MODULE,
        [ordinary, planned_failure],
        "planning-rev",
        180,
        keep_copy=True,
        source_path=FIXTURE,
    )
    planning_by_id = {
        occurrence["id"]: occurrence
        for occurrence in planning_record["occurrences"]
    }
    if planning_record["aggregate"].get("compile") is not True:
        raise RuntimeError(f"valid candidate aggregate was invalidated by planning failure: {planning_record!r}")
    if planning_record["aggregate"].get("candidate_plan_complete") is not False:
        raise RuntimeError(f"planning failure was not reported separately: {planning_record!r}")
    if planning_record["aggregate"].get("closure_complete") is not False:
        raise RuntimeError(f"incomplete closure was reported complete: {planning_record!r}")
    if planning_by_id[ordinary["id"]]["terminal_outcome"] != "materialized":
        raise RuntimeError("valid candidate was not materialized alongside planning failure")
    failed_planning = planning_by_id[planned_failure["id"]]
    if failed_planning["terminal_outcome"] != "coverage_failure":
        raise RuntimeError("deliberate planning failure was not retained")
    if failed_planning.get("failure_reason") != "inadmissible_enclosing_body_proof":
        raise RuntimeError(f"planning failure reason changed: {failed_planning!r}")
    if planning_record["aggregate"].get("replacement_count") != 1:
        raise RuntimeError(f"unexpected planned candidate count: {planning_record!r}")

    # With no replacement candidates, legitimate not-reached/backtracked
    # outcomes still complete the module after the recording compile; the
    # aggregate compile is intentionally skipped rather than reported false.
    terminal_output = ROOT / ".lake" / "g1-closure-terminal-fixture"
    coverage.OUTPUT = terminal_output
    coverage.RESULTS = terminal_output / "results"
    coverage.AGGREGATE_RESULTS = terminal_output / "aggregate-results"
    terminal_entries = [dead, abandoned, failed_first]
    terminal_record = coverage.run_closure_module(
        MODULE,
        terminal_entries,
        "terminal-rev",
        180,
        keep_copy=True,
        source_path=FIXTURE,
    )
    if terminal_record["aggregate"].get("compile") is not None:
        raise RuntimeError(f"candidate-free module unexpectedly compiled an aggregate: {terminal_record!r}")
    if terminal_record["aggregate"].get("candidate_plan_complete") is not True:
        raise RuntimeError(f"candidate-free terminal outcomes were not complete: {terminal_record!r}")
    if terminal_record["aggregate"].get("closure_complete") is not True:
        raise RuntimeError(f"candidate-free terminal outcomes were not closure-complete: {terminal_record!r}")
    terminal_by_id = {
        occurrence["id"]: occurrence
        for occurrence in terminal_record["occurrences"]
    }
    if terminal_by_id[dead["id"]]["terminal_outcome"] != "not_reached":
        raise RuntimeError("candidate-free not-reached outcome changed")
    if any(
        terminal_by_id[entry["id"]]["terminal_outcome"] != "attempted_backtracked"
        for entry in (abandoned, failed_first)
    ):
        raise RuntimeError("candidate-free backtracked outcome changed")

    # A failed recording compile cannot establish not-reached status.  Use a
    # synthetic recorder result so this conservative classification remains a
    # fast unit-level regression rather than another Lean compile.
    recording_output = ROOT / ".lake" / "g1-closure-recording-failure-fixture"
    coverage.OUTPUT = recording_output
    coverage.RESULTS = recording_output / "results"
    coverage.AGGREGATE_RESULTS = recording_output / "aggregate-results"
    original_recording = coverage.passive_module_recording

    def failed_recording(*_args, **_kwargs):
        return {
            "compile": False,
            "compile_count": 1,
            "elapsed_seconds": 0,
            "report_count": 0,
            "observed_occurrence_ids": [],
            "reports": [],
            "first_owner_reports": [],
            "failure_category": "recording_compile_failure",
        }

    coverage.passive_module_recording = failed_recording
    try:
        failed_record = coverage.run_closure_module(
            MODULE,
            entries,
            "recording-failure-rev",
            180,
            keep_copy=True,
            source_path=FIXTURE,
        )
    finally:
        coverage.passive_module_recording = original_recording
    if any(
        occurrence["terminal_outcome"] != "coverage_failure"
        or occurrence.get("failure_reason") != "recording_compile_failure"
        for occurrence in failed_record["occurrences"]
    ):
        raise RuntimeError(f"failed recording was treated as reachability data: {failed_record!r}")
    for label, checked_record in (
        ("base", record),
        ("mutation", mutation_record),
        ("planning", planning_record),
        ("terminal", terminal_record),
        ("recording-failure", failed_record),
    ):
        if any(
            occurrence.get("terminal_outcome") == "coverage_failure"
            and not occurrence.get("failure_reason")
            for occurrence in checked_record.get("occurrences", [])
        ):
            raise RuntimeError(f"{label} record has an unreasoned coverage failure")

    # Summary validation must exclude a stale/corrupted record rather than
    # counting it as a complete module.  Keep this check synthetic so it does
    # not require a corpus-wide closure run.
    summary_output = ROOT / ".lake" / "g1-closure-summary-fixture"
    summary_record = json.loads(json.dumps(record))
    summary_record["mathlib_revision"] = "summary-rev"
    corrupted_summary = json.loads(json.dumps(summary_record))
    corrupted_summary["occurrences"] = corrupted_summary["occurrences"][:-1]
    summary_inventory = {
        "mathlib_revision": "summary-rev",
        "entries": entries,
    }
    original_output = coverage.OUTPUT
    original_inventory_loader = coverage.load_inventory
    original_record_loader = coverage.load_closure_records
    original_mathlib = coverage.MATHLIB
    coverage.OUTPUT = summary_output
    coverage.MATHLIB = ROOT
    coverage.load_inventory = lambda: summary_inventory
    coverage.load_closure_records = lambda: [summary_record, corrupted_summary]
    try:
        summary = coverage.write_closure_summary("summary-rev")
    finally:
        coverage.OUTPUT = original_output
        coverage.MATHLIB = original_mathlib
        coverage.load_inventory = original_inventory_loader
        coverage.load_closure_records = original_record_loader
    if summary.get("valid_recorded_modules") != 1:
        raise RuntimeError(f"summary did not retain the valid module: {summary!r}")
    if summary.get("missing_modules") or summary.get("missing_occurrences"):
        raise RuntimeError(f"summary reported valid fixture data as missing: {summary!r}")
    if summary.get("closure_modules") != {"complete": 0, "incomplete": 1}:
        raise RuntimeError(f"summary closure gate counts are wrong: {summary!r}")

    print("G1 closure retained operational survivors and rejected proof fallbacks")


if __name__ == "__main__":
    main()
