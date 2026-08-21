#!/usr/bin/env python3
"""Bounded regression for the singleton whole-body proof fallback."""

from __future__ import annotations

import json
from pathlib import Path
import re
from types import SimpleNamespace
import time

import simp_coverage as coverage


MODULE = "Mathlib/Algebra/Algebra/Basic.lean"
TARGET_ID = "ef04e0e8339535de"
FORBIDDEN = ("FVarId", "Syntax.mk", "Expr.mvar", "mvarId")
STANDALONE_SIMP = re.compile(r"(?m)(?<![A-Za-z0-9_])simp(?:\s|\[|$)")


def main() -> None:
    started = time.monotonic()
    output = coverage.ROOT / ".lake" / "g-body-scope-proof"
    coverage.OUTPUT = output
    coverage.INVENTORY = output / "inventory.json"
    coverage.RESULTS = output / "results"
    coverage.AGGREGATE_RESULTS = output / "aggregate-results"

    coverage.inventory(
        SimpleNamespace(modules=[MODULE], timeout=600, batch_size=1000)
    )
    document = coverage.load_inventory()
    entries = [
        entry
        for entry in document["entries"]
        if entry["kind"] in coverage.SUPPORTED_KINDS
        and entry["id"] == TARGET_ID
    ]
    if len(entries) != 1:
        raise RuntimeError(f"expected exactly one production fallback entry: {entries!r}")
    entry = entries[0]
    if entry["module"] != MODULE:
        raise RuntimeError(f"fallback ID moved modules: {entry!r}")

    record = coverage.run_closure_module(
        MODULE,
        entries,
        document["mathlib_revision"],
        180,
        keep_copy=True,
    )
    aggregate = record.get("aggregate", {})
    if record.get("recording", {}).get("compile_count") != 1:
        raise RuntimeError(f"fallback recording was not singular: {record!r}")
    if aggregate.get("compile") is not True:
        raise RuntimeError(f"fallback final aggregate did not compile: {record!r}")
    if aggregate.get("closure_complete") is not True:
        raise RuntimeError(f"fallback closure was not complete: {record!r}")
    if aggregate.get("optimistic_compile") is not False:
        raise RuntimeError(f"fallback did not retain the optimistic failure: {record!r}")

    occurrences = record.get("occurrences", [])
    if len(occurrences) != 1 or occurrences[0].get("id") != TARGET_ID:
        raise RuntimeError(f"fallback occurrence identity changed: {record!r}")
    occurrence = occurrences[0]
    if occurrence.get("terminal_outcome") != "materialized":
        raise RuntimeError(f"fallback occurrence was not materialized: {record!r}")
    candidate = occurrence.get("candidate")
    if not isinstance(candidate, dict) or candidate.get("kind") != "body_scope_proof":
        raise RuntimeError(f"fallback did not replace the occurrence candidate: {record!r}")

    fallback = aggregate.get("body_scope_proof_fallback")
    final_attempt = aggregate.get("body_scope_proof_aggregate")
    if not isinstance(fallback, dict) or fallback.get("compile") is not True:
        raise RuntimeError(f"body-proof export attempt did not compile: {record!r}")
    if not isinstance(final_attempt, dict) or final_attempt.get("compile") is not True:
        raise RuntimeError(f"body-proof final aggregate did not compile: {record!r}")
    if fallback.get("label") != "body-scope-proof-fallback":
        raise RuntimeError(f"unexpected body-proof export label: {fallback!r}")
    if final_attempt.get("label") != "body-scope-proof-aggregate":
        raise RuntimeError(f"unexpected body-proof aggregate label: {final_attempt!r}")
    labels = [attempt.get("label") for attempt in aggregate.get("attempts", [])]
    if fallback["label"] not in labels or final_attempt["label"] not in labels:
        raise RuntimeError(f"body-proof audit attempts are missing: {labels!r}")

    reports = [
        report
        for report in fallback.get("reports", [])
        if report.get("scopeId") == entry.get("bodyScopeId")
    ]
    if len(reports) != 1:
        raise RuntimeError(f"expected one validated body-proof report: {fallback!r}")
    report = reports[0]
    proof = report.get("proof")
    local_renames = report.get("localRenames")
    if not isinstance(proof, str) or not proof.strip():
        raise RuntimeError(f"body-proof report has no proof: {report!r}")
    if report.get("closesGoal") is not True or report.get("failureReason") is not None:
        raise RuntimeError(f"body-proof report was not a clean closing result: {report!r}")
    if not isinstance(local_renames, list) or not local_renames:
        raise RuntimeError(f"body-proof report lost exact local renames: {report!r}")
    if candidate.get("localRenames") != local_renames:
        raise RuntimeError(f"candidate/local-renames metadata diverged: {candidate!r}")

    replacement = candidate.get("replacement")
    if not isinstance(replacement, str):
        raise RuntimeError(f"body-proof candidate has no source replacement: {candidate!r}")
    if not replacement.startswith("simp_explicit_rename ["):
        raise RuntimeError(f"body-proof replacement omitted exact-index rename: {replacement!r}")
    if "\nexact " not in replacement:
        raise RuntimeError(f"body-proof replacement omitted exact proof tactic: {replacement!r}")
    if STANDALONE_SIMP.search(replacement):
        raise RuntimeError(f"body-proof replacement retained ambient simp: {replacement!r}")
    if candidate.get("startByte") != entry.get("bodyScopeStartByte"):
        raise RuntimeError(f"body-proof range start changed: {candidate!r}")
    if candidate.get("endByte") != entry.get("bodyScopeEndByte"):
        raise RuntimeError(f"body-proof range end changed: {candidate!r}")
    if candidate.get("expected") != entry.get("bodyScopeSource"):
        raise RuntimeError(f"body-proof source range changed: {candidate!r}")
    source = (coverage.MATHLIB / MODULE).read_bytes()
    actual_body = source[entry["bodyScopeStartByte"] : entry["bodyScopeEndByte"]].decode("utf-8")
    if actual_body != entry["bodyScopeSource"]:
        raise RuntimeError("production body inventory range is stale")

    serialized = json.dumps(record, ensure_ascii=False, sort_keys=True)
    if any(marker in serialized for marker in FORBIDDEN):
        raise RuntimeError("body-proof closure record contains a raw internal identity")
    elapsed = time.monotonic() - started
    print(f"singleton body-proof fallback passed in {elapsed:.3f}s")


if __name__ == "__main__":
    main()
