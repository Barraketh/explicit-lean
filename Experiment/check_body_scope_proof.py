#!/usr/bin/env python3
"""Bounded rejection regression for singleton operational source ownership."""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace
import time

import simp_coverage as coverage


MODULE = "Mathlib/Algebra/Algebra/Basic.lean"
TARGET_ID = "ef04e0e8339535de"
FORBIDDEN = ("FVarId", "Syntax.mk", "Expr.mvar", "mvarId")


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
    if aggregate.get("compile") is not False:
        raise RuntimeError(f"fallback-dependent aggregate unexpectedly compiled: {record!r}")
    if aggregate.get("closure_complete") is not False:
        raise RuntimeError(f"fallback-dependent closure was marked complete: {record!r}")
    if aggregate.get("optimistic_compile") is not False:
        raise RuntimeError(f"fallback did not retain the optimistic failure: {record!r}")

    occurrences = record.get("occurrences", [])
    if len(occurrences) != 1 or occurrences[0].get("id") != TARGET_ID:
        raise RuntimeError(f"fallback occurrence identity changed: {record!r}")
    occurrence = occurrences[0]
    if occurrence.get("terminal_outcome") != "coverage_failure":
        raise RuntimeError(f"fallback occurrence bypassed the completion gate: {record!r}")
    if occurrence.get("failure_reason") != "source_rewrite":
        raise RuntimeError(f"fallback rejection reason changed: {record!r}")
    candidate = occurrence.get("candidate")
    if not isinstance(candidate, dict) or candidate.get("kind") != "occurrence":
        raise RuntimeError(f"original operational candidate audit was lost: {record!r}")

    fallback = aggregate.get("body_scope_proof_fallback")
    final_attempt = aggregate.get("body_scope_proof_aggregate")
    if fallback is not None or final_attempt is not None:
        raise RuntimeError(f"body-proof fallback was still selected: {record!r}")
    if aggregate.get("body_scope_proof_failures") != {
        TARGET_ID: "source_rewrite"
    }:
        raise RuntimeError(f"body-proof rejection audit changed: {record!r}")
    labels = [attempt.get("label") for attempt in aggregate.get("attempts", [])]
    if "body-scope-proof-fallback" in labels or "body-scope-proof-aggregate" in labels:
        raise RuntimeError(f"body-proof compile attempt was not suppressed: {labels!r}")
    source = (coverage.MATHLIB / MODULE).read_bytes()
    actual_body = source[entry["bodyScopeStartByte"] : entry["bodyScopeEndByte"]].decode("utf-8")
    if actual_body != entry["bodyScopeSource"]:
        raise RuntimeError("production body inventory range is stale")

    serialized = json.dumps(record, ensure_ascii=False, sort_keys=True)
    if any(marker in serialized for marker in FORBIDDEN):
        raise RuntimeError("body-proof closure record contains a raw internal identity")
    elapsed = time.monotonic() - started
    print(f"singleton body-proof fallback rejected in {elapsed:.3f}s")


if __name__ == "__main__":
    main()
