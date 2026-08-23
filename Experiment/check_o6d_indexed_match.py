#!/usr/bin/env python3
"""Focused O6d gate for indexed theorem replay and source-faithful match discovery."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import simp_coverage as coverage


ROOT = coverage.ROOT
MODULE = "Mathlib/Algebra/AddConstMap/Basic.lean"
TARGET_ID = "5771ee0e1343e576"
FIXTURE = ROOT / "Experiment" / "O6dIndexedMatchProbe.lean"
OUTPUT = ROOT / ".lake" / "o6d-indexed-match"
ANCHOR = "match 2 => AddConstMap.coe_mk"


def run_source(path: Path) -> tuple[int, str]:
    return coverage.run(["lake", "env", "lean", str(path)], timeout=180)[:2]


def check_focused_source() -> None:
    source = FIXTURE.read_text(encoding="utf-8")
    if source.count(ANCHOR) != 1:
        raise RuntimeError("focused O6d selector anchor is not unique")
    code, output = run_source(FIXTURE)
    if code != 0:
        raise RuntimeError(f"focused indexed-match source failed:\n{output}")

    mutated_source = source.replace(ANCHOR, "AddConstMap.coe_mk", 1)
    mutated = OUTPUT / "focused" / "O6dIndexedMatchProbe_next.lean"
    mutated.parent.mkdir(parents=True, exist_ok=True)
    mutated.write_text(mutated_source, encoding="utf-8")
    code, output = run_source(mutated)
    if code == 0:
        raise RuntimeError("first-site mutation unexpectedly compiled")
    if "ordered simp rule did not match anywhere in the remaining traversal" not in output:
        raise RuntimeError(f"first-site mutation lost its ordered-rule diagnostic:\n{output}")


def check_production() -> None:
    coverage.OUTPUT = OUTPUT
    coverage.INVENTORY = OUTPUT / "inventory.json"
    coverage.RESULTS = OUTPUT / "results"
    coverage.AGGREGATE_RESULTS = OUTPUT / "aggregate-results"
    coverage.inventory(SimpleNamespace(modules=[MODULE], timeout=600, batch_size=1000))
    document = coverage.load_inventory()
    entries = [
        entry
        for entry in document["entries"]
        if entry["kind"] in coverage.SUPPORTED_KINDS and entry["id"] == TARGET_ID
    ]
    if len(entries) != 1:
        raise RuntimeError(f"AddConstMap target occurrence changed: {entries!r}")

    record = coverage.run_closure_module(
        MODULE,
        entries,
        document["mathlib_revision"],
        180,
        keep_copy=True,
    )
    if record.get("complete") is not True:
        raise RuntimeError(f"focused AddConstMap closure did not complete: {record!r}")
    occurrence = record["occurrences"][0]
    if (
        occurrence.get("terminal_outcome") != "materialized"
        or occurrence.get("materialized_compile") is not True
        or occurrence.get("failure_reason") is not None
    ):
        raise RuntimeError(f"AddConstMap target did not materialize: {occurrence!r}")

    report = occurrence.get("report") or {}
    certificate = report.get("acceptedCertificate")
    if not isinstance(certificate, str) or certificate.count(ANCHOR) != 1:
        raise RuntimeError(f"target certificate lost its exact second match: {certificate!r}")
    if report.get("certificate") != certificate or report.get("legacyCertificate") is not None:
        raise RuntimeError(f"target report did not preserve its operational certificate: {report!r}")
    encoding = report.get("encoding") or {}
    if (
        encoding.get("matchSelectorCount") != 1
        or encoding.get("nextSelectorCount") != 6
        or encoding.get("tickSelectorCount") != 0
        or encoding.get("operationalProgramFailures") != 0
    ):
        raise RuntimeError(f"target selector encoding changed: {encoding!r}")
    candidate = occurrence.get("candidate") or {}
    if candidate.get("replacement") != certificate:
        raise RuntimeError("materialized candidate did not preserve the accepted certificate")


def main() -> None:
    check_focused_source()
    check_production()
    print("O6d indexed theorem replay and exact-match gates passed")


if __name__ == "__main__":
    main()
