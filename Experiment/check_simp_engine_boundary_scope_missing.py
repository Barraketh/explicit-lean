#!/usr/bin/env python3
"""Check fail-closed recovery for missing quoted executable syntax.

The focused checks use only in-memory records.  With ``--diagnostic`` they
also postprocess the existing full-corpus diagnostic artifact, without
rerunning inventory or Lean, and require that exactly its five unresolved
records change.
"""

from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import sys

import check_simp_engine_boundary_scope as scope


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_IDS = {
    "8a18ca2cc5877278",
    "d9b60e8150d86521",
    "6c2a52e93b5afdd3",
    "35beee1afee45baf",
    "87ef8f8d4afcf255",
}


def missing_record(
    *,
    declarations: list[dict[str, object]] | None,
    quoted: bool = True,
    status: str = "missing_execution",
) -> dict[str, object]:
    """Make the smallest source-backed shape accepted by the scope helper."""
    return {
        "id": "synthetic",
        "startByte": 10,
        "endByte": 20,
        "kind": "simp",
        "source": "simp [$args,*]",
        "ancestors": (
            ["Lean.Parser.Tactic.quot", "Lean.Parser.Tactic.simp"]
            if quoted
            else ["Lean.Parser.Tactic.simp"]
        ),
        "executionEvidence": {"status": status},
        "executionRole": "unresolved",
        "declarationKind": "unknown",
        "action": "unresolved",
        "declarations": declarations,
    }


def expect_unchanged(result: dict[str, object], label: str) -> None:
    before = copy.deepcopy(result)
    if scope.reclassify_missing_quoted_execution(result):
        raise AssertionError(f"{label} was reclassified")
    if result != before:
        raise AssertionError(f"{label} changed despite fail-closed evidence")


def check_five_record_shapes() -> None:
    """Each real unresolved record shape gets the reusable classification."""
    diagnostic = ROOT / ".lake/week-2026-08-31/schema13-isolated-full-manifest-v3-unresolved-diagnostic.json"
    if not diagnostic.exists():
        # Keep the focused check reproducible without generated corpus inputs.
        records = [
            missing_record(declarations=[{"isProof": False}])
            for _ in EXPECTED_IDS
        ]
    else:
        manifest = json.loads(diagnostic.read_text(encoding="utf-8"))
        records = [
            occurrence
            for module in manifest["modules"]
            for occurrence in module["occurrences"]
            if occurrence.get("action") == "unresolved"
        ]
        if {str(record["id"]) for record in records} != EXPECTED_IDS:
            raise AssertionError("diagnostic unresolved IDs changed")
    for record in records:
        if not scope.reclassify_missing_quoted_execution(record):
            raise AssertionError(f"record was not recovered: {record.get('id')}")
        if (record["executionRole"], record["declarationKind"], record["action"]) != (
            "reusable_executable",
            "caller_dependent",
            "materialize",
        ):
            raise AssertionError(f"unexpected recovered dimensions: {record}")
        scope.validate_scope_dimensions(
            record["executionRole"], record["declarationKind"], record["action"]
        )


def check_fail_closed_adversaries() -> None:
    expect_unchanged(
        missing_record(declarations=[{"isProof": True}]),
        "proof-valued declaration",
    )
    expect_unchanged(missing_record(declarations=[]), "no declarations")
    expect_unchanged(
        missing_record(declarations=[{"isProof": False}, {"isProof": True}]),
        "mixed declarations",
    )
    expect_unchanged(
        missing_record(declarations=[{"isProof": False}], status="incomplete_execution_evidence"),
        "incomplete execution evidence",
    )
    expect_unchanged(
        missing_record(declarations=[{"isProof": None}]),
        "unauthenticated declaration",
    )
    expect_unchanged(
        missing_record(declarations=[{"isProof": False}], quoted=False),
        "nonquoted missing execution",
    )

    macro = {
        "ancestors": [
            "Lean.Parser.Command.macro",
            "Lean.Parser.Tactic.quot",
            "Lean.Parser.Tactic.simp",
        ],
        "commandKind": None,
        "startByte": 10,
        "endByte": 20,
        "kind": "simp",
        "source": "simp",
    }
    classified = scope.classify(macro, [])
    if (classified["executionRole"], classified["declarationKind"], classified["action"]) != (
        "reusable_executable",
        "caller_dependent",
        "materialize",
    ):
        raise AssertionError(f"macro reusable classification changed: {classified}")

    check = dict(macro)
    check["ancestors"] = ["Lean.Parser.Tactic.quot", "Lean.Parser.Tactic.simp"]
    check["commandKind"] = "Lean.Parser.Command.check"
    classified = scope.classify(check, [])
    if (classified["executionRole"], classified["declarationKind"], classified["action"]) != (
        "retained_syntax_data",
        "not_applicable",
        "retain",
    ):
        raise AssertionError(f"#check retained classification changed: {classified}")


def check_diagnostic_postprocess(path: Path) -> None:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    original = copy.deepcopy(manifest)
    changed: set[str] = set()
    for module in manifest.get("modules", []):
        for occurrence in module.get("occurrences", []):
            before = copy.deepcopy(occurrence)
            if scope.reclassify_missing_quoted_execution(occurrence):
                changed.add(str(occurrence["id"]))
                if occurrence["executionEvidence"]["status"] != "missing_execution":
                    raise AssertionError("postprocess changed evidence status")
            if occurrence["id"] not in EXPECTED_IDS and occurrence != before:
                raise AssertionError(f"unexpected diagnostic record change: {occurrence['id']}")
    if changed != EXPECTED_IDS:
        raise AssertionError(f"postprocess changed {sorted(changed)}, expected five IDs")
    unresolved = [
        occurrence
        for module in manifest["modules"]
        for occurrence in module["occurrences"]
        if occurrence.get("action") == "unresolved"
    ]
    if unresolved:
        raise AssertionError(f"postprocess left unresolved records: {len(unresolved)}")
    # The only permitted edits are the three dimensions and explanatory reason.
    for before_module, after_module in zip(original["modules"], manifest["modules"]):
        for before, after in zip(before_module["occurrences"], after_module["occurrences"]):
            if before["id"] not in EXPECTED_IDS and before != after:
                raise AssertionError(f"non-target record changed: {before['id']}")
            if before["id"] in EXPECTED_IDS:
                for key in before:
                    if key not in {"executionRole", "declarationKind", "action", "reason"} and before[key] != after[key]:
                        raise AssertionError(f"target changed evidence/source field: {key}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnostic", type=Path)
    args = parser.parse_args()
    check_five_record_shapes()
    check_fail_closed_adversaries()
    if args.diagnostic:
        check_diagnostic_postprocess(args.diagnostic)
    print("PASS: missing quoted execution scope checks")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, KeyError, TypeError, ValueError) as error:
        print(f"missing quoted execution scope checks failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
