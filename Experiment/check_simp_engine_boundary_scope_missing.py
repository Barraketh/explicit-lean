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
import tempfile

import check_simp_engine_boundary_scope as scope


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_IDS = {
    "8a18ca2cc5877278",
    "d9b60e8150d86521",
    "6c2a52e93b5afdd3",
    "35beee1afee45baf",
    "87ef8f8d4afcf255",
}


def valid_nonproof_declaration() -> dict[str, object]:
    return {
        "module": "Test.Module",
        "name": "Test.Module.owner",
        "startByte": 0,
        "endByte": 20,
        "selectionStartByte": 0,
        "selectionEndByte": 5,
        "isProof": False,
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


def expect_diagnostic_rejection(manifest: dict[str, object], label: str) -> None:
    """Require diagnostic preconditions to reject a forged or stale input."""
    with tempfile.TemporaryDirectory(prefix=f"{label}-") as directory:
        path = Path(directory) / "diagnostic.json"
        path.write_text(json.dumps(manifest), encoding="utf-8")
        try:
            check_diagnostic_postprocess(path)
        except AssertionError:
            return
        raise AssertionError(f"{label} diagnostic was accepted")


def check_synthetic_recovery() -> None:
    """Each representative unresolved shape gets the reusable classification."""
    records = [
        dict(missing_record(declarations=[valid_nonproof_declaration()]), id=occurrence_id)
        for occurrence_id in sorted(EXPECTED_IDS)
    ]
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
    proof = valid_nonproof_declaration()
    proof["isProof"] = True
    expect_unchanged(
        missing_record(declarations=[proof]),
        "proof-valued declaration",
    )
    expect_unchanged(missing_record(declarations=[]), "no declarations")
    mixed_proof = valid_nonproof_declaration()
    mixed_proof["isProof"] = True
    expect_unchanged(
        missing_record(declarations=[valid_nonproof_declaration(), mixed_proof]),
        "mixed declarations",
    )
    expect_unchanged(
        missing_record(
            declarations=[valid_nonproof_declaration()],
            status="incomplete_execution_evidence",
        ),
        "incomplete execution evidence",
    )
    expect_unchanged(
        missing_record(declarations=[{**valid_nonproof_declaration(), "isProof": None}]),
        "unauthenticated declaration",
    )
    expect_unchanged(
        missing_record(declarations=[valid_nonproof_declaration()], quoted=False),
        "nonquoted missing execution",
    )

    valid = valid_nonproof_declaration()
    malformed = (
        ("missing module", {**valid, "module": ""}),
        ("missing name", {**valid, "name": ""}),
        ("string byte", {**valid, "startByte": "0"}),
        ("boolean byte", {**valid, "endByte": True}),
        ("reversed declaration range", {**valid, "startByte": 21}),
        ("reversed selection range", {**valid, "selectionStartByte": 6}),
        ("selection outside declaration", {**valid, "selectionEndByte": 21}),
        ("nonbool isProof", {**valid, "isProof": 0}),
        ("extra owner field", {**valid, "unexpected": "value"}),
    )
    for label, declaration in malformed:
        expect_unchanged(missing_record(declarations=[declaration]), label)

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


def check_diagnostic_preconditions() -> None:
    """Reject duplicate rows and stale diagnostics with no unresolved rows."""
    records = [
        dict(missing_record(declarations=[valid_nonproof_declaration()]), id=occurrence_id)
        for occurrence_id in sorted(EXPECTED_IDS)
    ]
    duplicate = {"modules": [{"occurrences": [*records, copy.deepcopy(records[0])]}]}
    expect_diagnostic_rejection(duplicate, "six-row-duplicate")

    materialized = copy.deepcopy(records)
    for occurrence in materialized:
        occurrence.update(
            executionRole="reusable_executable",
            declarationKind="caller_dependent",
            action="materialize",
        )
    zero_unresolved = {"modules": [{"occurrences": materialized}]}
    expect_diagnostic_rejection(zero_unresolved, "zero-preexisting-unresolved")


def check_diagnostic_postprocess(path: Path) -> None:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    original = copy.deepcopy(manifest)
    all_occurrences = [
        occurrence
        for module in manifest.get("modules", [])
        for occurrence in module.get("occurrences", [])
    ]
    all_ids = [str(occurrence.get("id")) for occurrence in all_occurrences]
    if len(set(all_ids)) != len(all_ids):
        raise AssertionError("diagnostic contains duplicate occurrence IDs")
    unresolved = [
        occurrence
        for occurrence in all_occurrences
        if occurrence.get("action") == "unresolved"
    ]
    if len(unresolved) != len(EXPECTED_IDS):
        raise AssertionError(
            "diagnostic must contain exactly five pre-change unresolved records: "
            f"found {len(unresolved)}"
        )
    unresolved_ids = {str(occurrence["id"]) for occurrence in unresolved}
    if unresolved_ids != EXPECTED_IDS:
        raise AssertionError(
            f"diagnostic unresolved IDs are {sorted(unresolved_ids)}, expected five targets"
        )
    target_records = [
        occurrence for occurrence in all_occurrences if str(occurrence["id"]) in EXPECTED_IDS
    ]
    if len(target_records) != len(EXPECTED_IDS) or any(
        occurrence.get("action") != "unresolved" for occurrence in target_records
    ):
        raise AssertionError("diagnostic target is already materialized or missing")
    changed: set[str] = set()
    changed_count: dict[str, int] = {}
    for module in manifest.get("modules", []):
        for occurrence in module.get("occurrences", []):
            before = copy.deepcopy(occurrence)
            if scope.reclassify_missing_quoted_execution(occurrence):
                occurrence_id = str(occurrence["id"])
                changed.add(occurrence_id)
                changed_count[occurrence_id] = changed_count.get(occurrence_id, 0) + 1
                if occurrence["executionEvidence"]["status"] != "missing_execution":
                    raise AssertionError("postprocess changed evidence status")
            if occurrence["id"] not in EXPECTED_IDS and occurrence != before:
                raise AssertionError(f"unexpected diagnostic record change: {occurrence['id']}")
    if changed != EXPECTED_IDS:
        raise AssertionError(f"postprocess changed {sorted(changed)}, expected five IDs")
    if changed_count != {occurrence_id: 1 for occurrence_id in EXPECTED_IDS}:
        raise AssertionError(f"postprocess change counts were {changed_count}")
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
    check_synthetic_recovery()
    check_fail_closed_adversaries()
    check_diagnostic_preconditions()
    if args.diagnostic:
        check_diagnostic_postprocess(args.diagnostic)
        print("PASS: missing quoted execution scope unit and diagnostic checks")
    else:
        print("PASS: missing quoted execution scope unit checks")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, KeyError, TypeError, ValueError) as error:
        print(f"missing quoted execution scope checks failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
