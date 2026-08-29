#!/usr/bin/env python3
"""Close exactly the old diagnostic manifest's 101 scope unknowns.

The input manifest was deliberately produced before execution evidence existed.
This bounded diagnostic reuses only its 101 source-backed records, applies the
two fixed static exclusions, and compiles one temporary probe copy per module
for the remaining records.  It does not inventory or re-elaborate the full
Mathlib corpus.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

import check_simp_engine_boundary_scope as scope


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / ".lake/boundary-corpus-manifest/manifest.json"
MATHLIB = ROOT / ".lake/packages/mathlib"


def static_classification(occurrence: dict[str, object]) -> str | None:
    ancestors = occurrence.get("ancestors")
    if not isinstance(ancestors, list) or not all(
        isinstance(kind, str) for kind in ancestors
    ):
        raise RuntimeError(f"old unknown has invalid ancestry: {occurrence!r}")
    if "Lean.Elab.Command.command_Irreducible_def____" in ancestors:
        return "out_of_scope_nonproof_command"
    if occurrence.get("commandKind") == "Lean.Parser.Command.variable":
        return "out_of_scope_declaration_signature"
    if scope.TO_DUAL_PROOF_COMMAND in ancestors:
        return "in_scope_generated_proof_command"
    return None


def close_manifest(path: Path, timeout: int) -> Counter[str]:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    unknown_by_module: dict[str, list[dict[str, object]]] = {}
    for module_record in manifest.get("modules", []):
        if not isinstance(module_record, dict):
            raise RuntimeError(f"invalid module record in {path}: {module_record!r}")
        module = module_record.get("module")
        occurrences = module_record.get("occurrences")
        if not isinstance(module, str) or not isinstance(occurrences, list):
            raise RuntimeError(f"invalid module record in {path}: {module_record!r}")
        selected = [
            dict(occurrence)
            for occurrence in occurrences
            if isinstance(occurrence, dict)
            and occurrence.get("classification") == "unclassified"
        ]
        if selected:
            unknown_by_module[module] = selected

    old_count = sum(len(values) for values in unknown_by_module.values())
    if old_count != 101:
        raise RuntimeError(f"expected 101 old unknowns, found {old_count}")

    counts: Counter[str] = Counter()
    dynamic_count = 0
    generated_proof_count = 0
    dynamic_results: dict[str, str] = {}
    for module in sorted(unknown_by_module):
        source_path = MATHLIB / module
        source = source_path.read_bytes()
        dynamic_occurrences: list[dict[str, object]] = []
        dynamic_entries: list[dict[str, object]] = []
        for occurrence in unknown_by_module[module]:
            static = static_classification(occurrence)
            if static is not None:
                counts[static] += 1
                if static == "in_scope_generated_proof_command":
                    generated_proof_count += 1
                continue
            occurrence_id = occurrence.get("id")
            if not isinstance(occurrence_id, str) or not occurrence_id:
                raise RuntimeError(f"old unknown has no stable ID: {occurrence!r}")
            entry = dict(occurrence)
            entry["module"] = module
            entry["kind"] = entry.get("kind", "simp")
            entry["syntaxKind"] = entry.get("syntaxKind", "Lean.Parser.Tactic.simp")
            dynamic_entries.append(entry)
            dynamic_occurrences.append(occurrence)
            dynamic_count += 1
        if not dynamic_entries:
            continue
        compiled = module[: -len(".lean")].replace("/", ".")
        evidence = scope.resolve_execution_evidence(
            compiled,
            source,
            dynamic_entries,
            dynamic_occurrences,
            timeout=timeout,
        )
        if module == "Mathlib/Data/UInt.lean":
            if len(evidence) != 1:
                raise RuntimeError(
                    f"Data/UInt expected one dynamic ID, found {len(evidence)}"
                )
            data_evidence = next(iter(evidence.values()))
            if (
                data_evidence["status"] != "complete_proof_declaration"
                or data_evidence["executionCount"] != 5
            ):
                raise RuntimeError(
                    f"Data/UInt expected five proof executions: {data_evidence}"
                )
        for occurrence_id in sorted(evidence):
            status = str(evidence[occurrence_id]["status"])
            dynamic_results[occurrence_id] = status
            if status != "complete_proof_declaration":
                print(
                    f"targeted dynamic unresolved: {module}:{occurrence_id}: "
                    f"{evidence[occurrence_id]}"
                )
            if status == "complete_proof_declaration":
                counts["in_scope_observed_proof_declaration"] += 1
            elif status == "complete_nonproof_declaration":
                counts["out_of_scope_observed_nonproof_declaration"] += 1
            else:
                counts["unclassified"] += 1

    if len(dynamic_results) != dynamic_count:
        raise RuntimeError(
            f"targeted dynamic join lost IDs: expected {dynamic_count}, "
            f"found {len(dynamic_results)}"
        )
    unresolved = counts["unclassified"]
    if unresolved:
        raise RuntimeError(
            f"targeted old-unknown closure left {unresolved} unclassified: {counts}"
        )
    if counts["out_of_scope_nonproof_command"] != 38:
        raise RuntimeError(f"unexpected irreducible exclusion count: {counts}")
    if counts["out_of_scope_declaration_signature"] != 3:
        raise RuntimeError(f"unexpected variable-signature exclusion count: {counts}")
    if generated_proof_count != 5:
        raise RuntimeError(f"unexpected generated proof-command count: {counts}")
    if dynamic_count != 55:
        raise RuntimeError(f"unexpected dynamic unknown count: {dynamic_count}")
    if counts["in_scope_observed_proof_declaration"] != dynamic_count:
        raise RuntimeError(
            "measured dynamic proof classification did not close all remaining "
            f"unknowns: {counts}"
        )
    if counts["out_of_scope_observed_nonproof_declaration"]:
        raise RuntimeError(f"measured dynamic nonproof classifications: {counts}")
    print(
        "targeted old-unknown scope closure: "
        f"old=101, static_nonproof_command={counts['out_of_scope_nonproof_command']}, "
        f"static_signature={counts['out_of_scope_declaration_signature']}, "
        f"generated_proof={generated_proof_count}, dynamic={dynamic_count}, "
        f"observed_proof={counts['in_scope_observed_proof_declaration']}, "
        f"observed_nonproof={counts['out_of_scope_observed_nonproof_declaration']}, "
        f"unclassified={unresolved}: ok"
    )
    return counts


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    result.add_argument("--timeout", type=int, default=3600)
    return result


def main() -> None:
    args = parser().parse_args()
    try:
        close_manifest(args.manifest, args.timeout)
    except Exception as error:
        print(f"targeted old-unknown scope closure failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
