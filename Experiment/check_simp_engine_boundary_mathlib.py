#!/usr/bin/env python3
"""Materialize in-scope ``simp`` occurrences in representative Mathlib modules.

Each eligible proof-body or reusable-syntax occurrence is recorded, replaced at
its whole-occurrence range, and checked with the apply-only tactic. Excluded
non-proof and retained-quotation occurrences must remain byte-for-byte present
in the post-rewrite syntax inventory. The per-module debug trees intentionally
remain separate so a failing materialization can be inspected in isolation.
"""

from __future__ import annotations

import json
from pathlib import Path
from dataclasses import dataclass
from collections import Counter

import simp_engine_inventory as coverage
import check_simp_engine_boundary_scope as scope
from check_simp_engine_boundary_source import (
    group_report_variants,
    replace_all_occurrences,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_MARKER = "SIMP_ENGINE_BOUNDARY_ARTIFACT "
DEBUG_ROOT = ROOT / ".lake" / "boundary-mathlib-debug"


@dataclass(frozen=True)
class ModuleSpec:
    module: str
    expected_occurrences: int
    expected_eligible_occurrences: int
    debug_name: str

    @property
    def source(self) -> Path:
        return ROOT / ".lake" / "packages" / "mathlib" / Path(
            *self.module.split("/")
        )


MODULES = (
    ModuleSpec(
        "Mathlib/CategoryTheory/EqToHom.lean",
        expected_occurrences=33,
        expected_eligible_occurrences=27,
        debug_name="eq-to-hom",
    ),
    ModuleSpec(
        "Mathlib/Data/Fintype/List.lean",
        expected_occurrences=6,
        expected_eligible_occurrences=0,
        debug_name="fintype-list",
    ),
    ModuleSpec(
        "Mathlib/Algebra/Algebra/NonUnitalHom.lean",
        expected_occurrences=7,
        expected_eligible_occurrences=0,
        debug_name="non-unital-hom-parser-compatibility",
    ),
    ModuleSpec(
        "Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean",
        expected_occurrences=3,
        expected_eligible_occurrences=3,
        debug_name="cstar-pos-part",
    ),
)


ELIGIBLE_CLASSIFICATIONS = {
    "in_scope_generated_proof_command",
    "in_scope_proof_declaration",
    "in_scope_observed_proof_declaration",
    "reusable_tactic_syntax",
}
EXCLUDED_CLASSIFICATIONS = {
    "out_of_scope_declaration_signature",
    "out_of_scope_nonproof_command",
    "out_of_scope_nonproof_declaration",
    "out_of_scope_observed_nonproof_declaration",
    "out_of_scope_quotation",
}


def compiled_module_name(module: str) -> str:
    if not module.endswith(".lean"):
        raise RuntimeError(f"module path has no .lean suffix: {module}")
    return module[:-len(".lean")].replace("/", ".")


def occurrence_key(entry: dict[str, object]) -> tuple[int, int, str, str]:
    return (
        int(entry["startByte"]),
        int(entry["endByte"]),
        str(entry["kind"]),
        str(entry["source"]),
    )


def classify_entries(
    spec: ModuleSpec,
    entries: list[dict[str, object]],
    occurrences_by_module: dict[str, list[dict[str, object]]],
    declarations_by_module: dict[str, list[dict[str, object]]],
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    """Join the syntax inventory to semantic scope records one-to-one."""
    module = compiled_module_name(spec.module)
    occurrences = occurrences_by_module.get(module, [])
    declarations = declarations_by_module.get(module, [])
    if not declarations:
        raise RuntimeError(f"scope classifier found no declarations for {module}")

    inventory_by_key: dict[tuple[int, int, str, str], list[dict[str, object]]] = {}
    for entry in entries:
        inventory_by_key.setdefault(occurrence_key(entry), []).append(entry)
    scope_by_key: dict[tuple[int, int, str, str], list[dict[str, object]]] = {}
    for occurrence in occurrences:
        scope_by_key.setdefault(occurrence_key(occurrence), []).append(occurrence)

    all_keys = set(inventory_by_key) | set(scope_by_key)
    duplicate_inventory = {
        key: values for key, values in inventory_by_key.items() if len(values) != 1
    }
    duplicate_scope = {
        key: values for key, values in scope_by_key.items() if len(values) != 1
    }
    missing = sorted(set(inventory_by_key) - set(scope_by_key))
    extra = sorted(set(scope_by_key) - set(inventory_by_key))
    if duplicate_inventory or duplicate_scope or missing or extra:
        raise RuntimeError(
            f"scope/inventory join is not one-to-one for {spec.module}: "
            f"duplicate inventory={duplicate_inventory}, "
            f"duplicate scope={duplicate_scope}, missing={missing}, extra={extra}"
        )

    eligible: list[dict[str, object]] = []
    excluded: list[dict[str, object]] = []
    for key in sorted(all_keys):
        entry = inventory_by_key[key][0]
        occurrence = scope_by_key[key][0]
        result = scope.classify(occurrence, declarations)
        classification = str(result["classification"])
        if classification in ELIGIBLE_CLASSIFICATIONS:
            eligible.append(entry)
        elif classification in EXCLUDED_CLASSIFICATIONS:
            excluded.append(entry)
        else:
            raise RuntimeError(
                f"scope classification is not actionable for {spec.module}: "
                f"{classification} at {entry['startByte']}:{entry['endByte']} "
                f"{entry['source']!r}; reason={result['reason']}"
            )
    if len(eligible) + len(excluded) != len(entries):
        raise RuntimeError(
            f"scope classification did not partition {spec.module}: "
            f"total={len(entries)}, eligible={len(eligible)}, excluded={len(excluded)}"
        )
    if len(eligible) != spec.expected_eligible_occurrences:
        raise RuntimeError(
            f"expected {spec.expected_eligible_occurrences} eligible occurrences in "
            f"{spec.module}, found {len(eligible)}"
        )
    return eligible, excluded


def run(command: list[str], timeout: int = 600) -> str:
    code, output, _ = coverage.run(command, timeout=timeout)
    if code:
        raise RuntimeError(output)
    return output


def dynamic_library() -> str:
    run(["lake", "build", "ExplicitLean:shared"], timeout=600)
    output = run(
        ["lake", "query", "ExplicitLean:shared", "--json"], timeout=60
    )
    # Lake may replay dependency diagnostics before the JSON query result.
    # Parse the final nonempty line rather than treating the complete combined
    # stdout/stderr stream as one JSON value.
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if not lines:
        raise RuntimeError("lake query returned no dynamic-library path")
    value = json.loads(lines[-1])
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"lake query returned an invalid path: {value!r}")
    return value


def compile_copy(path: Path, dylib: str) -> str:
    command = coverage.lean_command(path)
    command.insert(3, f"--load-dynlib={dylib}")
    return run(command, timeout=600)


def assert_nonoverlapping(
    entries: list[dict[str, object]], module: str
) -> None:
    ordered = sorted(entries, key=lambda entry: int(entry["startByte"]))
    for left, right in zip(ordered, ordered[1:]):
        left_end = int(left["endByte"])
        right_start = int(right["startByte"])
        if left_end > right_start:
            raise RuntimeError(
                f"nested or overlapping occurrence ranges in {module}: "
                f"{left['id']} [{left['startByte']},{left['endByte']}) and "
                f"{right['id']} [{right['startByte']},{right['endByte']})"
            )


def copy_at_module_root(work: Path, module: str, source: bytes) -> Path:
    destination = work / Path(*module.split("/"))
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def instrumented_source(source: bytes, entries: list[dict[str, object]]) -> bytes:
    rewritten = coverage.rewrite_simp_heads(
        source,
        entries,
        lambda entry: f'simp_engine_boundary_record "{entry["id"]}"',
    )
    return coverage.inject_import(rewritten, "ExplicitLean.SimpEngine.Boundary")


def materialize_source(
    source: bytes,
    entries: list[dict[str, object]],
    reports: dict[str, list[dict[str, object]]],
) -> bytes:
    expected_ids = {str(entry["id"]) for entry in entries}
    if set(reports) != expected_ids:
        raise RuntimeError(
            f"materialization report IDs do not match inventory: "
            f"expected {sorted(expected_ids)}, found {sorted(reports)}"
        )
    return replace_all_occurrences(source, entries, reports)


def parse_reports(output: str) -> list[object]:
    reports: list[object] = []
    for line in output.splitlines():
        if ARTIFACT_MARKER not in line:
            continue
        try:
            reports.append(json.loads(line.split(ARTIFACT_MARKER, 1)[1]))
        except json.JSONDecodeError as error:
            raise RuntimeError(f"invalid artifact report line: {line}") from error
    return reports


def check_module(
    spec: ModuleSpec,
    dylib: str,
    occurrences_by_module: dict[str, list[dict[str, object]]],
    declarations_by_module: dict[str, list[dict[str, object]]],
) -> None:
    original = spec.source.read_bytes()
    inventory = [
        entry
        for entry in coverage.syntax_inventory_file(spec.source, spec.module, 600)
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    if len(inventory) != spec.expected_occurrences:
        raise RuntimeError(
            f"expected {spec.expected_occurrences} supported occurrences in "
            f"{spec.module}, found {len(inventory)}: {inventory}"
        )
    eligible, excluded = classify_entries(
        spec, inventory, occurrences_by_module, declarations_by_module
    )
    # Replacing an eligible outer occurrence would also rewrite a nested
    # excluded call. Fail closed until mixed-scope range composition has an
    # explicit design.
    assert_nonoverlapping(inventory, spec.module)

    work = DEBUG_ROOT / spec.debug_name
    instrumented_path = copy_at_module_root(
        work / "instrumented", spec.module, instrumented_source(original, eligible)
    )
    output = compile_copy(instrumented_path, dylib)
    report_list = parse_reports(output)
    expected_ids = [str(entry["id"]) for entry in eligible]
    reports_path = work / "artifact-reports.jsonl"
    reports_path.parent.mkdir(parents=True, exist_ok=True)
    reports_path.write_text(
        "".join(json.dumps(report, sort_keys=True) + "\n" for report in report_list),
        encoding="utf-8",
    )
    try:
        reports = group_report_variants(report_list, expected_ids)
    except RuntimeError as error:
        raise RuntimeError(
            f"{error}; generated source: {instrumented_path}\n{output}"
        ) from error

    materialized_bytes = materialize_source(original, eligible, reports)
    materialized_bytes = coverage.inject_import(
        materialized_bytes, "ExplicitLean.SimpEngine.Boundary.Tactic"
    )
    materialized_path = copy_at_module_root(
        work / "materialized", spec.module, materialized_bytes
    )
    compile_copy(materialized_path, dylib)
    remaining = [
        entry
        for entry in coverage.syntax_inventory_file(
            materialized_path,
            f"{spec.module}.materialized",
            600,
            allow_elaboration_errors=True,
        )
        if entry["kind"] in coverage.SUPPORTED_KINDS
    ]
    excluded_multiset = Counter(
        (str(entry["kind"]), str(entry["source"])) for entry in excluded
    )
    remaining_multiset = Counter(
        (str(entry["kind"]), str(entry["source"])) for entry in remaining
    )
    if remaining_multiset != excluded_multiset:
        raise RuntimeError(
            f"materialized syntax inventory differs from excluded inventory in "
            f"{spec.module}: expected {excluded_multiset}, found {remaining_multiset}; "
            f"generated source: {materialized_path}"
        )

    print(
        f"boundary {spec.module}: total={len(inventory)}, "
        f"eligible={len(eligible)}, excluded={len(excluded)}; "
        f"recorded eligible, materialized, compiled, zero remaining in-scope "
        f"(excluded retained={len(remaining)}): ok"
    )


def main() -> None:
    for spec in MODULES:
        if not spec.source.is_file():
            raise RuntimeError(f"Mathlib source not found: {spec.source}")
    scope_specs = [
        scope.ModuleSpec(
            compiled_module_name(spec.module),
            spec.source,
            spec.expected_occurrences,
        )
        for spec in MODULES
    ]
    occurrences_by_module, declarations_by_module = scope.load_records(scope_specs)
    dylib = dynamic_library()
    for spec in MODULES:
        check_module(
            spec,
            dylib,
            occurrences_by_module,
            declarations_by_module,
        )


if __name__ == "__main__":
    main()
