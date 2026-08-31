#!/usr/bin/env python3
"""Materialize executable ``simp`` occurrences in representative Mathlib modules.

Each materialize candidate is recorded, replaced at its whole-occurrence
range, and checked with the apply-only tactic. Retained syntax-data occurrences
must remain byte-for-byte present in the post-rewrite syntax inventory. The
per-module debug trees intentionally remain separate so a failing
materialization can be inspected in isolation.
"""

from __future__ import annotations

import json
from pathlib import Path
from dataclasses import dataclass
from collections import Counter
import subprocess

import boundary_materialize_shard as materializer
import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as coverage
import check_simp_engine_boundary_scope as scope
from boundary_protocol import (
    assert_exact_source_preservation,
    check_recording_abort_markers,
    parse_framed_json_lines,
    recording_subprocess_environment,
    group_report_variants,
    reject_forbidden_generated_text,
)
from check_simp_engine_boundary_source import (
    materialization_replacement_lengths,
    replace_all_occurrences,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_MARKER = "SIMP_ENGINE_BOUNDARY_ARTIFACT "
DEBUG_ROOT = ROOT / ".lake" / "boundary-mathlib-debug"


@dataclass(frozen=True)
class ModuleSpec:
    module: str
    expected_occurrences: int
    expected_materialize_occurrences: int
    expected_oracle_counts: tuple[int, int, int, int, int, int]
    debug_name: str

    @property
    def source(self) -> Path:
        return ROOT / ".lake" / "packages" / "mathlib" / Path(
            *self.module.split("/")
        )


MODULES = (
    ModuleSpec(
        "Mathlib/Algebra/AddConstMap/Basic.lean",
        expected_occurrences=17,
        expected_materialize_occurrences=17,
        expected_oracle_counts=(143, 141, 103, 2, 0, 141),
        debug_name="add-const-map",
    ),
    ModuleSpec(
        "Mathlib/CategoryTheory/EqToHom.lean",
        expected_occurrences=33,
        expected_materialize_occurrences=33,
        expected_oracle_counts=(139, 139, 71, 5, 5, 134),
        debug_name="eq-to-hom",
    ),
    ModuleSpec(
        "Mathlib/Data/Fintype/List.lean",
        expected_occurrences=6,
        expected_materialize_occurrences=6,
        expected_oracle_counts=(15, 10, 5, 5, 0, 10),
        debug_name="fintype-list",
    ),
    ModuleSpec(
        "Mathlib/Algebra/Algebra/NonUnitalHom.lean",
        expected_occurrences=7,
        expected_materialize_occurrences=7,
        expected_oracle_counts=(165, 165, 104, 0, 0, 165),
        debug_name="non-unital-hom-parser-compatibility",
    ),
    ModuleSpec(
        "Mathlib/Analysis/CStarAlgebra/SpecialFunctions/PosPart.lean",
        expected_occurrences=3,
        expected_materialize_occurrences=3,
        expected_oracle_counts=(5, 5, 5, 0, 0, 5),
        debug_name="cstar-pos-part",
    ),
)




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

    materialize: list[dict[str, object]] = []
    retain: list[dict[str, object]] = []
    for key in sorted(all_keys):
        entry = inventory_by_key[key][0]
        occurrence = scope_by_key[key][0]
        result = scope.classify(occurrence, declarations)
        action = str(result["action"])
        if action == "materialize":
            materialize.append(entry)
        elif action == "retain":
            retain.append(entry)
        else:
            raise RuntimeError(
                f"scope classification is not actionable for {spec.module}: "
                f"{result['executionRole']}/{result['declarationKind']} at "
                f"{entry['startByte']}:{entry['endByte']} "
                f"{entry['source']!r}; reason={result['reason']}"
            )
    if len(materialize) + len(retain) != len(entries):
        raise RuntimeError(
            f"scope classification did not partition {spec.module}: "
            f"total={len(entries)}, materialize={len(materialize)}, retain={len(retain)}"
        )
    if len(materialize) != spec.expected_materialize_occurrences:
        raise RuntimeError(
            f"expected {spec.expected_materialize_occurrences} materialize occurrences in "
            f"{spec.module}, found {len(materialize)}"
        )
    return materialize, retain


def run(
    command: list[str],
    timeout: int = 600,
    *,
    env: dict[str, str] | None = None,
) -> str:
    if env is None:
        code, output, _ = coverage.run(command, timeout=timeout)
    else:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
            env=env,
        )
        code, output = completed.returncode, completed.stdout
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


def compile_copy(
    path: Path, dylib: str, *, env: dict[str, str] | None = None
) -> str:
    command = coverage.lean_command(path)
    command.insert(3, f"--load-dynlib={dylib}")
    return run(command, timeout=600, env=env)


def compile_recording_copy(path: Path, dylib: str) -> tuple[str, str]:
    """Compile one instrumented copy with an authenticated recording nonce."""
    environment, nonce = recording_subprocess_environment()
    return compile_copy(path, dylib, env=environment), nonce


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
    materialize, retain = classify_entries(
        spec, inventory, occurrences_by_module, declarations_by_module
    )
    # Replacing an outer occurrence would also rewrite a nested occurrence.
    # Fail closed until mixed-scope range composition has an explicit design.
    assert_nonoverlapping(inventory, spec.module)

    work = DEBUG_ROOT / spec.debug_name
    original_path = copy_at_module_root(work / "original", spec.module, original)
    instrumented_without_import = coverage.rewrite_simp_heads(
        original,
        materialize,
        lambda entry: f'simp_engine_boundary_record "{entry["id"]}"',
    )
    instrumented_bytes = coverage.inject_import(
        instrumented_without_import, "ExplicitLean.SimpEngine.Boundary"
    )
    assert_exact_source_preservation(
        original,
        instrumented_bytes,
        materialize,
        imported="ExplicitLean.SimpEngine.Boundary",
        label=f"instrumented source {spec.module}",
        expected_without_import=instrumented_without_import,
    )
    instrumented_path = copy_at_module_root(
        work / "instrumented", spec.module, instrumented_bytes
    )
    output, nonce = compile_recording_copy(instrumented_path, dylib)
    check_recording_abort_markers(
        output,
        expected_nonce=nonce,
        expected_module=compiled_module_name(spec.module),
    )
    report_list = parse_framed_json_lines(
        output,
        marker=ARTIFACT_MARKER,
        expected_nonce=nonce,
        label=f"boundary artifact for {spec.module}",
    )
    reject_forbidden_generated_text(report_list, f"artifact reports for {spec.module}")
    expected_ids = [str(entry["id"]) for entry in materialize]
    reports_path = work / "artifact-reports.jsonl"
    reports_path.parent.mkdir(parents=True, exist_ok=True)
    reports_path.write_text(
        "".join(json.dumps(report, sort_keys=True) + "\n" for report in report_list),
        encoding="utf-8",
    )
    try:
        reports = group_report_variants(
            report_list,
            expected_ids,
            expected_module=compiled_module_name(spec.module),
        )
    except RuntimeError as error:
        raise RuntimeError(
            f"{error}; generated source: {instrumented_path}\n{output}"
        ) from error

    materialized_without_import = materialize_source(original, materialize, reports)
    materialized_bytes = coverage.inject_import(
        materialized_without_import, "ExplicitLean.SimpEngine.Boundary.Tactic"
    )
    assert_exact_source_preservation(
        original,
        materialized_bytes,
        materialize,
        imported="ExplicitLean.SimpEngine.Boundary.Tactic",
        label=f"materialized source {spec.module}",
        expected_without_import=materialized_without_import,
        replacement_lengths=materialization_replacement_lengths(original, materialize, reports),
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
    retain_multiset = Counter(
        (str(entry["kind"]), str(entry["source"])) for entry in retain
    )
    remaining_multiset = Counter(
        (str(entry["kind"]), str(entry["source"])) for entry in remaining
    )
    if remaining_multiset != retain_multiset:
        raise RuntimeError(
            f"materialized syntax inventory differs from retained inventory in "
            f"{spec.module}: expected {retain_multiset}, found {remaining_multiset}; "
            f"generated source: {materialized_path}"
        )

    declaration_oracle = materializer.run_declaration_oracle(
        spec.module,
        original_path,
        materialized_path,
        work,
        dylib,
        600,
    )
    oracle_report = declaration_oracle["report"]
    oracle_counts = (
        oracle_report["stockDeclarationCount"],
        oracle_report["appliedDeclarationCount"],
        oracle_report["commonPublicDeclarationCount"],
        oracle_report["stockOnlyPrivateProofCount"],
        oracle_report["appliedOnlyPrivateProofCount"],
        oracle_report["checkedDeclarationCount"],
    )
    if oracle_counts != spec.expected_oracle_counts:
        raise RuntimeError(
            f"declaration oracle coverage changed for {spec.module}: "
            f"expected {spec.expected_oracle_counts}, found {oracle_counts}"
        )

    print(
        f"boundary {spec.module}: total={len(inventory)}, "
        f"materialize={len(materialize)}, retain={len(retain)}; "
        f"recorded materialize, compiled, zero remaining executable "
        f"(retained={len(remaining)}); "
        "declaration/environment oracle passed "
        f"(accounted={oracle_report['checkedDeclarationCount']}): ok"
    )


def invalidate_oracle_evidence() -> None:
    for spec in MODULES:
        module_root = DEBUG_ROOT / spec.debug_name
        for name in ("declaration-oracle.log", "declaration-oracle-report.json"):
            (module_root / name).unlink(missing_ok=True)


def main() -> None:
    invalidate_oracle_evidence()
    initial_environment = corpus.verify_environment()
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
    try:
        final_environment = corpus.verify_environment()
    except Exception:
        invalidate_oracle_evidence()
        raise
    if final_environment != initial_environment:
        invalidate_oracle_evidence()
        raise RuntimeError("pinned environment changed during representative gate")


if __name__ == "__main__":
    main()
