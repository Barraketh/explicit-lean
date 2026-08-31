#!/usr/bin/env python3
"""Run a bounded, manifest-driven Boundary materialization shard.

The manifest is the authority for scope classification.  This runner only
consumes selected, source-verified modules: it records outermost materializable
tactic calls in a disposable module-root copy, accounts for their contained
calls, groups the resulting Boundary artifacts, replaces the complete outer
ranges, and checks that
retained syntax is the only supported simp syntax left in the generated copy.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any, Iterable

import check_simp_engine_boundary_scope as scope
import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
from process_runner import run_process
from boundary_protocol import (
    ABORT_CATEGORIES,
    OCCURRENCE_CLASSIFICATIONS,
    artifact_protocol,
    assert_exact_source_preservation,
    check_recording_abort_markers,
    check_replay_abort_markers,
    group_report_variants,
    make_occurrence_result,
    occurrence_classification_counts,
    parse_framed_json_lines,
    recording_subprocess_environment,
    replay_subprocess_environment,
    REPLAY_GUARD_KIND,
    REPLAY_GUARD_SCHEMA,
    replacement_plan,
    reject_forbidden_generated_text,
    validate_artifact_protocol,
    validate_occurrence_summary,
)
from check_simp_engine_boundary_source import (
    materialization_replacement_lengths,
    replace_all_occurrences,
)


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = corpus.MATHLIB
MANIFEST_KIND = "simp_engine_boundary_manifest"
MANIFEST_SCHEMA = 2
REPORT_KIND = "simp_engine_boundary_materialization_shard"
REPORT_SCHEMA = 10
ARTIFACT_MARKER = "SIMP_ENGINE_BOUNDARY_ARTIFACT "
DECLARATION_ORACLE_MARKER = "SIMP_ENGINE_DECLARATION_ORACLE "
DECLARATION_ORACLE_KIND = "simp_engine_declaration_oracle"
DECLARATION_ORACLE_SCHEMA = 1
BOUNDARY_DEBUG_ROOT = ROOT / ".lake" / "boundary-materialization"
FAILURE_MARKER = "SIMP_ENGINE_BOUNDARY_MATERIALIZATION_FAILURE "
FAILURE_KIND = "simp_engine_boundary_materialization_failure"
FAILURE_SCHEMA = 1


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _require_int(value: object, label: str, *, nonnegative: bool = False) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise RuntimeError(f"{label} must be an integer: {value!r}")
    if nonnegative and value < 0:
        raise RuntimeError(f"{label} must be nonnegative: {value!r}")
    return value


def _require_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"{label} must be a nonempty string: {value!r}")
    return value


def abort_category(error: BaseException) -> str | None:
    """Map known boundary aborts to the stable report taxonomy."""
    message = str(error)
    if "ambiguous_boundary_variant" in message:
        return "ambiguous_boundary_variant"
    if (
        "boundary_comparison_unsupported_environment_delta" in message
        or "boundary_state_delta_unsupported" in message
        or "boundary_comparison_extra_module_uses" in message
        or "boundary_comparison_missing_stock_extension" in message
        or "boundary_comparison_missing_applied_extension" in message
        or "boundary_comparison_nondeterministic_extension_serialization" in message
        or "boundary_comparison_extension_state" in message
    ):
        return "external_effect_failure"
    if "declaration_value_mismatch" in message:
        return "declaration_value_mismatch"
    if "environment_delta_mismatch" in message:
        return "environment_delta_mismatch"
    if (
        "unstable printer output" in message
        or "invalid explicit-printer source" in message
        or "internal metavariable name" in message
    ):
        return "printer_failure"
    return None


def emit_failure_marker(error: BaseException, stream: Any = sys.stderr) -> bool:
    """Emit the exact stable failure marker for a known boundary abort."""
    category = abort_category(error)
    if category is None:
        return False
    if category not in ABORT_CATEGORIES:
        raise RuntimeError(f"unknown boundary abort category: {category}") from error
    print(
        FAILURE_MARKER
        + json.dumps(
            {
                "kind": FAILURE_KIND,
                "schema": FAILURE_SCHEMA,
                "category": category,
                "detail": str(error),
            },
            ensure_ascii=False,
            sort_keys=True,
        ),
        file=stream,
    )
    return True


def _command_output(command: list[str], timeout: int, label: str) -> str:
    code, output, _elapsed = _run_command(command, timeout)
    if code != 0:
        raise RuntimeError(f"{label} failed (exit {code}):\n{output}")
    return output


def _run_command(
    command: list[str], timeout: int, *, env: dict[str, str] | None = None
) -> tuple[int, str, float]:
    started = time.monotonic()
    try:
        completed = run_process(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
            env=env,
        )
        return completed.returncode, completed.stdout, time.monotonic() - started
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return (
            124,
            output + "\nexplicit-lean: compilation timed out\n",
            time.monotonic() - started,
        )


def _current_commit(timeout: int) -> str:
    return _command_output(["git", "rev-parse", "HEAD"], timeout, "git rev-parse HEAD").strip()


def _safe_relative_root(path: Path, root: Path, label: str) -> Path:
    """Resolve a manifest-relative path without permitting root escape."""
    if path.is_absolute():
        raise RuntimeError(f"{label} must be relative to the repository: {path}")
    resolved = (root / path).resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError as error:
        raise RuntimeError(f"{label} escapes repository root: {path}") from error
    return resolved


def verify_implementation_hashes(manifest: dict[str, Any]) -> None:
    values = manifest.get("implementationHashes")
    if not isinstance(values, dict):
        raise RuntimeError("manifest implementationHashes must be an object")
    for raw_path, expected in sorted(values.items()):
        if not isinstance(raw_path, str) or not raw_path:
            raise RuntimeError(f"manifest has an invalid implementation path: {raw_path!r}")
        expected_hash = _require_string(expected, f"implementation hash {raw_path}")
        path = _safe_relative_root(Path(raw_path), ROOT, "implementation path")
        if not path.is_file():
            raise RuntimeError(f"manifest implementation source is missing: {raw_path}")
        actual = sha256(path.read_bytes())
        if actual != expected_hash:
            raise RuntimeError(
                f"implementation source changed: {raw_path}: {actual} != {expected_hash}"
            )
    current = corpus.implementation_hashes()
    if values != current:
        missing = sorted(set(current) - set(values))
        extra = sorted(set(values) - set(current))
        changed = sorted(
            path for path in set(values) & set(current) if values[path] != current[path]
        )
        raise RuntimeError(
            "manifest implementation source set is not current: "
            f"missing={missing}, extra={extra}, changed={changed}"
        )


def resolve_output_path(raw_output: str, manifest_path: Path) -> Path:
    output_path = Path(raw_output)
    if not output_path.is_absolute():
        output_path = ROOT / output_path
    output_path = output_path.resolve()
    if output_path == manifest_path:
        raise RuntimeError("materialization report must not overwrite its input manifest")
    output_root = BOUNDARY_DEBUG_ROOT.resolve()
    try:
        output_path.relative_to(output_root)
    except ValueError as error:
        raise RuntimeError(
            "generated reports must stay under .lake/boundary-materialization"
        ) from error
    protected_roots = (
        MATHLIB.resolve(),
        (ROOT / "ExplicitLean").resolve(),
        (ROOT / "Experiment").resolve(),
    )
    for protected in protected_roots:
        try:
            output_path.relative_to(protected)
        except ValueError:
            continue
        raise RuntimeError(f"materialization report targets protected source: {output_path}")
    return output_path


def invalidate_output(output_path: Path) -> None:
    """Remove only this run's exact report and atomic-write temporary sibling."""
    output_path.unlink(missing_ok=True)
    output_path.with_name(output_path.name + ".tmp").unlink(missing_ok=True)


def _paths_overlap(first: Path, second: Path) -> bool:
    """Return whether either path is an ancestor of the other."""
    # ``Path.absolute`` preserves ``..`` components.  Normalize those lexical
    # components without resolving symlinks, since a symlink at the manifest
    # location is itself vulnerable to run-subtree cleanup.
    first = Path(os.path.abspath(first))
    second = Path(os.path.abspath(second))
    return (
        first == second
        or first.is_relative_to(second)
        or second.is_relative_to(first)
    )


def validate_cleanup_targets(
    manifest_path: Path,
    output_path: Path,
    debug_root: Path,
    *,
    manifest_location: Path | None = None,
) -> None:
    """Reject an input manifest that any pre-run cleanup could remove.

    ``clear_debug_root`` recursively removes the run subtree, while
    ``invalidate_output`` removes both the report and its atomic-write
    temporary sibling.  Check the lexical input location as well as its
    resolved target so a manifest symlink inside a cleanup target is protected
    before either cleanup operation starts.
    """
    input_paths = [Path(os.path.abspath(manifest_path))]
    if manifest_location is not None:
        input_paths.append(Path(os.path.abspath(manifest_location)))
    cleanup_targets = (
        Path(os.path.abspath(output_path)),
        Path(os.path.abspath(output_path.with_name(output_path.name + ".tmp"))),
        Path(os.path.abspath(debug_root)),
    )
    for input_path in input_paths:
        for cleanup_target in cleanup_targets:
            if _paths_overlap(input_path, cleanup_target):
                raise RuntimeError(
                    "input manifest overlaps a cleanup target: "
                    f"{input_path} and {cleanup_target}"
                )


def verify_environment(manifest: dict[str, Any], timeout: int) -> dict[str, Any]:
    expected_repository = _require_string(
        manifest.get("repositoryCommit"), "manifest repositoryCommit"
    )
    actual_repository = _current_commit(timeout)
    if actual_repository != expected_repository:
        raise RuntimeError(
            f"moving_ref: expected {expected_repository}, checked out {actual_repository}"
        )

    expected_mathlib = _require_string(manifest.get("mathlibCommit"), "manifest mathlibCommit")
    lake_mathlib = corpus.pinned_mathlib_commit()
    if lake_mathlib != expected_mathlib:
        raise RuntimeError(
            f"lake manifest Mathlib revision differs from boundary manifest: "
            f"{lake_mathlib} != {expected_mathlib}"
        )
    actual_mathlib = _command_output(
        ["git", "-C", str(MATHLIB), "rev-parse", "HEAD"],
        timeout,
        "Mathlib git rev-parse HEAD",
    ).strip()
    if actual_mathlib != expected_mathlib:
        raise RuntimeError(
            f"mathlib_commit_mismatch:{actual_mathlib}!={expected_mathlib}"
        )
    mathlib_status = _command_output(
        ["git", "-C", str(MATHLIB), "status", "--porcelain", "--untracked-files=all"],
        timeout,
        "Mathlib git status",
    ).strip()
    if mathlib_status:
        raise RuntimeError("mathlib_dirty_worktree")

    lean = manifest.get("lean")
    if not isinstance(lean, dict):
        raise RuntimeError(f"manifest lean provenance must be an object: {lean!r}")
    expected_version = _require_string(lean.get("version"), "manifest Lean version")
    expected_lean_commit = _require_string(lean.get("commit"), "manifest Lean commit")
    actual_version = _command_output(["lean", "--version"], timeout, "lean --version").strip()
    if (
        f"version {expected_version}" not in actual_version
        or f"commit {expected_lean_commit}" not in actual_version
    ):
        raise RuntimeError(
            f"unexpected Lean toolchain: {actual_version}; expected "
            f"Lean {expected_version} {expected_lean_commit}"
        )
    return {
        "repositoryCommit": actual_repository,
        "mathlibCommit": actual_mathlib,
        "lean": {"version": expected_version, "commit": expected_lean_commit},
    }


def _validate_count_map(
    value: object, label: str, allowed: set[str]
) -> dict[str, int]:
    if not isinstance(value, dict):
        raise RuntimeError(f"manifest {label} must be an object")
    result: dict[str, int] = {}
    for key, raw_count in value.items():
        if not isinstance(key, str) or key not in allowed:
            raise RuntimeError(f"manifest {label} has an unknown key: {key!r}")
        result[key] = _require_int(raw_count, f"manifest {label}.{key}", nonnegative=True)
    return result


@dataclass(frozen=True)
class SelectedModule:
    module: str
    compiled_module: str
    source_path: Path
    source: bytes
    occurrences: tuple[dict[str, Any], ...]
    materialize: tuple[dict[str, Any], ...]
    retain: tuple[dict[str, Any], ...]

    @property
    def replacement_roots(self) -> list[dict[str, Any]]:
        return replacement_plan(self.source, self.materialize, self.module)[0]

    @property
    def covered_by(self) -> dict[str, str]:
        return replacement_plan(self.source, self.materialize, self.module)[1]


def _validate_occurrence(
    module: str, source: bytes, occurrence: object
) -> dict[str, Any]:
    if not isinstance(occurrence, dict):
        raise RuntimeError(f"manifest occurrence is not an object in {module}: {occurrence!r}")
    result = dict(occurrence)
    result["module"] = module
    occurrence_id = _require_string(result.get("id"), f"{module} occurrence id")
    kind = _require_string(result.get("kind"), f"{module} occurrence kind")
    if kind not in inventory.SUPPORTED_KINDS:
        raise RuntimeError(f"unsupported manifest occurrence kind in {module}: {kind!r}")
    source_text = result.get("source")
    if not isinstance(source_text, str):
        raise RuntimeError(f"manifest occurrence source is not a string in {module}")
    start = _require_int(result.get("startByte"), f"{module} occurrence startByte")
    end = _require_int(result.get("endByte"), f"{module} occurrence endByte")
    expected_id = inventory.occurrence_id(module, start, end)
    if occurrence_id != expected_id:
        raise RuntimeError(
            f"manifest occurrence ID mismatch in {module}: "
            f"{occurrence_id} != {expected_id}"
        )
    syntax_kind = result.get("syntaxKind")
    # ``simp only`` is represented by the same parser node as ``simp``; the
    # inventory's ``kind`` field distinguishes the source command variant.
    expected_syntax_kind = "Lean.Parser.Tactic.simp"
    if syntax_kind != expected_syntax_kind:
        raise RuntimeError(
            f"manifest occurrence syntax kind mismatch in {module}:{start}: "
            f"{syntax_kind!r} != {expected_syntax_kind!r}"
        )
    inventory.validate_occurrence(source, result)
    execution_role = _require_string(
        result.get("executionRole"), f"{module} occurrence executionRole"
    )
    declaration_kind = _require_string(
        result.get("declarationKind"), f"{module} occurrence declarationKind"
    )
    action = _require_string(result.get("action"), f"{module} occurrence action")
    try:
        scope.validate_scope_dimensions(execution_role, declaration_kind, action)
    except RuntimeError as error:
        raise RuntimeError(
            f"manifest occurrence has invalid scope dimensions in {module}:{start}: {error}"
        ) from error
    return result


def validate_manifest_selection(
    manifest: dict[str, Any],
    selected_names: list[str],
    *,
    expect_total: int | None,
    expect_materialize: int | None,
) -> list[SelectedModule]:
    try:
        corpus.enforce_manifest_policy(manifest)
    except RuntimeError as error:
        raise RuntimeError(f"boundary manifest policy validation failed: {error}") from error
    if manifest.get("reportSchema") != MANIFEST_SCHEMA:
        raise RuntimeError(
            f"unsupported boundary manifest schema: {manifest.get('reportSchema')!r}"
        )
    if manifest.get("kind") != MANIFEST_KIND:
        raise RuntimeError(f"unexpected boundary manifest kind: {manifest.get('kind')!r}")
    if manifest.get("allowUnresolved") is not False:
        raise RuntimeError("boundary materialization requires allowUnresolved=false")
    if manifest.get("allowDirty") is not False:
        raise RuntimeError("boundary materialization requires allowDirty=false")

    modules = manifest.get("modules")
    if not isinstance(modules, list):
        raise RuntimeError("manifest modules must be an array")
    module_file_count = _require_int(
        manifest.get("moduleFileCount"), "manifest moduleFileCount", nonnegative=True
    )
    if module_file_count != len(modules):
        raise RuntimeError(
            f"manifest moduleFileCount disagrees with modules: {module_file_count} != {len(modules)}"
        )

    declared_total = _require_int(
        manifest.get("occurrenceCount"), "manifest occurrenceCount", nonnegative=True
    )
    declared_execution_roles = _validate_count_map(
        manifest.get("countsByExecutionRole"),
        "countsByExecutionRole",
        corpus.EXECUTION_ROLES,
    )
    declared_declaration_kinds = _validate_count_map(
        manifest.get("countsByDeclarationKind"),
        "countsByDeclarationKind",
        corpus.DECLARATION_KINDS,
    )
    declared_actions = _validate_count_map(
        manifest.get("countsByAction"),
        "countsByAction",
        corpus.ACTIONS,
    )
    if sum(declared_execution_roles.values()) != declared_total:
        raise RuntimeError(
            "manifest execution-role counts do not sum to occurrenceCount: "
            f"{declared_execution_roles} != {declared_total}"
        )
    if sum(declared_declaration_kinds.values()) != declared_total:
        raise RuntimeError(
            "manifest declaration-kind counts do not sum to occurrenceCount: "
            f"{declared_declaration_kinds} != {declared_total}"
        )
    if sum(declared_actions.values()) != declared_total:
        raise RuntimeError(
            "manifest action counts do not sum to occurrenceCount: "
            f"{declared_actions} != {declared_total}"
        )

    module_records: dict[
        str, tuple[dict[str, Any], Path, bytes, tuple[dict[str, Any], ...]]
    ] = {}
    actual_execution_roles: Counter[str] = Counter()
    actual_declaration_kinds: Counter[str] = Counter()
    actual_actions: Counter[str] = Counter()
    seen_occurrence_ids: set[str] = set()
    all_occurrences = 0
    for raw_module in modules:
        if not isinstance(raw_module, dict):
            raise RuntimeError(f"manifest module record is not an object: {raw_module!r}")
        module = _require_string(raw_module.get("module"), "manifest module name")
        if module in module_records:
            raise RuntimeError(f"manifest contains duplicate module record: {module}")
        if not module.startswith("Mathlib/") or not module.endswith(".lean"):
            raise RuntimeError(f"manifest module is not a Mathlib .lean path: {module}")
        compiled = corpus.compiled_module_name(module)
        if raw_module.get("compiledModule") != compiled:
            raise RuntimeError(
                f"manifest compiled module mismatch for {module}: "
                f"{raw_module.get('compiledModule')!r} != {compiled!r}"
            )
        expected_module_hash = sha256(module.encode("utf-8"))
        if raw_module.get("moduleHash") != expected_module_hash:
            raise RuntimeError(f"manifest module hash mismatch for {module}")
        source_path = (MATHLIB / Path(*module.split("/"))).resolve()
        try:
            source_path.relative_to(MATHLIB.resolve())
        except ValueError as error:
            raise RuntimeError(
                f"manifest Mathlib source escapes the pinned package: {module}"
            ) from error
        if not source_path.is_file():
            raise RuntimeError(f"manifest Mathlib source is missing: {source_path}")
        source = source_path.read_bytes()
        expected_source_hash = _require_string(
            raw_module.get("sourceHash"), f"manifest sourceHash for {module}"
        )
        actual_source_hash = sha256(source)
        if actual_source_hash != expected_source_hash:
            raise RuntimeError(
                f"manifest source hash mismatch for {module}: "
                f"{actual_source_hash} != {expected_source_hash}"
            )
        occurrences = raw_module.get("occurrences")
        if not isinstance(occurrences, list):
            raise RuntimeError(f"manifest occurrences must be an array for {module}")
        all_occurrences += len(occurrences)
        checked_occurrences: list[dict[str, Any]] = []
        for occurrence in occurrences:
            checked = _validate_occurrence(module, source, occurrence)
            checked_occurrences.append(checked)
            occurrence_id = str(checked["id"])
            if occurrence_id in seen_occurrence_ids:
                raise RuntimeError(f"manifest contains duplicate occurrence ID: {occurrence_id}")
            seen_occurrence_ids.add(occurrence_id)
            actual_execution_roles[str(checked["executionRole"])] += 1
            actual_declaration_kinds[str(checked["declarationKind"])] += 1
            actual_actions[str(checked["action"])] += 1
        module_records[module] = (
            raw_module,
            source_path,
            source,
            tuple(checked_occurrences),
        )

    if all_occurrences != declared_total:
        raise RuntimeError(
            f"manifest occurrence records do not sum to occurrenceCount: "
            f"{all_occurrences} != {declared_total}"
        )
    if dict(sorted(actual_execution_roles.items())) != dict(
        sorted(declared_execution_roles.items())
    ):
        raise RuntimeError(
            f"manifest execution-role counts disagree with occurrence records: "
            f"{dict(actual_execution_roles)} != {declared_execution_roles}"
        )
    if dict(sorted(actual_declaration_kinds.items())) != dict(
        sorted(declared_declaration_kinds.items())
    ):
        raise RuntimeError(
            f"manifest declaration-kind counts disagree with occurrence records: "
            f"{dict(actual_declaration_kinds)} != {declared_declaration_kinds}"
        )
    if dict(sorted(actual_actions.items())) != dict(
        sorted(declared_actions.items())
    ):
        raise RuntimeError(
            f"manifest action counts disagree with occurrence records: "
            f"{dict(actual_actions)} != {declared_actions}"
        )

    if len(selected_names) != len(set(selected_names)):
        raise RuntimeError(f"selected modules must be unique: {selected_names}")
    if not selected_names:
        raise RuntimeError("at least one --module is required")
    if expect_total is not None or expect_materialize is not None:
        if len(selected_names) != 1:
            raise RuntimeError(
                "--expect-total/--expect-materialize are only valid for one selected module"
            )

    selected_set = set(selected_names)
    if len(selected_set) != len(selected_names):
        raise RuntimeError("selected modules must be unique")
    unknown_selected = selected_set - set(module_records)
    if unknown_selected:
        raise RuntimeError(
            "selected module does not occur exactly once in manifest: "
            f"{sorted(unknown_selected)}"
        )
    manifest_module_order = [
        str(raw_module["module"])
        for raw_module in modules
        if isinstance(raw_module, dict) and str(raw_module.get("module")) in selected_set
    ]
    result: list[SelectedModule] = []
    for module in manifest_module_order:
        validated = module_records.get(module)
        if validated is None:
            raise RuntimeError(
                f"selected module does not occur exactly once in manifest: {module}"
            )
        _record, source_path, source, checked_occurrence_tuple = validated
        checked_occurrences = list(checked_occurrence_tuple)
        replacement_plan(source, checked_occurrences, module)
        reusable = [
            occurrence
            for occurrence in checked_occurrences
            if occurrence["executionRole"] == "reusable_executable"
        ]
        if reusable:
            ids = [str(occurrence["id"]) for occurrence in reusable]
            raise RuntimeError(
                f"selected module contains reusable_executable, which this "
                f"runner does not support: {module}: {ids}"
            )
        materialize = tuple(
            occurrence
            for occurrence in checked_occurrences
            if occurrence["action"] == "materialize"
        )
        retain = tuple(
            occurrence
            for occurrence in checked_occurrences
            if occurrence["action"] == "retain"
        )
        unresolved = tuple(
            occurrence
            for occurrence in checked_occurrences
            if occurrence["action"] == "unresolved"
        )
        if unresolved:
            ids = [str(occurrence["id"]) for occurrence in unresolved]
            raise RuntimeError(
                f"selected module contains unresolved occurrences: {module}: {ids}"
            )
        if not materialize:
            raise RuntimeError(
                f"selected module has no materialize occurrences: {module}"
            )
        if expect_total is not None and expect_total != len(checked_occurrences):
            raise RuntimeError(
                f"--expect-total mismatch for {module}: expected {expect_total}, "
                f"found {len(checked_occurrences)}"
            )
        if expect_materialize is not None and expect_materialize != len(materialize):
            raise RuntimeError(
                f"--expect-materialize mismatch for {module}: expected {expect_materialize}, "
                f"found {len(materialize)}"
            )
        result.append(
            SelectedModule(
                module=module,
                compiled_module=corpus.compiled_module_name(module),
                source_path=source_path,
                source=source,
                occurrences=tuple(checked_occurrences),
                materialize=materialize,
                retain=retain,
            )
        )
    return result


def verify_selected_classifications(
    selected: list[SelectedModule], timeout: int
) -> None:
    """Recompute selected source inventory and scope metadata from pinned inputs.

    A manifest is an immutable selection, not authority for semantic metadata:
    every source identity and execution-role/declaration-kind/action triple is
    reproduced with the same inventory, scope, and execution-evidence helpers
    used by the corpus builder before any materialization is attempted.
    """
    paths = [item.source_path for item in selected]
    by_module, _fallbacks = corpus.inventory_paths(
        paths, batch_size=max(1, len(paths)), timeout=timeout
    )
    inventories: dict[str, list[dict[str, Any]]] = {}
    specs: list[scope.ModuleSpec] = []
    for item in selected:
        entries, _nested, _duplicates = corpus.validate_module_inventory(
            item.module, item.source, by_module.get(item.module, [])
        )
        inventories[item.module] = entries
        specs.append(
            scope.ModuleSpec(
                item.compiled_module,
                item.source_path,
                len(entries),
            )
        )
    occurrences_by_module, declarations_by_module, _scope_fallbacks = (
        scope.load_records_with_fallbacks(
            specs, batch_size=max(1, len(specs)), timeout=timeout
        )
    )
    identity_fields = (
        "id",
        "kind",
        "source",
        "startByte",
        "endByte",
        "syntaxKind",
        "executionRole",
        "declarationKind",
        "action",
    )
    for item in selected:
        entries = inventories[item.module]
        classified, _duplicate_scope_records = corpus.join_scope_records(
            item.module,
            entries,
            occurrences_by_module.get(item.compiled_module, []),
            declarations_by_module.get(item.compiled_module, []),
        )
        unresolved = [entry for entry in classified if entry["action"] == "unresolved"]
        if unresolved:
            unresolved_ids = {str(entry["id"]) for entry in unresolved}
            scope.apply_execution_evidence(
                item.compiled_module,
                item.source,
                unresolved,
                entries=[entry for entry in entries if str(entry["id"]) in unresolved_ids],
                timeout=timeout,
            )
        if len(classified) != len(item.occurrences):
            raise RuntimeError(
                f"selected source inventory changed for {item.module}: "
                f"{len(classified)} != {len(item.occurrences)}"
            )
        for index, (recorded, recomputed) in enumerate(
            zip(item.occurrences, classified)
        ):
            for field in identity_fields:
                if recorded.get(field) != recomputed.get(field):
                    raise RuntimeError(
                        f"selected manifest classification mismatch for {item.module} "
                        f"occurrence[{index}].{field}: recorded "
                        f"{recorded.get(field)!r}, recomputed {recomputed.get(field)!r}"
                    )


def _sanitize_stem(value: str) -> str:
    result = re.sub(r"[^A-Za-z0-9._-]+", "-", value).strip(".-")
    return result or "shard"


def debug_root_for(output: Path) -> Path:
    base = BOUNDARY_DEBUG_ROOT.resolve()
    try:
        relative = output.resolve().relative_to(base)
    except ValueError as error:
        raise RuntimeError(f"debug output escapes boundary root: {output}") from error
    if not relative.parts:
        raise RuntimeError(f"debug output cannot be the boundary root: {output}")
    return output.resolve().parent / (_sanitize_stem(output.stem) + "-run")


def clear_debug_root(path: Path) -> None:
    """Clear only the validated run subtree, never the shared debug root."""
    base = BOUNDARY_DEBUG_ROOT.resolve()
    # Resolve the parent but not the leaf: if a stale run root is a symlink,
    # unlink that exact symlink instead of following it and deleting its target.
    resolved = path.parent.resolve() / path.name
    try:
        relative = resolved.relative_to(base)
    except ValueError as error:
        raise RuntimeError(f"debug run subtree escapes boundary root: {path}") from error
    if not relative.parts or resolved == base:
        raise RuntimeError("refusing to clear the shared boundary debug root")
    if resolved.is_symlink() or (resolved.exists() and not resolved.is_dir()):
        resolved.unlink()
    elif resolved.exists():
        shutil.rmtree(resolved)
    resolved.mkdir(parents=True, exist_ok=True)


def _copy_at_module_root(root: Path, module: str, source: bytes) -> Path:
    destination = root / Path(*module.split("/"))
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _injected_import(imported: str) -> bytes:
    return f"import {imported}\n".encode("utf-8")


def _inject_import(source: bytes, imported: str) -> bytes:
    """Append an import after the original header imports.

    This preserves `prelude` placement and the authored import order.  Importing
    immediately after the `module` token is not valid for prelude modules.
    """
    injected = _injected_import(imported)
    if source.count(injected):
        raise RuntimeError(f"source already imports generated dependency: {imported}")
    import_offset, _body_offset = scope._header_offsets(source)
    return source[:import_offset] + injected + source[import_offset:]


def _assert_context_gaps(
    original: bytes,
    generated: bytes,
    entries: Iterable[dict[str, Any]],
    *,
    imported: str,
    label: str,
    expected_without_import: bytes,
    replacement_lengths: list[int] | None = None,
) -> None:
    assert_exact_source_preservation(
        original,
        generated,
        entries,
        imported=imported,
        label=label,
        expected_without_import=expected_without_import,
        replacement_lengths=replacement_lengths,
    )


def instrumented_source(
    source: bytes, materialize: list[dict[str, Any]]
) -> bytes:
    rewritten = inventory.rewrite_simp_heads(
        source,
        materialize,
        lambda entry: f'simp_engine_boundary_record "{entry["id"]}"',
    )
    return _inject_import(rewritten, "ExplicitLean.SimpEngine.Boundary")


def _canonical_json_line(value: object) -> str:
    return json.dumps(
        value, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    )


def _write_jsonl(path: Path, values: list[object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(_canonical_json_line(value) + "\n" for value in values),
        encoding="utf-8",
    )


def _compile_copy(
    path: Path,
    dylib: str,
    timeout: int,
    *,
    env: dict[str, str] | None = None,
) -> tuple[int, str, float]:
    command = inventory.lean_command(path)
    command.insert(3, f"--load-dynlib={dylib}")
    return _run_command(command, timeout, env=env)


DECLARATION_ORACLE_COUNT_FIELDS = {
    "stockDeclarationCount",
    "appliedDeclarationCount",
    "commonPublicDeclarationCount",
    "stockOnlyPrivateProofCount",
    "appliedOnlyPrivateProofCount",
    "stockExtensionCount",
    "appliedExtensionCount",
    "checkedDeclarationCount",
}
DECLARATION_ORACLE_FIELDS = DECLARATION_ORACLE_COUNT_FIELDS | {
    "kind",
    "schema",
    "module",
    "status",
    "failureCategory",
    "failureDetail",
}


def _parse_declaration_oracle(
    output: str, expected_module: str
) -> dict[str, Any]:
    markers = [
        line.split(DECLARATION_ORACLE_MARKER, 1)[1].strip()
        for line in output.splitlines()
        if line.startswith(DECLARATION_ORACLE_MARKER)
    ]
    if len(markers) != 1:
        raise RuntimeError(
            "declaration oracle must emit exactly one canonical marker; "
            f"found {len(markers)}"
        )
    try:
        report = json.loads(markers[0])
    except json.JSONDecodeError as error:
        raise RuntimeError("declaration oracle marker is not valid JSON") from error
    if not isinstance(report, dict):
        raise RuntimeError("declaration oracle marker payload must be an object")
    if set(report) != DECLARATION_ORACLE_FIELDS:
        raise RuntimeError(
            "declaration oracle marker has unexpected fields: "
            f"{sorted(report)}"
        )
    if report.get("kind") != DECLARATION_ORACLE_KIND:
        raise RuntimeError(
            f"declaration oracle marker has unexpected kind: {report.get('kind')!r}"
        )
    schema = report.get("schema")
    if (
        isinstance(schema, bool)
        or not isinstance(schema, int)
        or schema != DECLARATION_ORACLE_SCHEMA
    ):
        raise RuntimeError(
            f"declaration oracle marker has unexpected schema: {schema!r}"
        )
    if report.get("module") != expected_module:
        raise RuntimeError(
            "declaration oracle marker has unexpected module: "
            f"{report.get('module')!r}"
        )
    for field in DECLARATION_ORACLE_COUNT_FIELDS:
        value = report[field]
        if isinstance(value, bool) or not isinstance(value, int) or value < 0:
            raise RuntimeError(
                f"declaration oracle marker has invalid {field}: {value!r}"
            )
    if report.get("status") not in {"success", "failure"}:
        raise RuntimeError(
            f"declaration oracle marker has unexpected status: {report.get('status')!r}"
        )
    category = report.get("failureCategory")
    detail = report.get("failureDetail")
    if report["status"] == "success":
        if category is not None or detail is not None:
            raise RuntimeError("successful declaration oracle report has failure details")
        checked = report["checkedDeclarationCount"]
        if checked + report["stockOnlyPrivateProofCount"] != report[
            "stockDeclarationCount"
        ]:
            raise RuntimeError(
                "successful declaration oracle report has inconsistent stock counts"
            )
        if checked + report["appliedOnlyPrivateProofCount"] != report[
            "appliedDeclarationCount"
        ]:
            raise RuntimeError(
                "successful declaration oracle report has inconsistent applied counts"
            )
        if report["commonPublicDeclarationCount"] > checked:
            raise RuntimeError(
                "successful declaration oracle report has inconsistent public count"
            )
    else:
        if not isinstance(category, str) or not category:
            raise RuntimeError("failed declaration oracle report has no failure category")
        if not isinstance(detail, str) or not detail:
            raise RuntimeError("failed declaration oracle report has no failure detail")
        if any(report[field] != 0 for field in DECLARATION_ORACLE_COUNT_FIELDS):
            raise RuntimeError("failed declaration oracle report has nonzero counts")
    return report


def run_declaration_oracle(
    module: str,
    original_path: Path,
    materialized_path: Path,
    module_root: Path,
    dylib: str,
    timeout: int,
) -> dict[str, Any]:
    compiled_module = corpus.compiled_module_name(module)
    log_path = module_root / "declaration-oracle.log"
    report_path = module_root / "declaration-oracle-report.json"
    # A failed rerun must not leave a previous successful oracle report.
    report_path.unlink(missing_ok=True)
    command = [
        sys.executable,
        str(ROOT / "Experiment" / "lean_toolchain_cache.py"),
        "oracle",
        compiled_module,
        str(original_path),
        str(materialized_path),
    ]
    environment, nonce = replay_subprocess_environment()
    code, output, elapsed = _run_command(command, timeout, env=environment)
    _write_text(log_path, output)
    try:
        replay_guard = replay_guard_evidence(output, nonce, log_path, compiled_module)
        oracle_report = _parse_declaration_oracle(output, compiled_module)
    except RuntimeError as error:
        raise RuntimeError(
            f"declaration oracle protocol failed for {module}: {error}; "
            f"see {log_path}"
        ) from error
    _atomic_write_json(report_path, oracle_report)
    if code != 0 or oracle_report["status"] != "success":
        category = oracle_report.get("failureCategory")
        detail = oracle_report.get("failureDetail")
        raise RuntimeError(
            f"declaration oracle failed for {module}: "
            f"{category}: {detail}; see {log_path}"
        )
    return {
        "path": str(log_path.resolve()),
        "reportPath": str(report_path.resolve()),
        "sha256": sha256(log_path.read_bytes()),
        "reportSha256": sha256(report_path.read_bytes()),
        "compileSuccess": True,
        "seconds": elapsed,
        "status": oracle_report["status"],
        "report": oracle_report,
        "replayGuard": replay_guard,
    }


def replay_guard_evidence(
    output: str, nonce: str, log_path: Path, module: str
) -> dict[str, Any]:
    """Scan the complete subprocess output before publishing its guard evidence."""
    check_replay_abort_markers(output, expected_nonce=nonce, expected_module=module)
    log_bytes = log_path.read_bytes()
    if log_bytes.decode("utf-8") != output:
        raise RuntimeError("replay guard log differs from scanned process output")
    evidence = {
        "kind": REPLAY_GUARD_KIND,
        "schema": REPLAY_GUARD_SCHEMA,
        "nonce": nonce,
        "path": str(log_path.resolve()),
        "sha256": sha256(log_bytes),
    }
    _validate_replay_guard(evidence, "replay guard")
    return evidence


def _query_dynamic_library(timeout: int, debug_root: Path) -> str:
    build_code, build_output, _build_elapsed = _run_command(
        ["lake", "build", "ExplicitLean:shared"], timeout
    )
    _write_text(debug_root / "explicitlean-build.log", build_output)
    if build_code != 0:
        raise RuntimeError(f"lake build ExplicitLean:shared failed (exit {build_code})")
    query_code, query_output, _query_elapsed = _run_command(
        ["lake", "query", "ExplicitLean:shared", "--json"], timeout
    )
    _write_text(debug_root / "explicitlean-query.log", query_output)
    if query_code != 0:
        raise RuntimeError(f"lake query ExplicitLean:shared failed (exit {query_code})")
    lines = [line.strip() for line in query_output.splitlines() if line.strip()]
    if not lines:
        raise RuntimeError("lake query ExplicitLean:shared returned no JSON result")
    try:
        value = json.loads(lines[-1])
    except json.JSONDecodeError as error:
        raise RuntimeError(
            f"lake query ExplicitLean:shared returned invalid JSON: {lines[-1]!r}"
        ) from error
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"lake query ExplicitLean:shared returned invalid path: {value!r}")
    return value


def _module_result(
    selected: SelectedModule,
    debug_root: Path,
    dylib: str,
    timeout: int,
) -> dict[str, Any]:
    module_slug = _sanitize_stem(selected.module.removeprefix("Mathlib/").removesuffix(".lean"))
    module_root = debug_root / module_slug
    original_path = _copy_at_module_root(module_root / "original", selected.module, selected.source)
    roots = selected.replacement_roots
    covered_by = selected.covered_by
    instrumented = instrumented_source(selected.source, roots)
    instrumented_path = _copy_at_module_root(module_root / "instrumented", selected.module, instrumented)
    _assert_context_gaps(
        selected.source,
        instrumented,
        selected.materialize,
        imported="ExplicitLean.SimpEngine.Boundary",
        label=f"instrumented source {selected.module}",
        expected_without_import=inventory.rewrite_simp_heads(
            selected.source,
            roots,
            lambda entry: f'simp_engine_boundary_record "{entry["id"]}"',
        ),
    )

    recording_environment, recording_nonce = recording_subprocess_environment()
    instrumented_code, instrumented_output, instrumented_elapsed = _compile_copy(
        instrumented_path, dylib, timeout, env=recording_environment
    )
    _write_text(module_root / "instrumented.log", instrumented_output)
    check_recording_abort_markers(
        instrumented_output,
        expected_nonce=recording_nonce,
        expected_module=selected.compiled_module,
    )
    if instrumented_code != 0:
        raise RuntimeError(
            f"instrumented module compilation failed for {selected.module} "
            f"(exit {instrumented_code}); see {module_root / 'instrumented.log'}"
        )
    report_list = parse_framed_json_lines(
        instrumented_output,
        marker=ARTIFACT_MARKER,
        expected_nonce=recording_nonce,
        label=f"boundary artifact for {selected.module}",
    )
    for report in report_list:
        reject_forbidden_generated_text(report, f"artifact report for {selected.module}")
    materialize_ids = [str(entry["id"]) for entry in selected.materialize]
    expected_ids = [str(entry["id"]) for entry in roots]
    observed_ids = {
        str(report["occurrence"])
        for report in report_list
        if isinstance(report, dict) and isinstance(report.get("occurrence"), str)
    }
    unobserved_ids = set(expected_ids) - observed_ids
    try:
        report_variants = group_report_variants(
            report_list,
            expected_ids,
            expected_module=selected.compiled_module,
            unobserved_ids=unobserved_ids,
        )
    except RuntimeError as error:
        raise RuntimeError(
            f"{error}; generated source: {instrumented_path}; "
            f"see {module_root / 'instrumented.log'}"
        ) from error
    reports_path = module_root / "artifact-reports.jsonl"
    _write_jsonl(reports_path, report_list)

    execution_counts: Counter[str] = Counter(
        str(report["occurrence"])
        for report in report_list
        if isinstance(report, dict)
    )
    occurrence_ids = [str(entry["id"]) for entry in selected.occurrences]
    occurrence_actions = [str(entry["action"]) for entry in selected.occurrences]
    occurrence_results = [
        make_occurrence_result(
            occurrence_id,
            action,
            execution_counts.get(occurrence_id, 0),
            report_variants.get(occurrence_id, []),
            covered_by=covered_by.get(occurrence_id),
        )
        for occurrence_id, action in zip(occurrence_ids, occurrence_actions)
    ]
    occurrence_counts = validate_occurrence_summary(
        occurrence_results,
        occurrence_ids,
        occurrence_actions,
        occurrence_classification_counts(occurrence_results),
    )

    materialized = replace_all_occurrences(
        selected.source,
        list(selected.materialize),
        report_variants,
    )
    materialized = _inject_import(
        materialized, "ExplicitLean.SimpEngine.Boundary.Tactic"
    )
    materialized_path = _copy_at_module_root(
        module_root / "materialized", selected.module, materialized
    )
    _assert_context_gaps(
        selected.source,
        materialized,
        selected.materialize,
        imported="ExplicitLean.SimpEngine.Boundary.Tactic",
        label=f"materialized source {selected.module}",
        expected_without_import=replace_all_occurrences(
            selected.source,
            list(selected.materialize),
            report_variants,
        ),
        replacement_lengths=materialization_replacement_lengths(
            selected.source, list(selected.materialize), report_variants,
        ),
    )
    replay_environment, replay_nonce = replay_subprocess_environment()
    materialized_code, materialized_output, materialized_elapsed = _compile_copy(
        materialized_path, dylib, timeout, env=replay_environment
    )
    materialized_log = module_root / "materialized.log"
    _write_text(materialized_log, materialized_output)
    replay_guard = replay_guard_evidence(
        materialized_output, replay_nonce, materialized_log, selected.compiled_module
    )
    if materialized_code != 0:
        raise RuntimeError(
            f"materialized module compilation failed for {selected.module} "
            f"(exit {materialized_code}); see {module_root / 'materialized.log'}"
        )
    declaration_oracle = run_declaration_oracle(
        selected.module,
        original_path,
        materialized_path,
        module_root,
        dylib,
        timeout,
    )
    remaining = [
        entry
        for entry in inventory.syntax_inventory_file(
            materialized_path,
            f"{selected.module}.materialized",
            timeout,
            allow_elaboration_errors=True,
            header_imports=True,
        )
        if entry["kind"] in inventory.SUPPORTED_KINDS
    ]
    expected_retained = Counter(
        (str(entry["kind"]), str(entry["source"])) for entry in selected.retain
    )
    actual_remaining = Counter(
        (str(entry["kind"]), str(entry["source"])) for entry in remaining
    )
    if actual_remaining != expected_retained:
        raise RuntimeError(
            f"materialized syntax inventory differs from manifest-retained inventory "
            f"in {selected.module}: expected {expected_retained}, found {actual_remaining}; "
            f"generated source: {materialized_path}"
        )

    variant_counts = {
        occurrence_id: len(report_variants.get(occurrence_id, []))
        for occurrence_id in materialize_ids
    }
    variant_status_counts: Counter[str] = Counter(
        str(report["status"])
        for variants in report_variants.values()
        for report in variants
    )
    execution_status_counts: Counter[str] = Counter(
        str(report.get("status"))
        for report in report_list
        if isinstance(report, dict)
    )
    original_hash = sha256(selected.source)
    instrumented_hash = sha256(instrumented)
    materialized_hash = sha256(materialized)
    report_hash = sha256(reports_path.read_bytes())
    observed_ordered = [occurrence_id for occurrence_id in expected_ids if occurrence_id in observed_ids]
    unobserved_ordered = [occurrence_id for occurrence_id in expected_ids if occurrence_id in unobserved_ids]
    exact_preservation = {
        "verified": True,
        "materializeRangesReplaced": True,
        "outsideMaterializeRanges": "byte-identical",
        "authoredBindersPreserved": True,
        "alphaRenaming": False,
        "statement": (
            "All authored source bytes outside whole materialize tactic ranges are "
            "byte-identical; only the selected ranges and the Boundary import "
            "are generated, with authored binders and surrounding source preserved."
        ),
    }
    return {
        "module": selected.module,
        "compiledModule": selected.compiled_module,
        "sourcePath": str(selected.source_path),
        "originalPath": str(original_path.resolve()),
        "instrumentedPath": str(instrumented_path.resolve()),
        "materializedPath": str(materialized_path.resolve()),
        "reportPath": str(reports_path.resolve()),
        "originalHash": original_hash,
        "instrumentedHash": instrumented_hash,
        "materializedHash": materialized_hash,
        "reportHash": report_hash,
        "original": {"path": str(original_path.resolve()), "sha256": original_hash},
        "instrumented": {
            "path": str(instrumented_path.resolve()),
            "sha256": instrumented_hash,
            "compileSuccess": True,
            "seconds": instrumented_elapsed,
        },
        "materialized": {
            "path": str(materialized_path.resolve()),
            "sha256": materialized_hash,
            "compileSuccess": True,
            "seconds": materialized_elapsed,
        },
        "artifactReport": {
            "path": str(reports_path.resolve()),
            "sha256": report_hash,
        },
        "declarationOracle": declaration_oracle,
        "replayGuard": replay_guard,
        "totalCount": len(selected.occurrences),
        "materializeCount": len(selected.materialize),
        "retainCount": len(selected.retain),
        "occurrenceResults": occurrence_results,
        "occurrenceClassificationCounts": occurrence_counts,
        "materializeIds": materialize_ids,
        "replacementRootIds": expected_ids,
        "retainIds": [str(entry["id"]) for entry in selected.retain],
        "observedIds": observed_ordered,
        "unobservedIds": unobserved_ordered,
        "executionReportCount": len(report_list),
        "variantCount": sum(variant_counts.values()),
        "variantCounts": variant_counts,
        "executionStatusCounts": dict(sorted(execution_status_counts.items())),
        "variantStatusCounts": dict(sorted(variant_status_counts.items())),
        "remainingRetainedCount": len(remaining),
        "remainingRetainedMultiset": {
            f"{kind}\u0000{source}": count
            for (kind, source), count in sorted(actual_remaining.items())
        },
        "exactSourcePreservation": exact_preservation,
        "compileSuccess": True,
    }


def _atomic_write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    temporary = path.with_name(path.name + ".tmp")
    try:
        temporary.write_text(encoded, encoding="utf-8")
        temporary.replace(path)
    except Exception:
        temporary.unlink(missing_ok=True)
        raise


SHARD_REPORT_FIELDS = frozenset(
    {
        "kind",
        "reportSchema",
        "reportIdentity",
        "artifactProtocol",
        "manifestPath",
        "manifestHash",
        "manifest",
        "manifestPolicy",
        "provenance",
        "repositoryCommit",
        "mathlibCommit",
        "lean",
        "runnerPath",
        "runnerHash",
        "runner",
        "selectedModules",
        "modules",
        "totalCount",
        "materializeCount",
        "retainCount",
        "occurrenceResults",
        "occurrenceClassificationCounts",
        "observedIds",
        "unobservedIds",
        "executionReportCount",
        "variantCount",
        "executionStatusCounts",
        "variantStatusCounts",
        "remainingRetainedCount",
        "exactSourcePreservation",
        "compileSuccess",
        "aggregate",
    }
)
MODULE_REPORT_FIELDS = frozenset(
    {
        "module",
        "compiledModule",
        "sourcePath",
        "originalPath",
        "instrumentedPath",
        "materializedPath",
        "reportPath",
        "originalHash",
        "instrumentedHash",
        "materializedHash",
        "reportHash",
        "original",
        "instrumented",
        "materialized",
        "artifactReport",
        "declarationOracle",
        "replayGuard",
        "totalCount",
        "materializeCount",
        "retainCount",
        "occurrenceResults",
        "occurrenceClassificationCounts",
        "materializeIds",
        "replacementRootIds",
        "retainIds",
        "observedIds",
        "unobservedIds",
        "executionReportCount",
        "variantCount",
        "variantCounts",
        "executionStatusCounts",
        "variantStatusCounts",
        "remainingRetainedCount",
        "remainingRetainedMultiset",
        "exactSourcePreservation",
        "compileSuccess",
    }
)
AGGREGATE_FIELDS = frozenset(
    {
        "selectedModuleCount",
        "totalCount",
        "materializeCount",
        "retainCount",
        "occurrenceClassificationCounts",
        "observedCount",
        "unobservedCount",
        "executionReportCount",
        "variantCount",
        "remainingRetainedCount",
    }
)
PATH_HASH_FIELDS = frozenset({"path", "sha256"})
COMPILED_ARTIFACT_FIELDS = frozenset({"path", "sha256", "compileSuccess", "seconds"})
SOURCE_PRESERVATION_TOP_FIELDS = frozenset(
    {"verified", "alphaRenaming", "statement"}
)
SOURCE_PRESERVATION_MODULE_FIELDS = frozenset(
    {
        "verified",
        "materializeRangesReplaced",
        "outsideMaterializeRanges",
        "authoredBindersPreserved",
        "alphaRenaming",
        "statement",
    }
)
PROVENANCE_FIELDS = frozenset(
    {
        "repositoryCommit",
        "mathlibCommit",
        "lean",
        "manifestRepositoryCommit",
        "manifestMathlibCommit",
    }
)
MANIFEST_POLICY_FIELDS = frozenset({"allowDirty", "allowUnresolved"})
ORACLE_WRAPPER_FIELDS = frozenset(
    {
        "path",
        "reportPath",
        "sha256",
        "reportSha256",
        "compileSuccess",
        "seconds",
        "status",
        "report",
        "replayGuard",
    }
)
REPLAY_GUARD_FIELDS = frozenset({"kind", "schema", "nonce", "path", "sha256"})


def _exact_fields(value: object, fields: frozenset[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != fields:
        found = (
            sorted(key for key in value if isinstance(key, str))
            if isinstance(value, dict)
            else value
        )
        raise RuntimeError(f"{label} fields changed: expected {sorted(fields)}, found {found}")
    return value


def _require_bool(value: object, label: str) -> bool:
    if not isinstance(value, bool):
        raise RuntimeError(f"{label} must be a boolean: {value!r}")
    return value


def _require_number(value: object, label: str) -> float | int:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise RuntimeError(f"{label} must be a number: {value!r}")
    if value < 0:
        raise RuntimeError(f"{label} must be nonnegative: {value!r}")
    return value


def _validate_string_list(
    value: object, label: str, *, unique: bool = True
) -> list[str]:
    if not isinstance(value, list):
        raise RuntimeError(f"{label} must be an array: {value!r}")
    result: list[str] = []
    for index, item in enumerate(value):
        result.append(_require_string(item, f"{label}[{index}]"))
    if unique and len(set(result)) != len(result):
        raise RuntimeError(f"{label} contains duplicate IDs: {result!r}")
    return result


def _validate_count_map(
    value: object, label: str, allowed: set[str] | frozenset[str] | None = None
) -> dict[str, int]:
    if not isinstance(value, dict):
        raise RuntimeError(f"{label} must be an object: {value!r}")
    result: dict[str, int] = {}
    for key, raw_count in value.items():
        if not isinstance(key, str) or (allowed is not None and key not in allowed):
            raise RuntimeError(f"{label} has an unknown key: {key!r}")
        result[key] = _require_int(raw_count, f"{label}.{key}", nonnegative=True)
    return result


def _validate_hash_ref(value: object, label: str) -> dict[str, Any]:
    result = _exact_fields(value, PATH_HASH_FIELDS, label)
    _require_string(result["path"], f"{label}.path")
    _require_string(result["sha256"], f"{label}.sha256")
    return result


def _validate_compiled_artifact(value: object, label: str) -> dict[str, Any]:
    result = _exact_fields(value, COMPILED_ARTIFACT_FIELDS, label)
    _require_string(result["path"], f"{label}.path")
    _require_string(result["sha256"], f"{label}.sha256")
    if not _require_bool(result["compileSuccess"], f"{label}.compileSuccess"):
        raise RuntimeError(f"{label}.compileSuccess must be true")
    _require_number(result["seconds"], f"{label}.seconds")
    return result


def _validate_replay_guard(value: object, label: str) -> dict[str, Any]:
    result = _exact_fields(value, REPLAY_GUARD_FIELDS, label)
    if result["kind"] != REPLAY_GUARD_KIND or _require_int(
        result["schema"], f"{label}.schema"
    ) != REPLAY_GUARD_SCHEMA:
        raise RuntimeError(f"{label} protocol identity mismatch")
    nonce = _require_string(result["nonce"], f"{label}.nonce")
    if re.fullmatch(r"[A-Za-z0-9_-]{43}", nonce) is None:
        raise RuntimeError(f"{label}.nonce is not a production compiler nonce")
    _require_string(result["path"], f"{label}.path")
    _require_string(result["sha256"], f"{label}.sha256")
    return result


def _validate_source_preservation(
    value: object, label: str, *, module: bool
) -> dict[str, Any]:
    fields = SOURCE_PRESERVATION_MODULE_FIELDS if module else SOURCE_PRESERVATION_TOP_FIELDS
    result = _exact_fields(value, fields, label)
    if not _require_bool(result["verified"], f"{label}.verified"):
        raise RuntimeError(f"{label}.verified must be true")
    if _require_bool(result["alphaRenaming"], f"{label}.alphaRenaming") is not False:
        raise RuntimeError(f"{label}.alphaRenaming must be false")
    _require_string(result["statement"], f"{label}.statement")
    if module:
        if not _require_bool(
            result["materializeRangesReplaced"], f"{label}.materializeRangesReplaced"
        ):
            raise RuntimeError(f"{label}.materializeRangesReplaced must be true")
        if result["outsideMaterializeRanges"] != "byte-identical":
            raise RuntimeError(
                f"{label}.outsideMaterializeRanges must be byte-identical"
            )
        if not _require_bool(
            result["authoredBindersPreserved"], f"{label}.authoredBindersPreserved"
        ):
            raise RuntimeError(f"{label}.authoredBindersPreserved must be true")
    return result


def _validate_oracle_wrapper(
    value: object, label: str, expected_module: str
) -> dict[str, Any]:
    result = _exact_fields(value, ORACLE_WRAPPER_FIELDS, label)
    for field in ("path", "reportPath", "sha256", "reportSha256"):
        _require_string(result[field], f"{label}.{field}")
    if not _require_bool(result["compileSuccess"], f"{label}.compileSuccess"):
        raise RuntimeError(f"{label}.compileSuccess must be true")
    _require_number(result["seconds"], f"{label}.seconds")
    if result["status"] != "success":
        raise RuntimeError(f"{label}.status must be success")
    oracle = result["report"]
    if not isinstance(oracle, dict):
        raise RuntimeError(f"{label}.report must be an object")
    parsed = _parse_declaration_oracle(
        DECLARATION_ORACLE_MARKER + json.dumps(oracle), expected_module
    )
    if parsed != oracle:
        raise RuntimeError(f"{label}.report changed during validation")
    guard = _validate_replay_guard(result["replayGuard"], f"{label}.replayGuard")
    if guard["path"] != result["path"] or guard["sha256"] != result["sha256"]:
        raise RuntimeError(f"{label}.replayGuard log reference disagrees")
    return result


def _validate_status_map(value: object, label: str) -> dict[str, int]:
    return _validate_count_map(value, label, {"success", "failure"})


def _validate_module_report(value: object, index: int) -> dict[str, Any]:
    label = f"modules[{index}]"
    module = _exact_fields(value, MODULE_REPORT_FIELDS, label)
    module_name = _require_string(module["module"], f"{label}.module")
    if not module_name.startswith("Mathlib/") or not module_name.endswith(".lean"):
        raise RuntimeError(f"{label}.module is not a Mathlib .lean path: {module_name!r}")
    expected_compiled = corpus.compiled_module_name(module_name)
    if module["compiledModule"] != expected_compiled:
        raise RuntimeError(
            f"{label}.compiledModule mismatch: {module['compiledModule']!r} != "
            f"{expected_compiled!r}"
        )
    for field in (
        "sourcePath",
        "originalPath",
        "instrumentedPath",
        "materializedPath",
        "reportPath",
        "originalHash",
        "instrumentedHash",
        "materializedHash",
        "reportHash",
    ):
        _require_string(module[field], f"{label}.{field}")
    original = _validate_hash_ref(module["original"], f"{label}.original")
    if module["originalPath"] != original["path"] or module["originalHash"] != original["sha256"]:
        raise RuntimeError(f"{label}.original duplicate fields disagree")
    instrumented = _validate_compiled_artifact(
        module["instrumented"], f"{label}.instrumented"
    )
    if (
        module["instrumentedPath"] != instrumented["path"]
        or module["instrumentedHash"] != instrumented["sha256"]
    ):
        raise RuntimeError(f"{label}.instrumented duplicate fields disagree")
    materialized = _validate_compiled_artifact(
        module["materialized"], f"{label}.materialized"
    )
    if (
        module["materializedPath"] != materialized["path"]
        or module["materializedHash"] != materialized["sha256"]
    ):
        raise RuntimeError(f"{label}.materialized duplicate fields disagree")
    artifact = _validate_hash_ref(module["artifactReport"], f"{label}.artifactReport")
    if module["reportPath"] != artifact["path"] or module["reportHash"] != artifact["sha256"]:
        raise RuntimeError(f"{label}.artifactReport duplicate fields disagree")
    _validate_oracle_wrapper(
        module["declarationOracle"], f"{label}.declarationOracle", expected_compiled
    )
    guard = _validate_replay_guard(module["replayGuard"], f"{label}.replayGuard")
    if guard["nonce"] == module["declarationOracle"]["replayGuard"]["nonce"]:
        raise RuntimeError(f"{label} reused a compiler nonce for the oracle process")
    _validate_source_preservation(
        module["exactSourcePreservation"], f"{label}.exactSourcePreservation", module=True
    )
    if not _require_bool(module["compileSuccess"], f"{label}.compileSuccess"):
        raise RuntimeError(f"{label}.compileSuccess must be true")

    total_count = _require_int(module["totalCount"], f"{label}.totalCount", nonnegative=True)
    materialize_count = _require_int(
        module["materializeCount"], f"{label}.materializeCount", nonnegative=True
    )
    retain_count = _require_int(module["retainCount"], f"{label}.retainCount", nonnegative=True)
    materialize_ids = _validate_string_list(module["materializeIds"], f"{label}.materializeIds")
    retain_ids = _validate_string_list(module["retainIds"], f"{label}.retainIds")
    if set(materialize_ids) & set(retain_ids):
        raise RuntimeError(f"{label} materialize and retain IDs overlap")
    if materialize_count != len(materialize_ids) or retain_count != len(retain_ids):
        raise RuntimeError(f"{label} action counts disagree with action IDs")
    occurrence_results = module["occurrenceResults"]
    result_ids = []
    result_actions = []
    if not isinstance(occurrence_results, list):
        raise RuntimeError(f"{label}.occurrenceResults must be an array")
    for raw in occurrence_results:
        if not isinstance(raw, dict):
            raise RuntimeError(f"{label}.occurrenceResults contains a non-object")
        result_ids.append(_require_string(raw.get("occurrence"), "occurrence result ID"))
        result_actions.append(raw.get("action"))
    if any(action not in {"materialize", "retain"} for action in result_actions):
        raise RuntimeError(f"{label}.occurrenceResults contains an invalid action")
    if len(result_ids) != len(set(result_ids)):
        raise RuntimeError(f"{label}.occurrenceResults contains duplicate IDs")
    if set(result_ids) != set(materialize_ids) | set(retain_ids):
        raise RuntimeError(f"{label}.occurrenceResults IDs disagree with action IDs")
    if [id for id, action in zip(result_ids, result_actions) if action == "materialize"] != materialize_ids:
        raise RuntimeError(f"{label}.materializeIds order disagrees with occurrenceResults")
    if [id for id, action in zip(result_ids, result_actions) if action == "retain"] != retain_ids:
        raise RuntimeError(f"{label}.retainIds order disagrees with occurrenceResults")
    expected_actions = [str(action) for action in result_actions]
    occurrence_counts = validate_occurrence_summary(
        occurrence_results,
        result_ids,
        expected_actions,
        module["occurrenceClassificationCounts"],
    )
    if total_count != len(result_ids) or total_count != materialize_count + retain_count:
        raise RuntimeError(f"{label} total/action counts disagree")
    if module["occurrenceClassificationCounts"] != occurrence_counts:
        raise RuntimeError(f"{label} occurrence classification counts disagree")

    root_ids = _validate_string_list(module["replacementRootIds"], f"{label}.replacementRootIds")
    if root_ids != [
        raw["occurrence"] for raw in occurrence_results
        if raw["action"] == "materialize" and raw["coveredBy"] is None
    ]:
        raise RuntimeError(f"{label}.replacementRootIds disagree with occurrence coverage")

    observed_ids = _validate_string_list(module["observedIds"], f"{label}.observedIds")
    unobserved_ids = _validate_string_list(module["unobservedIds"], f"{label}.unobservedIds")
    if set(observed_ids) & set(unobserved_ids):
        raise RuntimeError(f"{label} observed/unobserved IDs overlap")
    if set(observed_ids) | set(unobserved_ids) != set(root_ids):
        raise RuntimeError(f"{label} observed/unobserved IDs do not partition replacement roots")
    by_id = {raw["occurrence"]: raw for raw in occurrence_results}
    if [id for id in materialize_ids if id in set(observed_ids)] != observed_ids:
        raise RuntimeError(f"{label}.observedIds order disagrees with materialize IDs")
    if [id for id in materialize_ids if id in set(unobserved_ids)] != unobserved_ids:
        raise RuntimeError(f"{label}.unobservedIds order disagrees with materialize IDs")
    for occurrence_id in root_ids:
        result = by_id[occurrence_id]
        if (result["executionCount"] == 0) != (occurrence_id in set(unobserved_ids)):
            raise RuntimeError(f"{label} observed status disagrees for {occurrence_id}")

    variant_counts = _validate_count_map(
        module["variantCounts"], f"{label}.variantCounts"
    )
    if set(variant_counts) != set(materialize_ids):
        raise RuntimeError(f"{label}.variantCounts IDs disagree with materialize IDs")
    for occurrence_id in materialize_ids:
        if variant_counts[occurrence_id] != by_id[occurrence_id]["variantCount"]:
            raise RuntimeError(f"{label}.variantCounts disagrees for {occurrence_id}")
    execution_report_count = _require_int(
        module["executionReportCount"], f"{label}.executionReportCount", nonnegative=True
    )
    calculated_execution_count = sum(int(raw["executionCount"]) for raw in occurrence_results)
    if execution_report_count != calculated_execution_count:
        raise RuntimeError(f"{label}.executionReportCount disagrees with occurrence results")
    execution_status_counts = _validate_status_map(
        module["executionStatusCounts"], f"{label}.executionStatusCounts"
    )
    if sum(execution_status_counts.values()) != execution_report_count:
        raise RuntimeError(f"{label}.executionStatusCounts do not sum to executionReportCount")
    variant_count = _require_int(module["variantCount"], f"{label}.variantCount", nonnegative=True)
    if variant_count != sum(int(raw["variantCount"]) for raw in occurrence_results):
        raise RuntimeError(f"{label}.variantCount disagrees with occurrence results")
    variant_status_counts = _validate_status_map(
        module["variantStatusCounts"], f"{label}.variantStatusCounts"
    )
    expected_variant_status_counts: Counter[str] = Counter()
    for raw in occurrence_results:
        expected_variant_status_counts["success"] += int(raw["successVariantCount"])
        expected_variant_status_counts["failure"] += int(raw["failureVariantCount"])
    expected_variant_status_counts = Counter(
        {key: value for key, value in expected_variant_status_counts.items() if value}
    )
    if variant_status_counts != dict(expected_variant_status_counts):
        raise RuntimeError(f"{label}.variantStatusCounts disagree with occurrence results")
    if sum(variant_status_counts.values()) != variant_count:
        raise RuntimeError(f"{label}.variantStatusCounts do not sum to variantCount")
    remaining_count = _require_int(
        module["remainingRetainedCount"], f"{label}.remainingRetainedCount", nonnegative=True
    )
    multiset = module["remainingRetainedMultiset"]
    if not isinstance(multiset, dict):
        raise RuntimeError(f"{label}.remainingRetainedMultiset must be an object")
    for key, count in multiset.items():
        if not isinstance(key, str):
            raise RuntimeError(f"{label}.remainingRetainedMultiset has a non-string key")
        _require_int(count, f"{label}.remainingRetainedMultiset.{key}", nonnegative=True)
    if sum(int(count) for count in multiset.values()) != remaining_count:
        raise RuntimeError(f"{label}.remainingRetainedMultiset does not sum to remaining count")
    return module


def validate_shard_identity(value: object) -> dict[str, object]:
    """Validate schema/kind/protocol identity shared by every shard report."""
    if not isinstance(value, dict):
        raise RuntimeError(f"materialization shard report must be an object: {value!r}")
    report_schema = value.get("reportSchema")
    if (
        not isinstance(report_schema, int)
        or isinstance(report_schema, bool)
        or report_schema != REPORT_SCHEMA
    ):
        raise RuntimeError(
            f"materialization shard report schema must be {REPORT_SCHEMA}: "
            f"{report_schema!r}"
        )
    if value.get("kind") != REPORT_KIND:
        raise RuntimeError(f"materialization shard report kind is invalid: {value!r}")
    if value.get("reportIdentity") != {
        "kind": REPORT_KIND,
        "reportSchema": REPORT_SCHEMA,
    }:
        raise RuntimeError(f"materialization shard report identity is invalid: {value!r}")
    validate_artifact_protocol(value.get("artifactProtocol"))
    return value


def validate_shard_shape(value: object) -> dict[str, object]:
    """Validate exact schema-5 structure and internal count coherence.

    This deliberately does not read referenced files.  Publication additionally
    requires ``verify_shard_evidence``, which binds this shape to the selected
    manifest and the durable run artifacts.
    """
    value = _exact_fields(value, SHARD_REPORT_FIELDS, "materialization shard report")
    validate_shard_identity(value)
    for field in (
        "manifestPath",
        "manifestHash",
        "repositoryCommit",
        "mathlibCommit",
        "runnerPath",
        "runnerHash",
    ):
        _require_string(value[field], f"materialization shard report.{field}")
    manifest = _validate_hash_ref(value["manifest"], "materialization shard report.manifest")
    if value["manifestPath"] != manifest["path"] or value["manifestHash"] != manifest["sha256"]:
        raise RuntimeError("materialization shard report manifest duplicate fields disagree")
    runner = _validate_hash_ref(value["runner"], "materialization shard report.runner")
    if value["runnerPath"] != runner["path"] or value["runnerHash"] != runner["sha256"]:
        raise RuntimeError("materialization shard report runner duplicate fields disagree")
    policy = _exact_fields(value["manifestPolicy"], MANIFEST_POLICY_FIELDS, "manifestPolicy")
    _require_bool(policy["allowDirty"], "manifestPolicy.allowDirty")
    _require_bool(policy["allowUnresolved"], "manifestPolicy.allowUnresolved")
    provenance = _exact_fields(value["provenance"], PROVENANCE_FIELDS, "provenance")
    for field in (
        "repositoryCommit",
        "mathlibCommit",
        "manifestRepositoryCommit",
        "manifestMathlibCommit",
    ):
        _require_string(provenance[field], f"provenance.{field}")
    lean = _exact_fields(provenance["lean"], frozenset({"version", "commit"}), "provenance.lean")
    _require_string(lean["version"], "provenance.lean.version")
    _require_string(lean["commit"], "provenance.lean.commit")
    if value["lean"] != lean:
        raise RuntimeError("top-level lean provenance disagrees")
    if value["repositoryCommit"] != provenance["repositoryCommit"]:
        raise RuntimeError("top-level repository commit disagrees with provenance")
    if value["mathlibCommit"] != provenance["mathlibCommit"]:
        raise RuntimeError("top-level Mathlib commit disagrees with provenance")
    _validate_source_preservation(
        value["exactSourcePreservation"],
        "materialization shard report.exactSourcePreservation",
        module=False,
    )
    if not _require_bool(value["compileSuccess"], "materialization shard report.compileSuccess"):
        raise RuntimeError("materialization shard report.compileSuccess must be true")
    selected_modules = _validate_string_list(
        value["selectedModules"], "materialization shard report.selectedModules"
    )
    modules_value = value["modules"]
    if not isinstance(modules_value, list) or not modules_value:
        raise RuntimeError("materialization shard report.modules must be a nonempty array")
    modules = [_validate_module_report(module, index) for index, module in enumerate(modules_value)]
    module_names = [str(module["module"]) for module in modules]
    if module_names != selected_modules:
        raise RuntimeError("selectedModules order/identity disagrees with modules")
    if len(module_names) != len(set(module_names)):
        raise RuntimeError("materialization shard report contains duplicate modules")

    expected_occurrence_results = [
        result for module in modules for result in module["occurrenceResults"]
    ]
    if value["occurrenceResults"] != expected_occurrence_results:
        raise RuntimeError("top-level occurrenceResults disagree with module results")
    expected_ids = [str(result["occurrence"]) for result in expected_occurrence_results]
    expected_actions = [str(result["action"]) for result in expected_occurrence_results]
    if len(expected_ids) != len(set(expected_ids)):
        raise RuntimeError("top-level occurrenceResults contain duplicate IDs")
    top_occurrence_counts = validate_occurrence_summary(
        value["occurrenceResults"],
        expected_ids,
        expected_actions,
        value["occurrenceClassificationCounts"],
    )
    if value["occurrenceClassificationCounts"] != top_occurrence_counts:
        raise RuntimeError("top-level occurrence classification counts disagree")
    totals = {
        "totalCount": sum(int(module["totalCount"]) for module in modules),
        "materializeCount": sum(int(module["materializeCount"]) for module in modules),
        "retainCount": sum(int(module["retainCount"]) for module in modules),
        "executionReportCount": sum(int(module["executionReportCount"]) for module in modules),
        "variantCount": sum(int(module["variantCount"]) for module in modules),
        "remainingRetainedCount": sum(int(module["remainingRetainedCount"]) for module in modules),
    }
    for field, expected in totals.items():
        actual = _require_int(value[field], f"materialization shard report.{field}", nonnegative=True)
        if actual != expected:
            raise RuntimeError(f"top-level {field} disagrees with module totals")
    expected_observed = [str(item) for module in modules for item in module["observedIds"]]
    expected_unobserved = [str(item) for module in modules for item in module["unobservedIds"]]
    if value["observedIds"] != expected_observed:
        raise RuntimeError("top-level observedIds disagree with module results")
    if value["unobservedIds"] != expected_unobserved:
        raise RuntimeError("top-level unobservedIds disagree with module results")
    _validate_string_list(value["observedIds"], "materialization shard report.observedIds")
    _validate_string_list(value["unobservedIds"], "materialization shard report.unobservedIds")
    if set(expected_observed) & set(expected_unobserved):
        raise RuntimeError("top-level observedIds and unobservedIds overlap")
    expected_execution_status: Counter[str] = Counter()
    expected_variant_status: Counter[str] = Counter()
    for module in modules:
        expected_execution_status.update(module["executionStatusCounts"])
        expected_variant_status.update(module["variantStatusCounts"])
    actual_execution_status = _validate_status_map(
        value["executionStatusCounts"], "materialization shard report.executionStatusCounts"
    )
    actual_variant_status = _validate_status_map(
        value["variantStatusCounts"], "materialization shard report.variantStatusCounts"
    )
    if actual_execution_status != dict(expected_execution_status):
        raise RuntimeError("top-level executionStatusCounts disagree with modules")
    if actual_variant_status != dict(expected_variant_status):
        raise RuntimeError("top-level variantStatusCounts disagree with modules")
    aggregate = _exact_fields(value["aggregate"], AGGREGATE_FIELDS, "aggregate")
    for field in AGGREGATE_FIELDS - {"occurrenceClassificationCounts"}:
        _require_int(aggregate[field], f"aggregate.{field}", nonnegative=True)
    _validate_count_map(
        aggregate["occurrenceClassificationCounts"],
        "aggregate.occurrenceClassificationCounts",
        frozenset(OCCURRENCE_CLASSIFICATIONS),
    )
    expected_aggregate = {
        "selectedModuleCount": len(modules),
        "totalCount": totals["totalCount"],
        "materializeCount": totals["materializeCount"],
        "retainCount": totals["retainCount"],
        "occurrenceClassificationCounts": top_occurrence_counts,
        "observedCount": len(expected_observed),
        "unobservedCount": len(expected_unobserved),
        "executionReportCount": totals["executionReportCount"],
        "variantCount": totals["variantCount"],
        "remainingRetainedCount": totals["remainingRetainedCount"],
    }
    if aggregate != expected_aggregate:
        raise RuntimeError(
            "aggregate disagrees with validated report values: "
            f"expected {expected_aggregate!r}, found {aggregate!r}"
        )
    return value


def validate_shard_protocol(value: object) -> dict[str, object]:
    """Compatibility alias for the current report shape validator."""
    return validate_shard_shape(value)


def _read_evidence_file(path_value: object, expected: Path, label: str) -> bytes:
    recorded = Path(_require_string(path_value, f"{label}.path")).resolve()
    expected = expected.resolve()
    if recorded != expected:
        raise RuntimeError(
            f"{label} path identity mismatch: {recorded} != {expected}"
        )
    if not recorded.is_file():
        raise RuntimeError(f"{label} evidence file does not exist: {recorded}")
    return recorded.read_bytes()


def _validate_evidence_hash(
    data: bytes, expected_hash: object, label: str
) -> None:
    recorded = _require_string(expected_hash, f"{label}.sha256")
    actual = sha256(data)
    if actual != recorded:
        raise RuntimeError(f"{label} hash mismatch: {actual} != {recorded}")


def _parse_jsonl_evidence(data: bytes, label: str) -> list[object]:
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise RuntimeError(f"{label} is not UTF-8") from error
    values: list[object] = []
    for index, line in enumerate(text.splitlines()):
        if not line:
            raise RuntimeError(f"{label} contains an empty JSONL line at {index}")
        try:
            values.append(json.loads(line))
        except json.JSONDecodeError as error:
            raise RuntimeError(f"{label} contains invalid JSON at line {index}") from error
    canonical = "".join(_canonical_json_line(value) + "\n" for value in values)
    if text != canonical:
        raise RuntimeError(f"{label} is not canonical JSONL")
    return values


def verify_shard_evidence(
    report: object,
    *,
    manifest: dict[str, Any],
    manifest_path: Path,
    manifest_bytes: bytes,
    selected: list[SelectedModule],
    debug_root: Path,
    timeout: int,
) -> dict[str, object]:
    """Bind a valid schema-7 shape to selected manifest and durable files."""
    report = validate_shard_shape(report)
    resolved_manifest = manifest_path.resolve()
    if report["manifestPath"] != str(resolved_manifest):
        raise RuntimeError("report manifestPath does not identify the selected manifest")
    if report["manifestHash"] != sha256(manifest_bytes):
        raise RuntimeError("report manifestHash does not match selected manifest bytes")
    manifest_data = _read_evidence_file(
        report["manifest"]["path"], resolved_manifest, "manifest"
    )
    if manifest_data != manifest_bytes:
        raise RuntimeError("selected manifest bytes changed before evidence verification")
    _validate_evidence_hash(manifest_data, report["manifest"]["sha256"], "manifest")

    repository_commit = _require_string(
        manifest.get("repositoryCommit"), "manifest repositoryCommit"
    )
    mathlib_commit = _require_string(
        manifest.get("mathlibCommit"), "manifest mathlibCommit"
    )
    if (
        report["repositoryCommit"] != repository_commit
        or report["provenance"]["manifestRepositoryCommit"] != repository_commit
        or report["provenance"]["repositoryCommit"] != repository_commit
    ):
        raise RuntimeError("report repository commit is not bound to the manifest")
    if (
        report["mathlibCommit"] != mathlib_commit
        or report["provenance"]["manifestMathlibCommit"] != mathlib_commit
        or report["provenance"]["mathlibCommit"] != mathlib_commit
    ):
        raise RuntimeError("report Mathlib commit is not bound to the manifest")
    if report["lean"] != manifest.get("lean"):
        raise RuntimeError("report Lean identity is not bound to the manifest")
    if report["manifestPolicy"] != {
        "allowDirty": False,
        "allowUnresolved": False,
    }:
        raise RuntimeError("report manifest policy is not closed")

    runner_path = Path(__file__).resolve()
    runner_data = _read_evidence_file(report["runner"]["path"], runner_path, "runner")
    _validate_evidence_hash(runner_data, report["runner"]["sha256"], "runner")
    if report["runnerHash"] != sha256(runner_data):
        raise RuntimeError("report runnerHash does not match the executing runner")

    if report["selectedModules"] != [item.module for item in selected]:
        raise RuntimeError("report selectedModules differ from manifest selection")
    if len(report["modules"]) != len(selected):
        raise RuntimeError("report module count differs from manifest selection")

    for module_report, item in zip(report["modules"], selected):
        if module_report["module"] != item.module:
            raise RuntimeError("report module identity differs from manifest selection")
        module_root = debug_root / _sanitize_stem(
            item.module.removeprefix("Mathlib/").removesuffix(".lean")
        )
        expected_paths = {
            "original": module_root / "original" / Path(*item.module.split("/")),
            "instrumented": module_root / "instrumented" / Path(*item.module.split("/")),
            "materialized": module_root / "materialized" / Path(*item.module.split("/")),
            "materializedLog": module_root / "materialized.log",
            "artifactReport": module_root / "artifact-reports.jsonl",
            "oracleLog": module_root / "declaration-oracle.log",
            "oracleReport": module_root / "declaration-oracle-report.json",
        }
        source_data = _read_evidence_file(
            module_report["sourcePath"], item.source_path, f"{item.module} source"
        )
        if source_data != item.source:
            raise RuntimeError(f"{item.module} source bytes changed from manifest selection")

        original_data = _read_evidence_file(
            module_report["original"]["path"],
            expected_paths["original"],
            f"{item.module} original",
        )
        _validate_evidence_hash(
            original_data, module_report["original"]["sha256"], f"{item.module} original"
        )
        if original_data != item.source or module_report["originalHash"] != sha256(item.source):
            raise RuntimeError(f"{item.module} original is not the selected source")

        instrumented_data = _read_evidence_file(
            module_report["instrumented"]["path"],
            expected_paths["instrumented"],
            f"{item.module} instrumented",
        )
        _validate_evidence_hash(
            instrumented_data,
            module_report["instrumented"]["sha256"],
            f"{item.module} instrumented",
        )
        if instrumented_data != instrumented_source(item.source, item.replacement_roots):
            raise RuntimeError(f"{item.module} instrumented evidence is not reproducible")

        artifact_data = _read_evidence_file(
            module_report["artifactReport"]["path"],
            expected_paths["artifactReport"],
            f"{item.module} artifact report",
        )
        _validate_evidence_hash(
            artifact_data,
            module_report["artifactReport"]["sha256"],
            f"{item.module} artifact report",
        )
        reports = _parse_jsonl_evidence(artifact_data, f"{item.module} artifact report")
        for artifact in reports:
            reject_forbidden_generated_text(artifact, f"artifact report for {item.module}")
        materialize_ids = [str(entry["id"]) for entry in item.materialize]
        root_ids = [str(entry["id"]) for entry in item.replacement_roots]
        covered_by = item.covered_by
        if module_report["replacementRootIds"] != root_ids:
            raise RuntimeError(f"{item.module} replacement roots differ from selected ranges")
        observed = {
            str(artifact["occurrence"])
            for artifact in reports
            if isinstance(artifact, dict) and isinstance(artifact.get("occurrence"), str)
        }
        unobserved = set(root_ids) - observed
        variants = group_report_variants(
            reports,
            root_ids,
            expected_module=item.compiled_module,
            unobserved_ids=unobserved,
        )
        execution_counts: Counter[str] = Counter(
            str(artifact["occurrence"])
            for artifact in reports
            if isinstance(artifact, dict)
        )
        expected_results = [
            make_occurrence_result(
                str(entry["id"]),
                str(entry["action"]),
                execution_counts.get(str(entry["id"]), 0),
                variants.get(str(entry["id"]), []),
                covered_by=covered_by.get(str(entry["id"])),
            )
            for entry in item.occurrences
        ]
        if module_report["occurrenceResults"] != expected_results:
            raise RuntimeError(
                f"{item.module} occurrence results are not derived from artifact evidence"
            )
        expected_execution_statuses: Counter[str] = Counter(
            str(artifact["status"])
            for artifact in reports
            if isinstance(artifact, dict)
        )
        if module_report["executionStatusCounts"] != dict(
            sorted(expected_execution_statuses.items())
        ):
            raise RuntimeError(
                f"{item.module} execution statuses are not derived from artifact evidence"
            )
        if module_report["materializeIds"] != materialize_ids or module_report[
            "retainIds"
        ] != [str(entry["id"]) for entry in item.retain]:
            raise RuntimeError(f"{item.module} action IDs differ from selected manifest")
        expected_observed = [value for value in materialize_ids if value in observed]
        expected_unobserved = [value for value in materialize_ids if value in unobserved]
        if (
            module_report["observedIds"] != expected_observed
            or module_report["unobservedIds"] != expected_unobserved
        ):
            raise RuntimeError(f"{item.module} observation IDs differ from artifacts")

        expected_materialized = _inject_import(
            replace_all_occurrences(item.source, list(item.materialize), variants),
            "ExplicitLean.SimpEngine.Boundary.Tactic",
        )
        materialized_data = _read_evidence_file(
            module_report["materialized"]["path"],
            expected_paths["materialized"],
            f"{item.module} materialized",
        )
        _validate_evidence_hash(
            materialized_data,
            module_report["materialized"]["sha256"],
            f"{item.module} materialized",
        )
        if materialized_data != expected_materialized:
            raise RuntimeError(f"{item.module} materialized evidence is not reproducible")
        guard = module_report["replayGuard"]
        replay_log = _read_evidence_file(
            guard["path"], expected_paths["materializedLog"], f"{item.module} replay log"
        )
        _validate_evidence_hash(replay_log, guard["sha256"], f"{item.module} replay log")
        check_replay_abort_markers(
            replay_log.decode("utf-8"), expected_nonce=guard["nonce"],
            expected_module=item.compiled_module,
        )
        remaining = [
            entry
            for entry in inventory.syntax_inventory_file(
                expected_paths["materialized"],
                f"{item.module}.materialized",
                timeout,
                allow_elaboration_errors=True,
                header_imports=True,
            )
            if entry["kind"] in inventory.SUPPORTED_KINDS
        ]
        actual_remaining = Counter(
            (str(entry["kind"]), str(entry["source"])) for entry in remaining
        )
        expected_remaining = Counter(
            (str(entry["kind"]), str(entry["source"])) for entry in item.retain
        )
        recorded_remaining = {
            f"{kind}\u0000{source}": count
            for (kind, source), count in sorted(expected_remaining.items())
        }
        if actual_remaining != expected_remaining:
            raise RuntimeError(
                f"{item.module} materialized inventory differs from retained manifest"
            )
        if (
            module_report["remainingRetainedCount"] != sum(expected_remaining.values())
            or module_report["remainingRetainedMultiset"] != recorded_remaining
        ):
            raise RuntimeError(
                f"{item.module} remaining retained evidence differs from manifest"
            )

        oracle = module_report["declarationOracle"]
        oracle_log = _read_evidence_file(
            oracle["path"], expected_paths["oracleLog"], f"{item.module} oracle log"
        )
        _validate_evidence_hash(oracle_log, oracle["sha256"], f"{item.module} oracle log")
        check_replay_abort_markers(
            oracle_log.decode("utf-8"), expected_nonce=oracle["replayGuard"]["nonce"],
            expected_module=item.compiled_module,
        )
        if _parse_declaration_oracle(oracle_log.decode("utf-8"), item.compiled_module) != oracle["report"]:
            raise RuntimeError(f"{item.module} oracle log differs from embedded report")
        oracle_report_data = _read_evidence_file(
            oracle["reportPath"],
            expected_paths["oracleReport"],
            f"{item.module} oracle report",
        )
        _validate_evidence_hash(
            oracle_report_data, oracle["reportSha256"], f"{item.module} oracle report"
        )
        try:
            durable_oracle = json.loads(oracle_report_data)
        except json.JSONDecodeError as error:
            raise RuntimeError(f"{item.module} oracle report is invalid JSON") from error
        if durable_oracle != oracle["report"]:
            raise RuntimeError(f"{item.module} oracle wrapper differs from durable report")
    return report


def run_shard(args: argparse.Namespace) -> dict[str, Any]:
    manifest_location = Path(args.manifest)
    if not manifest_location.is_absolute():
        manifest_location = ROOT / manifest_location
    # Resolve the real input before lexical cleanup checks: collapsing `..`
    # before following a directory symlink can select a different manifest.
    manifest_location = manifest_location.absolute()
    manifest_path = manifest_location.resolve()
    # Invalidate the exact requested destination after cleanup safety checks,
    # before manifest validation or compiler work.  A failed rerun must not
    # leave a previous success that a consumer could mistake for the current run.
    output_path = resolve_output_path(args.output, manifest_path)
    debug_root = debug_root_for(output_path)
    validate_cleanup_targets(
        manifest_path,
        output_path,
        debug_root,
        manifest_location=manifest_location,
    )
    invalidate_output(output_path)
    clear_debug_root(debug_root)
    if not manifest_path.is_file():
        raise RuntimeError(f"manifest does not exist: {manifest_path}")
    manifest_bytes = manifest_path.read_bytes()
    try:
        manifest = json.loads(manifest_bytes)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"manifest is not valid JSON: {manifest_path}") from error
    if not isinstance(manifest, dict):
        raise RuntimeError("manifest root must be an object")

    verify_implementation_hashes(manifest)
    if manifest.get("allowDirty") is not False:
        raise RuntimeError("boundary materialization requires allowDirty=false")
    corpus.assert_repository(
        _require_string(manifest.get("repositoryCommit"), "manifest repositoryCommit"),
        False,
    )
    provenance = verify_environment(manifest, args.timeout)
    selected = validate_manifest_selection(
        manifest,
        list(args.module),
        expect_total=args.expect_total,
        expect_materialize=args.expect_materialize,
    )
    verify_selected_classifications(selected, args.timeout)
    runner_path = Path(__file__).resolve()
    runner_hash = sha256(runner_path.read_bytes())
    dylib = _query_dynamic_library(args.timeout, debug_root)

    module_results: list[dict[str, Any]] = []
    for item in selected:
        module_results.append(_module_result(item, debug_root, dylib, args.timeout))

    # Recheck the immutable inputs after all compiler invocations.  A report is
    # only published if the same pinned environment and source set survived.
    if manifest_path.read_bytes() != manifest_bytes:
        raise RuntimeError("manifest_changed_during_run")
    verify_implementation_hashes(manifest)
    final_provenance = verify_environment(manifest, args.timeout)
    if final_provenance != provenance:
        raise RuntimeError("pinned_environment_changed_during_run")
    for item in selected:
        current_source = item.source_path.read_bytes()
        if current_source != item.source:
            raise RuntimeError(f"selected Mathlib source changed during run: {item.module}")

    aggregate_execution_status: Counter[str] = Counter()
    aggregate_variant_status: Counter[str] = Counter()
    aggregate_variant_count = 0
    aggregate_execution_count = 0
    aggregate_remaining = 0
    observed_ids: list[str] = []
    unobserved_ids: list[str] = []
    occurrence_results: list[dict[str, object]] = []
    for module in module_results:
        aggregate_execution_status.update(module["executionStatusCounts"])
        aggregate_variant_status.update(module["variantStatusCounts"])
        aggregate_variant_count += int(module["variantCount"])
        aggregate_execution_count += int(module["executionReportCount"])
        aggregate_remaining += int(module["remainingRetainedCount"])
        observed_ids.extend(str(value) for value in module["observedIds"])
        unobserved_ids.extend(str(value) for value in module["unobservedIds"])
        occurrence_results.extend(module["occurrenceResults"])
    total_count = sum(int(module["totalCount"]) for module in module_results)
    materialize_count = sum(int(module["materializeCount"]) for module in module_results)
    retain_count = sum(int(module["retainCount"]) for module in module_results)
    expected_occurrence_ids = [
        str(entry["id"])
        for module in selected
        for entry in module.occurrences
    ]
    expected_occurrence_actions = [
        str(entry["action"])
        for module in selected
        for entry in module.occurrences
    ]
    aggregate_occurrence_counts = validate_occurrence_summary(
        occurrence_results,
        expected_occurrence_ids,
        expected_occurrence_actions,
        occurrence_classification_counts(occurrence_results),
    )
    validate_artifact_protocol(artifact_protocol())
    report = {
        "kind": REPORT_KIND,
        "reportSchema": REPORT_SCHEMA,
        "reportIdentity": {"kind": REPORT_KIND, "reportSchema": REPORT_SCHEMA},
        "artifactProtocol": artifact_protocol(),
        "manifestPath": str(manifest_path),
        "manifestHash": sha256(manifest_bytes),
        "manifest": {"path": str(manifest_path), "sha256": sha256(manifest_bytes)},
        "manifestPolicy": {
            "allowDirty": manifest.get("allowDirty"),
            "allowUnresolved": manifest.get("allowUnresolved"),
        },
        "provenance": {
            "repositoryCommit": provenance["repositoryCommit"],
            "mathlibCommit": provenance["mathlibCommit"],
            "lean": provenance["lean"],
            "manifestRepositoryCommit": manifest["repositoryCommit"],
            "manifestMathlibCommit": manifest["mathlibCommit"],
        },
        "repositoryCommit": provenance["repositoryCommit"],
        "mathlibCommit": provenance["mathlibCommit"],
        "lean": provenance["lean"],
        "runnerPath": str(runner_path),
        "runnerHash": runner_hash,
        "runner": {"path": str(runner_path), "sha256": runner_hash},
        "selectedModules": [item.module for item in selected],
        "modules": module_results,
        "totalCount": total_count,
        "materializeCount": materialize_count,
        "retainCount": retain_count,
        "occurrenceResults": occurrence_results,
        "occurrenceClassificationCounts": aggregate_occurrence_counts,
        "observedIds": observed_ids,
        "unobservedIds": unobserved_ids,
        "executionReportCount": aggregate_execution_count,
        "variantCount": aggregate_variant_count,
        "executionStatusCounts": dict(sorted(aggregate_execution_status.items())),
        "variantStatusCounts": dict(sorted(aggregate_variant_status.items())),
        "remainingRetainedCount": aggregate_remaining,
        "exactSourcePreservation": {
            "verified": all(
                bool(module["exactSourcePreservation"]["verified"])
                for module in module_results
            ),
            "alphaRenaming": False,
            "statement": (
                "Every selected module preserved authored source bytes outside whole "
                "materialize tactic ranges exactly; authored binders and surrounding "
                "source were not alpha-renamed."
            ),
        },
        "compileSuccess": True,
        "aggregate": {
            "selectedModuleCount": len(module_results),
            "totalCount": total_count,
            "materializeCount": materialize_count,
            "retainCount": retain_count,
            "occurrenceClassificationCounts": aggregate_occurrence_counts,
            "observedCount": len(observed_ids),
            "unobservedCount": len(unobserved_ids),
            "executionReportCount": aggregate_execution_count,
            "variantCount": aggregate_variant_count,
            "remainingRetainedCount": aggregate_remaining,
        },
    }
    validate_shard_shape(report)
    verify_shard_evidence(
        report,
        manifest=manifest,
        manifest_path=manifest_path,
        manifest_bytes=manifest_bytes,
        selected=selected,
        debug_root=debug_root,
        timeout=args.timeout,
    )
    corpus.assert_repository(provenance["repositoryCommit"], False)
    _atomic_write_json(output_path, report)
    return report


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--manifest", required=True, help="closed boundary manifest JSON")
    result.add_argument(
        "--output",
        required=True,
        help="atomic JSON report path under .lake/boundary-materialization",
    )
    result.add_argument("--module", action="append", required=True, help="Mathlib module path")
    result.add_argument("--expect-total", type=int)
    result.add_argument("--expect-materialize", type=int)
    result.add_argument("--timeout", type=int, default=600)
    return result


def main() -> None:
    args = parser().parse_args()
    if args.timeout <= 0:
        print("boundary materialization shard failed: --timeout must be positive", file=sys.stderr)
        raise SystemExit(2)
    for name in ("expect_total", "expect_materialize"):
        value = getattr(args, name)
        if value is not None and value < 0:
            print(f"boundary materialization shard failed: --{name.replace('_', '-')} must be nonnegative", file=sys.stderr)
            raise SystemExit(2)
    try:
        report = run_shard(args)
    except Exception as error:
        emit_failure_marker(error)
        print(f"boundary materialization shard failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
    print(
        "boundary materialization shard: "
        f"modules={len(report['selectedModules'])}, "
        f"total={report['totalCount']}, materialize={report['materializeCount']}, "
        f"retain={report['retainCount']}, observed={len(report['observedIds'])}, "
        f"unobserved={len(report['unobservedIds'])}, variants={report['variantCount']}: ok"
    )


if __name__ == "__main__":
    main()
