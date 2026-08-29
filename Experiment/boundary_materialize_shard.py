#!/usr/bin/env python3
"""Run a bounded, manifest-driven Boundary materialization shard.

The manifest is the authority for scope classification.  This runner only
consumes selected, source-verified modules: it records materializable tactic
calls in a disposable module-root copy, groups the resulting Boundary
artifacts, materializes the complete materialize ranges, and checks that
retained syntax is the only supported simp syntax left in the generated copy.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Any, Iterable

import check_simp_engine_boundary_scope as scope
import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
from check_simp_engine_boundary_source import (
    group_report_variants,
    replace_all_occurrences,
)


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = corpus.MATHLIB
MANIFEST_KIND = "simp_engine_boundary_manifest"
MANIFEST_SCHEMA = 2
REPORT_KIND = "simp_engine_boundary_materialization_shard"
REPORT_SCHEMA = 3
ARTIFACT_MARKER = "SIMP_ENGINE_BOUNDARY_ARTIFACT "
DECLARATION_ORACLE_MARKER = "SIMP_ENGINE_DECLARATION_ORACLE "
DECLARATION_ORACLE_KIND = "simp_engine_declaration_oracle"
DECLARATION_ORACLE_SCHEMA = 1
BOUNDARY_DEBUG_ROOT = ROOT / ".lake" / "boundary-materialization"

# These are generated terms and source, not authored input.  In particular,
# an artifact containing sorryAx would make the translation report unsound.
FORBIDDEN_AXIOM = "sorryAx"
FORBIDDEN_TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_'])(?:sorry|admit)(?![A-Za-z0-9_'])")


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


def _command_output(command: list[str], timeout: int, label: str) -> str:
    code, output, _elapsed = _run_command(command, timeout)
    if code != 0:
        raise RuntimeError(f"{label} failed (exit {code}):\n{output}")
    return output


def _run_command(
    command: list[str], timeout: int
) -> tuple[int, str, float]:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
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


def _assert_nonoverlapping(entries: list[dict[str, Any]], module: str) -> None:
    ordered = sorted(
        entries,
        key=lambda entry: (int(entry["startByte"]), int(entry["endByte"])),
    )
    previous: dict[str, Any] | None = None
    for entry in ordered:
        start = _require_int(entry.get("startByte"), f"{module} occurrence startByte")
        end = _require_int(entry.get("endByte"), f"{module} occurrence endByte")
        if previous is not None:
            previous_end = int(previous["endByte"])
            if start < previous_end:
                raise RuntimeError(
                    f"nested or overlapping occurrence ranges in {module}: "
                    f"{previous['id']} [{previous['startByte']},{previous_end}) and "
                    f"{entry['id']} [{start},{end})"
                )
        previous = entry


@dataclass(frozen=True)
class SelectedModule:
    module: str
    compiled_module: str
    source_path: Path
    source: bytes
    occurrences: tuple[dict[str, Any], ...]
    materialize: tuple[dict[str, Any], ...]
    retain: tuple[dict[str, Any], ...]


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

    result: list[SelectedModule] = []
    for module in selected_names:
        validated = module_records.get(module)
        if validated is None:
            raise RuntimeError(
                f"selected module does not occur exactly once in manifest: {module}"
            )
        _record, source_path, source, checked_occurrence_tuple = validated
        checked_occurrences = list(checked_occurrence_tuple)
        _assert_nonoverlapping(checked_occurrences, module)
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


def _sanitize_stem(value: str) -> str:
    result = re.sub(r"[^A-Za-z0-9._-]+", "-", value).strip(".-")
    return result or "shard"


def debug_root_for(output: Path) -> Path:
    base = BOUNDARY_DEBUG_ROOT.resolve()
    try:
        relative = output.resolve().relative_to(base)
    except ValueError:
        name = output.stem
    else:
        name = relative.parts[0] if relative.parts else output.stem
    return base / _sanitize_stem(name)


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


def _remove_import(source: bytes, imported: str) -> bytes:
    injected = _injected_import(imported)
    if source.count(injected) != 1:
        raise RuntimeError(
            f"generated source does not contain one expected injected import: {imported}"
        )
    position = source.index(injected)
    return source[:position] + source[position + len(injected) :]


def _assert_context_gaps(
    original: bytes,
    generated: bytes,
    entries: Iterable[dict[str, Any]],
    *,
    imported: str,
    label: str,
) -> None:
    """Check that source gaps around replaced ranges remain byte-identical.

    Generated artifact text is intentionally opaque here.  The ordered gap
    check proves that all authored bytes outside the selected whole ranges are
    retained; the only other permitted change is the known import injection.
    """
    generated = _remove_import(generated, imported)
    ordered = sorted(entries, key=lambda entry: int(entry["startByte"]))
    original_cursor = 0
    generated_cursor = 0
    for index, entry in enumerate(ordered):
        start = int(entry["startByte"])
        gap = original[original_cursor:start]
        found = generated.find(gap, generated_cursor)
        if found < 0:
            raise RuntimeError(
                f"{label} does not preserve an authored source gap before "
                f"{entry['id']}"
            )
        if index == 0 and found != 0:
            raise RuntimeError(f"{label} changes authored source before the first range")
        generated_cursor = found + len(gap)
        original_cursor = int(entry["endByte"])
    trailing = original[original_cursor:]
    if not generated.endswith(trailing):
        raise RuntimeError(f"{label} does not preserve the authored source suffix")


def instrumented_source(
    source: bytes, materialize: list[dict[str, Any]]
) -> bytes:
    rewritten = inventory.rewrite_simp_heads(
        source,
        materialize,
        lambda entry: f'simp_engine_boundary_record "{entry["id"]}"',
    )
    return _inject_import(rewritten, "ExplicitLean.SimpEngine.Boundary")


def _parse_artifact_reports(output: str) -> list[object]:
    reports: list[object] = []
    for line in output.splitlines():
        if ARTIFACT_MARKER not in line:
            continue
        payload = line.split(ARTIFACT_MARKER, 1)[1].strip()
        try:
            reports.append(json.loads(payload))
        except json.JSONDecodeError as error:
            raise RuntimeError(f"invalid artifact report line: {line}") from error
    return reports


def _walk_strings(value: object) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for key, child in value.items():
            if isinstance(key, str):
                yield key
            yield from _walk_strings(child)
    elif isinstance(value, (list, tuple)):
        for child in value:
            yield from _walk_strings(child)


def _reject_forbidden_generated_text(value: object, label: str) -> None:
    for text in _walk_strings(value):
        if FORBIDDEN_AXIOM in text:
            raise RuntimeError(f"{label} contains forbidden {FORBIDDEN_AXIOM}")
        match = FORBIDDEN_TOKEN_RE.search(text)
        if match:
            raise RuntimeError(
                f"{label} contains introduced forbidden token {match.group(0)!r}"
            )


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


def _compile_copy(path: Path, dylib: str, timeout: int) -> tuple[int, str, float]:
    command = inventory.lean_command(path)
    command.insert(3, f"--load-dynlib={dylib}")
    return _run_command(command, timeout)


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


def _run_declaration_oracle(
    selected: SelectedModule,
    original_path: Path,
    materialized_path: Path,
    module_root: Path,
    dylib: str,
    timeout: int,
) -> dict[str, Any]:
    command = [
        "lake",
        "env",
        "lean",
        f"--load-dynlib={dylib}",
        "--run",
        "Experiment/SimpEngineDeclarationOracle.lean",
        selected.compiled_module,
        str(original_path),
        str(materialized_path),
    ]
    code, output, elapsed = _run_command(command, timeout)
    log_path = module_root / "declaration-oracle.log"
    report_path = module_root / "declaration-oracle-report.json"
    _write_text(log_path, output)
    try:
        oracle_report = _parse_declaration_oracle(output, selected.compiled_module)
    except RuntimeError as error:
        raise RuntimeError(
            f"declaration oracle protocol failed for {selected.module}: {error}; "
            f"see {log_path}"
        ) from error
    _atomic_write_json(report_path, oracle_report)
    if code != 0 or oracle_report["status"] != "success":
        category = oracle_report.get("failureCategory")
        detail = oracle_report.get("failureDetail")
        raise RuntimeError(
            f"declaration oracle failed for {selected.module}: "
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
    }


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
    instrumented = instrumented_source(selected.source, list(selected.materialize))
    instrumented_path = _copy_at_module_root(module_root / "instrumented", selected.module, instrumented)
    _assert_context_gaps(
        selected.source,
        instrumented,
        selected.materialize,
        imported="ExplicitLean.SimpEngine.Boundary",
        label=f"instrumented source {selected.module}",
    )

    instrumented_code, instrumented_output, instrumented_elapsed = _compile_copy(
        instrumented_path, dylib, timeout
    )
    _write_text(module_root / "instrumented.log", instrumented_output)
    if instrumented_code != 0:
        raise RuntimeError(
            f"instrumented module compilation failed for {selected.module} "
            f"(exit {instrumented_code}); see {module_root / 'instrumented.log'}"
        )
    report_list = _parse_artifact_reports(instrumented_output)
    for report in report_list:
        _reject_forbidden_generated_text(report, f"artifact report for {selected.module}")
    expected_ids = [str(entry["id"]) for entry in selected.materialize]
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
            unobserved_ids=unobserved_ids,
        )
    except RuntimeError as error:
        raise RuntimeError(
            f"{error}; generated source: {instrumented_path}; "
            f"see {module_root / 'instrumented.log'}"
        ) from error
    reports_path = module_root / "artifact-reports.jsonl"
    _write_jsonl(reports_path, report_list)

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
    )
    materialized_code, materialized_output, materialized_elapsed = _compile_copy(
        materialized_path, dylib, timeout
    )
    _write_text(module_root / "materialized.log", materialized_output)
    if materialized_code != 0:
        raise RuntimeError(
            f"materialized module compilation failed for {selected.module} "
            f"(exit {materialized_code}); see {module_root / 'materialized.log'}"
        )
    declaration_oracle = _run_declaration_oracle(
        selected, original_path, materialized_path, module_root, dylib, timeout
    )
    remaining = [
        entry
        for entry in inventory.syntax_inventory_file(
            materialized_path,
            f"{selected.module}.materialized",
            timeout,
            allow_elaboration_errors=True,
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
        occurrence_id: len(report_variants[occurrence_id])
        for occurrence_id in expected_ids
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
        "totalCount": len(selected.occurrences),
        "materializeCount": len(selected.materialize),
        "retainCount": len(selected.retain),
        "materializeIds": expected_ids,
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
    temporary.write_text(encoded, encoding="utf-8")
    temporary.replace(path)


def run_shard(args: argparse.Namespace) -> dict[str, Any]:
    manifest_path = Path(args.manifest)
    if not manifest_path.is_absolute():
        manifest_path = ROOT / manifest_path
    manifest_path = manifest_path.resolve()
    if not manifest_path.is_file():
        raise RuntimeError(f"manifest does not exist: {manifest_path}")
    manifest_bytes = manifest_path.read_bytes()
    try:
        manifest = json.loads(manifest_bytes)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"manifest is not valid JSON: {manifest_path}") from error
    if not isinstance(manifest, dict):
        raise RuntimeError("manifest root must be an object")

    output_path = resolve_output_path(args.output, manifest_path)
    debug_root = debug_root_for(output_path)
    debug_root.mkdir(parents=True, exist_ok=True)

    verify_implementation_hashes(manifest)
    provenance = verify_environment(manifest, args.timeout)
    selected = validate_manifest_selection(
        manifest,
        list(args.module),
        expect_total=args.expect_total,
        expect_materialize=args.expect_materialize,
    )
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
    for module in module_results:
        aggregate_execution_status.update(module["executionStatusCounts"])
        aggregate_variant_status.update(module["variantStatusCounts"])
        aggregate_variant_count += int(module["variantCount"])
        aggregate_execution_count += int(module["executionReportCount"])
        aggregate_remaining += int(module["remainingRetainedCount"])
        observed_ids.extend(str(value) for value in module["observedIds"])
        unobserved_ids.extend(str(value) for value in module["unobservedIds"])
    total_count = sum(int(module["totalCount"]) for module in module_results)
    materialize_count = sum(int(module["materializeCount"]) for module in module_results)
    retain_count = sum(int(module["retainCount"]) for module in module_results)
    report = {
        "kind": REPORT_KIND,
        "reportSchema": REPORT_SCHEMA,
        "reportIdentity": {"kind": REPORT_KIND, "reportSchema": REPORT_SCHEMA},
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
            "observedCount": len(observed_ids),
            "unobservedCount": len(unobserved_ids),
            "executionReportCount": aggregate_execution_count,
            "variantCount": aggregate_variant_count,
            "remainingRetainedCount": aggregate_remaining,
        },
    }
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
