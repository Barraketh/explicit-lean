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
from typing import Any, Iterable, Mapping

import check_simp_engine_boundary_scope as scope
import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
import lean_toolchain_cache as tool_cache
import manual_overlay
import simp_manual_overrides as manual_overrides
from process_runner import run_process
from boundary_protocol import (
    ABORT_CATEGORIES,
    RUN_NONCE_ENV,
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
REPORT_SCHEMA = 13
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


# The campaign manifest is intentionally a single JSON document.  A capsule
# lets a child authenticate one (or a few) module objects without constructing
# the 200MiB ``modules`` array.  These helpers are a small structural scanner:
# they recognize JSON strings/brackets, but never decode an unselected value.
CAPSULE_KIND = "simp_engine_boundary_manifest_capsule"
CAPSULE_SCHEMA = 1


def _json_string_end(data: bytes, offset: int) -> int:
    if offset >= len(data) or data[offset] != 34:  # ``\"``
        raise RuntimeError("manifest capsule scanner expected a JSON string")
    index = offset + 1
    escaped = False
    while index < len(data):
        byte = data[index]
        if escaped:
            escaped = False
        elif byte == 92:
            escaped = True
        elif byte == 34:
            return index + 1
        index += 1
    raise RuntimeError("manifest capsule scanner found an unterminated string")


def _json_value_end(data: bytes, offset: int) -> int:
    """Return the end of one JSON value without decoding it."""
    while offset < len(data) and data[offset] in b" \t\r\n":
        offset += 1
    if offset >= len(data):
        raise RuntimeError("manifest capsule scanner found a missing value")
    if data[offset] == 34:
        return _json_string_end(data, offset)
    if data[offset] in (91, 123):  # array/object
        opening = data[offset]
        closing = 93 if opening == 91 else 125
        depth = 1
        index = offset + 1
        while index < len(data):
            byte = data[index]
            if byte == 34:
                index = _json_string_end(data, index)
                continue
            if byte == opening:
                depth += 1
            elif byte == closing:
                depth -= 1
                if depth == 0:
                    return index + 1
            index += 1
        raise RuntimeError("manifest capsule scanner found an unterminated container")
    index = offset
    while index < len(data) and data[index] not in b",}] \t\r\n":
        index += 1
    return index


def _module_object_spans(data: bytes) -> tuple[tuple[int, int], dict[str, tuple[int, int]], tuple[int, int]]:
    """Find direct objects in the root ``modules`` array and its byte span."""
    index = 0
    while index < len(data) and data[index] in b" \t\r\n":
        index += 1
    if index >= len(data) or data[index] != 123:
        raise RuntimeError("manifest capsule scanner expected an object root")
    index += 1
    modules_span: tuple[int, int] | None = None
    spans: dict[str, tuple[int, int]] = {}
    while True:
        while index < len(data) and data[index] in b" \t\r\n":
            index += 1
        if index >= len(data):
            break
        if data[index] == 125:
            index += 1
            break
        key_start = index
        key_end = _json_string_end(data, key_start)
        try:
            key = json.loads(data[key_start:key_end])
        except json.JSONDecodeError as error:
            raise RuntimeError("manifest capsule scanner found an invalid root key") from error
        index = key_end
        while index < len(data) and data[index] in b" \t\r\n":
            index += 1
        if index >= len(data) or data[index] != 58:
            raise RuntimeError("manifest capsule scanner expected a colon")
        index += 1
        while index < len(data) and data[index] in b" \t\r\n":
            index += 1
        value_start = index
        value_end = _json_value_end(data, value_start)
        if key == "modules":
            if value_start >= len(data) or data[value_start] != 91:
                raise RuntimeError("manifest modules must be an array")
            modules_span = (value_start, value_end)
            cursor = value_start + 1
            while cursor < value_end - 1:
                while cursor < value_end - 1 and data[cursor] in b" \t\r\n,":
                    cursor += 1
                if cursor >= value_end - 1:
                    break
                object_start = cursor
                object_end = _json_value_end(data, object_start)
                if data[object_start] != 123:
                    raise RuntimeError("manifest modules contains a non-object record")
                inner = object_start + 1
                module_name: str | None = None
                while inner < object_end - 1:
                    while inner < object_end - 1 and data[inner] in b" \t\r\n,":
                        inner += 1
                    if inner >= object_end - 1:
                        break
                    inner_end = _json_string_end(data, inner)
                    field = json.loads(data[inner:inner_end])
                    inner = inner_end
                    while inner < object_end - 1 and data[inner] in b" \t\r\n":
                        inner += 1
                    if inner >= object_end - 1 or data[inner] != 58:
                        raise RuntimeError("manifest module object has no field colon")
                    inner += 1
                    while inner < object_end - 1 and data[inner] in b" \t\r\n":
                        inner += 1
                    field_start = inner
                    field_end = _json_value_end(data, field_start)
                    if field == "module":
                        try:
                            module_name = json.loads(data[field_start:field_end])
                        except json.JSONDecodeError as error:
                            raise RuntimeError("manifest module name is invalid JSON") from error
                    inner = field_end
                if not isinstance(module_name, str) or not module_name:
                    raise RuntimeError("manifest module object has no module name")
                if module_name in spans:
                    raise RuntimeError(f"duplicate manifest module: {module_name}")
                spans[module_name] = (object_start, object_end)
                cursor = object_end

        index = value_end
        while index < len(data) and data[index] in b" \t\r\n":
            index += 1
        if index < len(data) and data[index] == 44:
            index += 1
            continue
        if index < len(data) and data[index] == 125:
            index += 1
            break
    if modules_span is None:
        raise RuntimeError("manifest has no modules array")
    return modules_span, spans, (0, index)


def stream_manifest_capsule(
    manifest_path: Path,
    capsule: Mapping[str, Any],
    requested_modules: Sequence[str] | None = None,
) -> tuple[str, int, dict[str, bytes]]:
    """Hash a manifest incrementally and capture only capsule-selected objects."""
    expected_hash = capsule.get("manifestHash")
    expected_size = capsule.get("manifestSize")
    modules_span = capsule.get("modulesSpan")
    selected = capsule.get("selectedModules")
    manual_modules = capsule.get("manualModules", [])
    if not isinstance(expected_hash, str) or not isinstance(expected_size, int) or expected_size < 0:
        raise RuntimeError("capsule has invalid manifest identity")
    if not isinstance(modules_span, list) or len(modules_span) != 2:
        raise RuntimeError("capsule has invalid modules span")
    if not isinstance(selected, list):
        raise RuntimeError("capsule selectedModules must be an array")
    spans: dict[str, tuple[int, int]] = {}
    requested = set(requested_modules) if requested_modules is not None else None
    selected_to_capture = [raw for raw in selected if requested is None or raw.get("module") in requested]
    all_records = list(selected_to_capture) + list(manual_modules) if isinstance(manual_modules, list) else list(selected_to_capture)
    for raw in all_records:
        if not isinstance(raw, Mapping) or not isinstance(raw.get("module"), str):
            raise RuntimeError("capsule selected module record is invalid")
        span = raw.get("span")
        if not isinstance(span, list) or len(span) != 2 or not all(isinstance(v, int) for v in span):
            raise RuntimeError(f"capsule span is invalid for {raw.get('module')}")
        if not 0 <= span[0] < span[1] <= expected_size:
            raise RuntimeError(f"capsule span is outside the manifest for {raw.get('module')}")
        # A module record is authenticated only when it is an object inside
        # the root modules array, never an arbitrary root/global byte range.
        if not 0 <= int(modules_span[0]) <= span[0] < span[1] <= int(modules_span[1]):
            raise RuntimeError(f"capsule module span is outside modules: {raw.get('module')}")
        module = str(raw["module"])
        if module in spans:
            if spans[module] != (span[0], span[1]):
                raise RuntimeError(f"duplicate capsule module projection: {module}")
            continue
        spans[module] = (span[0], span[1])
    hasher = hashlib.sha256()
    global_hasher = hashlib.sha256()
    captures: dict[str, bytearray] = {module: bytearray() for module in spans}
    modules_start, modules_end = int(modules_span[0]), int(modules_span[1])
    if not 0 <= modules_start < modules_end <= expected_size:
        raise RuntimeError("capsule modules span is outside the manifest")
    size = 0
    try:
        with manifest_path.open("rb") as stream:
            while chunk := stream.read(1024 * 1024):
                chunk_start = size
                size += len(chunk)
                hasher.update(chunk)
                # The root bytes outside the modules array authenticate all
                # global fields without decoding that array.
                for left, right in ((0, modules_start), (modules_end, size)):
                    begin = max(chunk_start, left)
                    end = min(size, right)
                    if begin < end:
                        global_hasher.update(chunk[begin - chunk_start:end - chunk_start])
                for module, (start, end) in spans.items():
                    begin = max(chunk_start, start)
                    finish = min(size, end)
                    if begin < finish:
                        captures[module].extend(chunk[begin - chunk_start:finish - chunk_start])
    except OSError as error:
        raise RuntimeError(f"cannot stream manifest {manifest_path}: {error}") from error
    actual_hash = hasher.hexdigest()
    if size != expected_size or actual_hash != expected_hash:
        raise RuntimeError("manifest changed or does not match capsule")
    if capsule.get("globalBytesSha256") != global_hasher.hexdigest():
        raise RuntimeError("manifest global identity does not match capsule")
    try:
        with manifest_path.open("rb") as stream:
            prefix = stream.read(modules_start)
            stream.seek(modules_end)
            suffix = stream.read()
        global_identity = json.loads(prefix + b"[]" + suffix)
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError("manifest global identity is not valid JSON") from error
    expected_global = capsule.get("globalIdentity")
    if isinstance(global_identity, dict):
        global_identity = dict(global_identity)
        global_identity.pop("modules", None)
    if not isinstance(global_identity, dict) or global_identity != expected_global:
        raise RuntimeError("manifest global identity fields differ from capsule")
    result = {module: bytes(value) for module, value in captures.items()}
    for raw in all_records:
        module = str(raw["module"])
        actual = result[module]
        if sha256(actual) != raw.get("recordSha256"):
            raise RuntimeError(f"selected manifest record hash mismatch: {module}")
    return actual_hash, size, result


def make_manifest_capsule(
    manifest_path: Path,
    manifest_bytes: bytes,
    manifest: Mapping[str, Any],
    selected: Sequence["SelectedModule"],
    *,
    overlay_identity: Mapping[str, Any] | None = None,
    manual_modules: Sequence[str] = (),
) -> dict[str, Any]:
    """Build a compact authenticated projection after global validation."""
    modules_span, spans, _root_span = _module_object_spans(manifest_bytes)
    records = {str(raw.get("module")): raw for raw in manifest.get("modules", []) if isinstance(raw, Mapping)}
    selected_records: list[dict[str, Any]] = []
    for item in selected:
        raw = records.get(item.module)
        span = spans.get(item.module)
        if raw is None or span is None:
            raise RuntimeError(f"validated selected module is absent from manifest: {item.module}")
        selected_records.append({
            "module": item.module,
            "span": [span[0], span[1]],
            "recordSha256": sha256(manifest_bytes[span[0]:span[1]]),
        })
    manual_records: list[dict[str, Any]] = []
    for module in sorted(set(manual_modules)):
        raw = records.get(module)
        span = spans.get(module)
        if raw is None or span is None:
            raise RuntimeError(f"manual overlay module is absent from manifest: {module}")
        manual_records.append({
            "module": module,
            "span": [span[0], span[1]],
            "recordSha256": sha256(manifest_bytes[span[0]:span[1]]),
        })
    global_bytes = manifest_bytes[:modules_span[0]] + manifest_bytes[modules_span[1]:]
    return {
        "kind": CAPSULE_KIND,
        "schema": CAPSULE_SCHEMA,
        "manifestPath": str(manifest_path.resolve()),
        "manifestHash": sha256(manifest_bytes),
        "manifestSize": len(manifest_bytes),
        "modulesSpan": [modules_span[0], modules_span[1]],
        "globalBytesSha256": sha256(global_bytes),
        "globalIdentity": {
            key: value for key, value in manifest.items() if key != "modules"
        },
        "selectedModules": selected_records,
        "manualModules": manual_records,
        "manualOverlay": dict(overlay_identity) if overlay_identity is not None else None,
    }


def read_manifest_capsule(path: Path, *, expected_hash: str | None = None) -> tuple[dict[str, Any], bytes]:
    try:
        payload = path.read_bytes()
    except OSError as error:
        raise RuntimeError(f"cannot read manifest capsule {path}: {error}") from error
    if expected_hash is not None and sha256(payload) != expected_hash:
        raise RuntimeError("manifest capsule changed or has the wrong hash")
    try:
        value = json.loads(payload)
    except json.JSONDecodeError as error:
        raise RuntimeError("manifest capsule is not valid JSON") from error
    if not isinstance(value, dict) or value.get("kind") != CAPSULE_KIND or value.get("schema") != CAPSULE_SCHEMA:
        raise RuntimeError("unsupported manifest capsule")
    return value, payload


def validate_capsule_module_record(
    module: str, raw_module: Mapping[str, Any], source_path: Path,
) -> "SelectedModule":
    """Validate the selected projection against the current source bytes."""
    if not module.startswith("Mathlib/") or not module.endswith(".lean") or ".." in Path(module).parts:
        raise RuntimeError(f"capsule module is not a pinned Mathlib path: {module}")
    source_path = source_path.resolve()
    try:
        source = source_path.read_bytes()
    except OSError as error:
        raise RuntimeError(f"cannot read selected source for {module}: {error}") from error
    if raw_module.get("module") != module:
        raise RuntimeError(f"capsule selected module mismatch: {module}")
    compiled = corpus.compiled_module_name(module)
    if raw_module.get("compiledModule") != compiled:
        raise RuntimeError(f"capsule compiled module mismatch: {module}")
    if raw_module.get("moduleHash") != sha256(module.encode("utf-8")):
        raise RuntimeError(f"capsule module hash mismatch: {module}")
    if raw_module.get("sourceHash") != sha256(source):
        raise RuntimeError(f"selected source hash mismatch: {module}")
    occurrences = raw_module.get("occurrences")
    if not isinstance(occurrences, list):
        raise RuntimeError(f"capsule occurrences must be an array: {module}")
    checked: list[dict[str, Any]] = []
    seen: set[str] = set()
    for occurrence in occurrences:
        item = _validate_occurrence(module, source, occurrence)
        if str(item["id"]) in seen:
            raise RuntimeError(f"duplicate capsule occurrence: {item['id']}")
        seen.add(str(item["id"]))
        checked.append(item)
    replacement_plan(source, checked, module)
    if any(item["executionRole"] == "reusable_executable" for item in checked):
        raise RuntimeError(f"selected module contains reusable_executable: {module}")
    if any(item["action"] == "unresolved" for item in checked):
        raise RuntimeError(f"selected module contains unresolved occurrences: {module}")
    materialize = tuple(item for item in checked if item["action"] == "materialize")
    retain = tuple(item for item in checked if item["action"] == "retain")
    if not materialize:
        raise RuntimeError(f"selected module has no materialize occurrences: {module}")
    return SelectedModule(module, compiled, source_path, source, tuple(checked), materialize, retain)


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
    protected_inputs: Iterable[Path] = (),
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
    input_paths.extend(Path(os.path.abspath(path)) for path in protected_inputs)
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


def validate_capsule_global_identity(identity: object) -> None:
    """Validate every authenticated non-module manifest field in capsule mode.

    The campaign worker performs the expensive full record/source validation
    before it publishes a capsule.  Children still reproduce the complete
    global schema, policy, and count-map checks instead of treating an
    authenticated byte projection as semantically valid by itself.
    """
    if not isinstance(identity, dict):
        raise RuntimeError("capsule global identity must be an object")
    expected_fields = set(corpus.MANIFEST_FIELDS) - {"modules"}
    if set(identity) != expected_fields:
        missing = sorted(expected_fields - set(identity))
        extra = sorted(set(identity) - expected_fields)
        raise RuntimeError(
            f"capsule global identity fields differ from manifest schema: "
            f"missing={missing}, extra={extra}"
        )
    if identity.get("reportSchema") != MANIFEST_SCHEMA:
        raise RuntimeError("capsule manifest schema is unsupported")
    if identity.get("kind") != MANIFEST_KIND:
        raise RuntimeError("capsule manifest kind is invalid")
    if identity.get("allowDirty") is not False or identity.get("allowUnresolved") is not False:
        raise RuntimeError("capsule requires a closed manifest policy")
    for field in ("repositoryCommit", "mathlibCommit"):
        _require_string(identity.get(field), f"capsule {field}")
    if not isinstance(identity.get("modulePrefix"), str):
        raise RuntimeError("capsule modulePrefix must be a string")
    lean = identity.get("lean")
    if not isinstance(lean, dict) or set(lean) != {"version", "commit"}:
        raise RuntimeError("capsule Lean identity is invalid")
    _require_string(lean.get("version"), "capsule lean.version")
    _require_string(lean.get("commit"), "capsule lean.commit")
    numeric_fields = (
        "moduleFileCount", "inventoriedModuleCount", "occurrenceCount",
        "nestedOccurrenceCount", "duplicateSyntaxRecords",
        "duplicateScopeSyntaxRecords",
    )
    numbers = {
        field: _require_int(identity.get(field), f"capsule {field}", nonnegative=True)
        for field in numeric_fields
    }
    if numbers["inventoriedModuleCount"] > numbers["moduleFileCount"]:
        raise RuntimeError("capsule inventoriedModuleCount exceeds moduleFileCount")
    if numbers["nestedOccurrenceCount"] > numbers["occurrenceCount"]:
        raise RuntimeError("capsule nestedOccurrenceCount exceeds occurrenceCount")
    for field in ("fullFrontendFallbacks", "scopeFrontendFallbacks"):
        value = identity.get(field)
        if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
            raise RuntimeError(f"capsule {field} must be an array of strings")
    expected_probe = {
        "module": scope.SCOPE_PROBE_IMPORT,
        "scheduling": scope.SCOPE_PROBE_SCHEDULING,
        "temporaryCopyOnly": True,
        "reportCommand": "simp_engine_boundary_scope_report",
    }
    if identity.get("scopeProbe") != expected_probe:
        raise RuntimeError("capsule scopeProbe metadata is invalid")
    implementations = identity.get("implementationHashes")
    if not isinstance(implementations, dict) or not implementations or not all(
        isinstance(path, str) and path and isinstance(digest, str) and digest
        for path, digest in implementations.items()
    ):
        raise RuntimeError("capsule implementationHashes is invalid")
    manual = identity.get("manualOverrides")
    if not isinstance(manual, dict) or set(manual) != {"sha256", "schema", "environment"}:
        raise RuntimeError("capsule manualOverrides identity is invalid")
    digest = manual.get("sha256")
    if not isinstance(digest, str) or len(digest) != 64 or any(
        character not in "0123456789abcdef" for character in digest
    ):
        raise RuntimeError("capsule manualOverrides digest is invalid")
    if manual.get("schema") != manual_overrides.SCHEMA:
        raise RuntimeError("capsule manualOverrides schema is invalid")
    if manual.get("environment") != {
        "mathlibCommit": identity["mathlibCommit"], "lean": lean,
    }:
        raise RuntimeError("capsule manualOverrides environment is invalid")
    count_maps = (
        _validate_count_map(identity.get("countsByExecutionRole"),
                            "countsByExecutionRole", corpus.EXECUTION_ROLES),
        _validate_count_map(identity.get("countsByDeclarationKind"),
                            "countsByDeclarationKind", corpus.DECLARATION_KINDS),
        _validate_count_map(identity.get("countsByAction"),
                            "countsByAction", corpus.ACTIONS),
    )
    for counts in count_maps:
        if sum(counts.values()) != numbers["occurrenceCount"]:
            raise RuntimeError("capsule count map does not sum to occurrenceCount")
    if count_maps[2].get("unresolved", 0) != 0:
        raise RuntimeError("capsule closed manifest contains unresolved occurrences")


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


@dataclass(frozen=True)
class OverlaySelection:
    """Canonical manifest selection plus its freshly classified patched copy."""

    canonical: SelectedModule
    effective: SelectedModule
    entries: tuple[dict[str, Any], ...]
    mappings: tuple[dict[str, Any], ...]


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


def prepare_overlay_selection(
    canonical: SelectedModule,
    overlay: manual_overlay.Overlay,
    debug_root: Path,
    timeout: int,
) -> OverlaySelection:
    """Apply manual splices and freshly classify every untouched occurrence."""
    entries = tuple(overlay.entries_by_module().get(canonical.module, ()))
    if not entries:
        mappings = tuple(
            {
                "canonicalId": str(entry["id"]),
                "effectiveId": str(entry["id"]),
                "kind": str(entry["kind"]),
                "source": str(entry["source"]),
                "canonicalStartByte": int(entry["startByte"]),
                "canonicalEndByte": int(entry["endByte"]),
                "effectiveStartByte": int(entry["startByte"]),
                "effectiveEndByte": int(entry["endByte"]),
            }
            for entry in canonical.occurrences
        )
        return OverlaySelection(canonical, canonical, (), mappings)

    patched = overlay.apply(canonical.module, canonical.source)
    patched_path = _copy_at_module_root(
        debug_root / "manual-overlay-input", canonical.module, patched
    )
    expected = tuple(overlay.shifted_occurrences(canonical.module))
    expected_by_position: dict[tuple[str, str, int, int], dict[str, object]] = {}
    for record in expected:
        key = (
            str(record["kind"]), str(record["source"]),
            int(record["startByte"]), int(record["endByte"]),
        )
        if key in expected_by_position:
            raise RuntimeError(
                f"manual overlay produced duplicate shifted occurrence coordinates in "
                f"{canonical.module}: {key!r}"
            )
        expected_by_position[key] = record

    raw_inventory = inventory.syntax_inventory_file(
        patched_path, canonical.module, timeout,
        allow_elaboration_errors=True, header_imports=True,
    )
    inventoried, _nested, _duplicates = corpus.validate_module_inventory(
        canonical.module, patched, raw_inventory
    )
    actual_by_position = {
        (str(record["kind"]), str(record["source"]),
         int(record["startByte"]), int(record["endByte"])): record
        for record in inventoried if record.get("kind") in inventory.SUPPORTED_KINDS
    }
    if set(actual_by_position) != set(expected_by_position):
        raise RuntimeError(
            f"manual overlay changed the untouched simp inventory in {canonical.module}: "
            f"expected={sorted(expected_by_position)}, actual={sorted(actual_by_position)}"
        )

    compiled = canonical.compiled_module
    scoped, declarations, _fallbacks = scope.load_records_with_fallbacks(
        [scope.ModuleSpec(compiled, patched_path, len(inventoried))],
        batch_size=1, timeout=timeout,
    )
    classified, _duplicate_scope = corpus.join_scope_records(
        canonical.module, inventoried, scoped.get(compiled, []),
        declarations.get(compiled, []),
    )
    unresolved = [entry for entry in classified if entry["action"] == "unresolved"]
    if unresolved:
        unresolved_ids = {str(entry["id"]) for entry in unresolved}
        scope.apply_execution_evidence(
            compiled, patched, unresolved,
            entries=[entry for entry in inventoried if str(entry["id"]) in unresolved_ids],
            timeout=timeout,
        )
    remaining_unresolved = [
        str(entry["id"]) for entry in classified if entry["action"] == "unresolved"
    ]
    if remaining_unresolved:
        raise RuntimeError(
            f"manual overlay left unresolved calls in {canonical.module}: "
            f"{remaining_unresolved}"
        )

    canonical_by_id = {str(entry["id"]): entry for entry in canonical.occurrences}
    mappings: list[dict[str, Any]] = []
    for record in classified:
        key = (
            str(record["kind"]), str(record["source"]),
            int(record["startByte"]), int(record["endByte"]),
        )
        expected_record = expected_by_position.get(key)
        if expected_record is None:
            raise RuntimeError(
                f"manual overlay classified an unmapped occurrence in {canonical.module}: {key!r}"
            )
        canonical_id = str(expected_record["canonicalId"])
        effective_id = str(record["id"])
        if effective_id != str(expected_record["id"]):
            raise RuntimeError(
                f"manual overlay effective ID mismatch in {canonical.module}: "
                f"{effective_id} != {expected_record['id']}"
            )
        canonical_record = canonical_by_id[canonical_id]
        for field in ("executionRole", "declarationKind", "action"):
            if canonical_record.get(field) != record.get(field):
                raise RuntimeError(
                    f"manual overlay changed {field} for {canonical.module}:"
                    f"{canonical_id}: {canonical_record.get(field)!r} != {record.get(field)!r}"
                )
        mappings.append({
            "canonicalId": canonical_id,
            "effectiveId": effective_id,
            "kind": str(record["kind"]),
            "source": str(record["source"]),
            "canonicalStartByte": int(expected_record["canonicalStartByte"]),
            "canonicalEndByte": int(expected_record["canonicalEndByte"]),
            "effectiveStartByte": int(record["startByte"]),
            "effectiveEndByte": int(record["endByte"]),
        })

    effective = SelectedModule(
        module=canonical.module, compiled_module=compiled,
        source_path=patched_path, source=patched,
        occurrences=tuple(classified),
        materialize=tuple(entry for entry in classified if entry["action"] == "materialize"),
        retain=tuple(entry for entry in classified if entry["action"] == "retain"),
    )
    return OverlaySelection(canonical, effective, entries, tuple(mappings))


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


def _recording_tactic(recording_mode: str) -> str:
    if recording_mode not in {"stock", "applied"}:
        raise ValueError(f"unsupported boundary recording mode: {recording_mode!r}")
    return "simp_engine_boundary_record_applied" if recording_mode == "applied" else "simp_engine_boundary_record"


def instrumented_source(
    source: bytes, materialize: list[dict[str, Any]], *, recording_mode: str = "stock"
) -> bytes:
    tactic = _recording_tactic(recording_mode)
    rewritten = inventory.rewrite_simp_heads(
        source,
        materialize,
        lambda entry: f'{tactic} "{entry["id"]}"',
    )
    return _inject_import(rewritten, "ExplicitLean.SimpEngine.Boundary")


def instrumentation_replacement_lengths(
    source: bytes, entries: list[dict[str, Any]], *, recording_mode: str = "stock"
) -> list[int]:
    """Lengths of the instrumented outer tactics, in validated source order.

    Only the four-byte ``simp`` head grows. A ``%$`` head annotation moves
    before the injected arguments but retains every original byte.
    """
    tactic = _recording_tactic(recording_mode)
    roots, _ = replacement_plan(source, entries, "instrumentation lengths")
    return [
        int(entry["endByte"]) - int(entry["startByte"])
        + len(f'{tactic} "{entry["id"]}"'.encode("utf-8")) - 4
        for entry in roots
    ]


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
    invocation_path: Path | None = None,
    module: str | None = None,
    recording_mode: str | None = None,
) -> tuple[int, str, float]:
    dylib = str(Path(dylib).resolve())
    command = _compiler_command(path, dylib)
    if invocation_path is not None:
        nonce = (env or {}).get(RUN_NONCE_ENV)
        if not nonce or not module:
            raise ValueError("compiler invocation receipt requires module and explicit nonce")
        _atomic_write_json(invocation_path, {
            "kind": "boundary_compiler_invocation_v1", "module": module,
            "source": str(path.resolve()), "sourceSha256": sha256(path.read_bytes()),
            "command": command, "cwd": str(ROOT), "nonce": nonce,
            "timeoutSeconds": timeout, "recordingMode": recording_mode,
            "runtime": str(Path(dylib).resolve()), "runtimeSha256": sha256(Path(dylib).read_bytes()),
        })
    return _run_command(command, timeout, env=env)


def _shared_runtime_path() -> Path:
    suffix = "dylib" if sys.platform == "darwin" else "so"
    return (ROOT / ".lake" / "build" / "lib" / f"libexplicitLean_ExplicitLean.{suffix}").resolve()


def _oracle_runtime_path() -> Path:
    return (ROOT / ".lake" / "build" / "bin" / "simpEngineDeclarationOracle").resolve()


def _compiler_command(path: Path, dylib: str) -> list[str]:
    command = inventory.lean_command(path.resolve())
    command.insert(3, f"--load-dynlib={dylib}")
    return command


def _oracle_command(module: str, original: Path, materialized: Path) -> list[str]:
    return ["lake", "env", str(_oracle_runtime_path()), module,
            str(original.resolve()), str(materialized.resolve())]


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
    # Build before recording its identity, then invoke that exact executable.
    # Running the cache launcher after writing the receipt could rebuild it.
    oracle_binary = _oracle_runtime_path()
    target, _relative_binary = tool_cache.TOOLS["oracle"]
    tool_cache._build("oracle", target, oracle_binary)
    command = _oracle_command(compiled_module, original_path, materialized_path)
    environment, nonce = replay_subprocess_environment()
    _atomic_write_json(module_root / "oracle-invocation.json", {
        "kind": "boundary_oracle_invocation_v1", "module": compiled_module,
        "stockSource": str(original_path.resolve()), "stockSourceSha256": sha256(original_path.read_bytes()),
        "appliedSource": str(materialized_path.resolve()), "appliedSourceSha256": sha256(materialized_path.read_bytes()),
        "command": command, "cwd": str(ROOT), "nonce": nonce, "timeoutSeconds": timeout,
        "runtime": str(oracle_binary), "runtimeSha256": sha256(oracle_binary.read_bytes()),
        "recordingMode": None,
    })
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
    reject_compiler_sorry_warning(output, f"replay output for {module}")
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


def reject_compiler_sorry_warning(output: str, label: str) -> None:
    """Reject compiler output whose declaration depends on ``sorryAx``.

    Artifact payloads already reject authored ``sorry`` tokens.  This separate
    output check also catches ``sorryAx`` inserted by elaborator error recovery
    or by generated syntax outside an artifact payload.  Durable report
    verification applies the same check to every authenticated compiler log.
    """
    if re.search(
        r"warning:\s+declaration uses\s+[`'‘’“”]?(?:sorry|sorryAx)[`'‘’“”]?(?:\s|[.,;:]|$)",
        output,
    ):
        raise RuntimeError(f"{label} contains a declaration using sorry")


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
    if Path(value).resolve() != _shared_runtime_path():
        raise RuntimeError(f"unexpected ExplicitLean shared runtime: {value!r}")
    return str(_shared_runtime_path())


def _module_result(
    selected: SelectedModule,
    debug_root: Path,
    dylib: str,
    timeout: int,
    *,
    recording_mode: str = "applied",
) -> dict[str, Any]:
    tactic = _recording_tactic(recording_mode)
    module_slug = _sanitize_stem(selected.module.removeprefix("Mathlib/").removesuffix(".lean"))
    module_root = debug_root / module_slug
    original_path = _copy_at_module_root(module_root / "original", selected.module, selected.source)
    roots = selected.replacement_roots
    covered_by = selected.covered_by
    instrumented = instrumented_source(selected.source, roots, recording_mode=recording_mode)
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
            lambda entry: f'{tactic} "{entry["id"]}"',
        ),
        replacement_lengths=instrumentation_replacement_lengths(
            selected.source, selected.materialize, recording_mode=recording_mode
        ),
    )

    recording_environment, recording_nonce = recording_subprocess_environment()
    instrumented_code, instrumented_output, instrumented_elapsed = _compile_copy(
        instrumented_path, dylib, timeout, env=recording_environment,
        invocation_path=module_root / "recording-invocation.json",
        module=selected.compiled_module, recording_mode=recording_mode,
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
    reject_compiler_sorry_warning(
        instrumented_output, f"recording output for {selected.compiled_module}"
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
        materialized_path, dylib, timeout, env=replay_environment,
        invocation_path=module_root / "replay-invocation.json", module=selected.compiled_module,
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
        "recordingMode": recording_mode,
        "runtime": str(Path(dylib).resolve()),
        "runtimeSha256": sha256(Path(dylib).read_bytes()),
        "recordingInvocation": {"path": str((module_root / "recording-invocation.json").resolve()),
                                 "sha256": sha256((module_root / "recording-invocation.json").read_bytes())},
        "recordingLog": {"path": str((module_root / "instrumented.log").resolve()),
                          "sha256": sha256((module_root / "instrumented.log").read_bytes())},
        "replayInvocation": {"path": str((module_root / "replay-invocation.json").resolve()),
                              "sha256": sha256((module_root / "replay-invocation.json").read_bytes())},
        "oracleInvocation": {"path": str((module_root / "oracle-invocation.json").resolve()),
                              "sha256": sha256((module_root / "oracle-invocation.json").read_bytes())},
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
        "manualOverlay": None,
        "canonicalTotalCount": len(selected.occurrences),
        "manualReplacementCount": 0,
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


def attach_manual_overlay_evidence(
    result: dict[str, Any],
    selection: OverlaySelection,
    overlay: manual_overlay.Overlay,
    debug_root: Path,
    dylib: str,
    timeout: int,
) -> None:
    """Attach the manual evidence mode without inventing recorder variants."""
    canonical = selection.canonical
    result["canonicalTotalCount"] = len(canonical.occurrences)
    result["manualReplacementCount"] = len(selection.entries)
    if not selection.entries:
        result["manualOverlay"] = None
        return

    module_slug = _sanitize_stem(
        canonical.module.removeprefix("Mathlib/").removesuffix(".lean")
    )
    module_root = debug_root / module_slug
    canonical_path = _copy_at_module_root(
        module_root / "canonical", canonical.module, canonical.source
    )
    final_path = Path(str(result["materializedPath"])).resolve()
    final_source = final_path.read_bytes()
    canonical_oracle = run_declaration_oracle(
        canonical.module,
        canonical_path,
        final_path,
        module_root / "canonical-oracle",
        dylib,
        timeout,
    )

    manual_records: list[dict[str, Any]] = []
    cumulative_delta = 0
    for entry in selection.entries:
        rendered = manual_overrides.render(entry, canonical.source)
        start, end = int(entry["startByte"]), int(entry["endByte"])
        effective_start = start + cumulative_delta
        effective_end = effective_start + len(rendered)
        if selection.effective.source[effective_start:effective_end] != rendered:
            raise RuntimeError(
                f"manual overlay rendered bytes changed for {entry['occurrence']}"
            )
        if rendered not in final_source:
            raise RuntimeError(
                f"manual overlay final composite dropped original comments for "
                f"{entry['occurrence']}"
            )
        manual_records.append({
            "canonicalId": str(entry["occurrence"]),
            "kind": next(
                str(item["kind"]) for item in canonical.occurrences
                if str(item["id"]) == str(entry["occurrence"])
            ),
            "source": str(entry["source"]),
            "canonicalStartByte": start,
            "canonicalEndByte": end,
            "effectiveStartByte": effective_start,
            "effectiveEndByte": effective_end,
            "replacementSha256": sha256(str(entry["replacement"]).encode("utf-8")),
            "renderedSha256": sha256(rendered),
        })
        cumulative_delta += len(rendered) - (end - start)

    manual_ids = [str(item["canonicalId"]) for item in manual_records]
    mapped_canonical = [str(item["canonicalId"]) for item in selection.mappings]
    mapped_effective = [str(item["effectiveId"]) for item in selection.mappings]
    canonical_ids = [str(item["id"]) for item in canonical.occurrences]
    ordinary_result_ids = [str(item["occurrence"]) for item in result["occurrenceResults"]]
    if len(set(manual_ids + mapped_canonical)) != len(canonical_ids) or set(
        manual_ids + mapped_canonical
    ) != set(canonical_ids):
        raise RuntimeError(
            f"manual overlay does not partition canonical occurrences in {canonical.module}"
        )
    if ordinary_result_ids != mapped_effective:
        raise RuntimeError(
            f"manual overlay effective mapping order disagrees with recorder results in "
            f"{canonical.module}"
        )
    if set(manual_ids) & set(mapped_effective):
        raise RuntimeError(
            f"manual overlay canonical IDs leaked into recorder evidence in {canonical.module}"
        )

    result["manualOverlay"] = {
        "identity": overlay.identity(),
        "canonicalSource": {
            "path": str(canonical_path.resolve()), "sha256": sha256(canonical.source)
        },
        "effectiveBase": {
            "path": str(Path(str(result["originalPath"])).resolve()),
            "sha256": str(result["originalHash"]),
        },
        "finalComposite": {
            "path": str(final_path), "sha256": sha256(final_source)
        },
        "manualIds": manual_ids,
        "manualReplacements": manual_records,
        "ordinaryOccurrenceMap": list(selection.mappings),
        "canonicalOracleInvocation": {
            "path": str((module_root / "canonical-oracle/oracle-invocation.json").resolve()),
            "sha256": sha256(
                (module_root / "canonical-oracle/oracle-invocation.json").read_bytes()
            ),
        },
        "canonicalDeclarationOracle": canonical_oracle,
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
        "manualOverlay",
        "canonicalTotalCount",
        "manualReplacementCount",
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
        "recordingMode",
        "runtime",
        "runtimeSha256",
        "recordingInvocation",
        "recordingLog",
        "replayInvocation",
        "oracleInvocation",
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
        "manualOverlay",
        "canonicalTotalCount",
        "manualReplacementCount",
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
        "canonicalTotalCount",
        "manualReplacementCount",
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
MANUAL_MODULE_FIELDS = frozenset(
    {
        "identity",
        "canonicalSource",
        "effectiveBase",
        "finalComposite",
        "manualIds",
        "manualReplacements",
        "ordinaryOccurrenceMap",
        "canonicalOracleInvocation",
        "canonicalDeclarationOracle",
    }
)
MANUAL_REPLACEMENT_FIELDS = frozenset(
    {
        "canonicalId",
        "kind",
        "source",
        "canonicalStartByte",
        "canonicalEndByte",
        "effectiveStartByte",
        "effectiveEndByte",
        "replacementSha256",
        "renderedSha256",
    }
)
MANUAL_MAPPING_FIELDS = frozenset(
    {
        "canonicalId",
        "effectiveId",
        "kind",
        "source",
        "canonicalStartByte",
        "canonicalEndByte",
        "effectiveStartByte",
        "effectiveEndByte",
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


def _validate_invocation_ref(
    ref: object, label: str, expected_path: Path, expected_module: str,
    expected_mode: str | None, source_fields: dict[str, str], *,
    expected_kind: str, expected_command: list[str], expected_runtime: str,
    expected_timeout: int,
) -> str:
    """Authenticate a prelaunch receipt against independently reconstructed inputs."""
    value = _validate_hash_ref(ref, label)
    if value["path"] != str(expected_path.resolve()):
        raise RuntimeError(f"{label}.path is not the expected durable sidecar")
    data = _read_evidence_file(value["path"], expected_path, label)
    _validate_evidence_hash(data, value["sha256"], label)
    try:
        sidecar = json.loads(data)
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise RuntimeError(f"{label} is not valid JSON") from error
    fields = {"kind", "module", "command", "cwd", "nonce", "timeoutSeconds",
              "runtime", "runtimeSha256", "recordingMode"}
    if expected_kind == "boundary_oracle_invocation_v1":
        fields.update({"stockSource", "stockSourceSha256", "appliedSource", "appliedSourceSha256"})
    elif expected_kind == "boundary_compiler_invocation_v1":
        fields.update({"source", "sourceSha256"})
    else:
        raise ValueError(f"unknown invocation kind: {expected_kind}")
    sidecar = _exact_fields(sidecar, frozenset(fields), label)
    if sidecar["kind"] != expected_kind:
        raise RuntimeError(f"{label}.kind is invalid")
    if sidecar["module"] != expected_module or sidecar["recordingMode"] != expected_mode:
        raise RuntimeError(f"{label} module or recording mode disagrees")
    for field, expected in source_fields.items():
        if sidecar[field] != expected:
            raise RuntimeError(f"{label}.{field} disagrees with durable source")
    if sidecar["command"] != expected_command:
        raise RuntimeError(f"{label}.command disagrees with reconstructed command")
    runtime_data = _read_evidence_file(sidecar["runtime"], Path(expected_runtime), f"{label} runtime")
    if sidecar["runtime"] != expected_runtime or sidecar["cwd"] != str(ROOT):
        raise RuntimeError(f"{label} runtime or cwd identity mismatch")
    _validate_evidence_hash(runtime_data, sidecar["runtimeSha256"], f"{label} runtime")
    nonce = sidecar["nonce"]
    if not isinstance(nonce, str) or re.fullmatch(r"[A-Za-z0-9_-]{43}", nonce) is None:
        raise RuntimeError(f"{label}.nonce is not a production compiler nonce")
    if (type(expected_timeout) is not int or expected_timeout <= 0 or
            type(sidecar["timeoutSeconds"]) is not int or sidecar["timeoutSeconds"] != expected_timeout):
        raise RuntimeError(f"{label}.timeoutSeconds disagrees")
    return nonce


def _validate_module_invocations(
    module_report: dict[str, Any], item: SelectedModule, module_root: Path,
    timeout: int, reports: list[object],
) -> dict[str, str]:
    """Join exact prelaunch identities to durable logs and their parsed artifacts."""
    shared_runtime = str(_shared_runtime_path())
    if module_report["runtime"] != shared_runtime:
        raise RuntimeError(f"{item.module} runtime path mismatch")
    _validate_evidence_hash(_shared_runtime_path().read_bytes(), module_report["runtimeSha256"],
                            f"{item.module} shared runtime")
    paths = {label: (module_root / label / item.module).resolve()
             for label in ("original", "instrumented", "materialized")}
    source_hashes = {}
    for label in paths:
        data = _read_evidence_file(str(paths[label]), paths[label], f"{item.module} {label}")
        digest = module_report[label + "Hash"]
        _validate_evidence_hash(data, digest, f"{item.module} {label}")
        source_hashes[label] = digest
    mode = module_report["recordingMode"]
    if mode not in {"stock", "applied"}:
        raise RuntimeError(f"{item.module} recording mode is invalid")
    compiler = "boundary_compiler_invocation_v1"
    expected = {
        "recording": (compiler, mode, shared_runtime,
            _compiler_command(paths["instrumented"], shared_runtime),
            {"source": str(paths["instrumented"]), "sourceSha256": source_hashes["instrumented"]}),
        "replay": (compiler, None, shared_runtime,
            _compiler_command(paths["materialized"], shared_runtime),
            {"source": str(paths["materialized"]), "sourceSha256": source_hashes["materialized"]}),
        "oracle": ("boundary_oracle_invocation_v1", None, str(_oracle_runtime_path()),
            _oracle_command(item.compiled_module, paths["original"], paths["materialized"]),
            {"stockSource": str(paths["original"]), "stockSourceSha256": source_hashes["original"],
             "appliedSource": str(paths["materialized"]), "appliedSourceSha256": source_hashes["materialized"]}),
    }
    nonces = {}
    for label, (kind, recording_mode, runtime, command, sources) in expected.items():
        nonces[label] = _validate_invocation_ref(
            module_report[label + "Invocation"], f"{item.module} {label}Invocation",
            module_root / (label + "-invocation.json"), item.compiled_module,
            recording_mode, sources, expected_kind=kind, expected_command=command,
            expected_runtime=runtime, expected_timeout=timeout,
        )
    if len(set(nonces.values())) != 3:
        raise RuntimeError(f"{item.module} invocation nonces are not unique")
    if nonces["replay"] != module_report["replayGuard"]["nonce"]:
        raise RuntimeError(f"{item.module} replay invocation nonce differs from log guard")
    if nonces["oracle"] != module_report["declarationOracle"]["replayGuard"]["nonce"]:
        raise RuntimeError(f"{item.module} oracle invocation nonce differs from log guard")
    logs = {
        "recording": (module_report["recordingLog"], "instrumented.log"),
        "replay": (module_report["replayGuard"], "materialized.log"),
        "oracle": (module_report["declarationOracle"], "declaration-oracle.log"),
    }
    for label, (ref, filename) in logs.items():
        data = _read_evidence_file(ref["path"], module_root / filename, f"{item.module} {label} log")
        _validate_evidence_hash(data, ref["sha256"], f"{item.module} {label} log")
        text = data.decode("utf-8")
        check_recording_abort_markers(text, expected_nonce=nonces[label], expected_module=item.compiled_module)
        check_replay_abort_markers(text, expected_nonce=nonces[label], expected_module=item.compiled_module)
        reject_compiler_sorry_warning(text, f"{item.module} {label} log")
        if label == "recording" and parse_framed_json_lines(
            text, marker=ARTIFACT_MARKER, expected_nonce=nonces[label],
            label=f"{item.module} recording artifacts",
        ) != reports:
            raise RuntimeError(f"{item.module} recording log artifacts differ from durable report")
    return nonces


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


def _validate_overlay_identity(value: object, label: str) -> dict[str, object]:
    identity = _exact_fields(
        value, frozenset({"kind", "schema", "database", "environment", "counts"}), label
    )
    if identity["kind"] != "simp_manual_overlay" or identity["schema"] != 2:
        raise RuntimeError(f"{label} has an unsupported identity")
    database = _exact_fields(
        identity["database"], frozenset({"sha256", "schema", "environment"}),
        f"{label}.database"
    )
    digest = _require_string(database["sha256"], f"{label}.database.sha256")
    if len(digest) != 64 or any(ch not in "0123456789abcdef" for ch in digest):
        raise RuntimeError(f"{label}.database.sha256 is invalid")
    _require_int(database["schema"], f"{label}.database.schema", nonnegative=True)
    environment = _exact_fields(
        identity["environment"], frozenset({"mathlibCommit", "lean"}),
        f"{label}.environment",
    )
    _require_string(environment["mathlibCommit"], f"{label}.environment.mathlibCommit")
    lean = _exact_fields(
        environment["lean"], frozenset({"version", "commit"}), f"{label}.environment.lean"
    )
    _require_string(lean["version"], f"{label}.environment.lean.version")
    _require_string(lean["commit"], f"{label}.environment.lean.commit")
    if database["environment"] != environment:
        raise RuntimeError(f"{label}.database.environment disagrees")
    counts = _exact_fields(
        identity["counts"],
        frozenset({"modules", "canonicalOccurrences", "manualOverrides", "untouchedOccurrences"}),
        f"{label}.counts",
    )
    for field in counts:
        _require_int(counts[field], f"{label}.counts.{field}", nonnegative=True)
    if counts["canonicalOccurrences"] != counts["manualOverrides"] + counts["untouchedOccurrences"]:
        raise RuntimeError(f"{label}.counts do not partition canonical occurrences")
    return identity


def _validate_manual_module(
    value: object, label: str, compiled_module: str,
    ordinary_results: list[dict[str, Any]], canonical_total: int, manual_count: int,
) -> dict[str, object]:
    overlay = _exact_fields(value, MANUAL_MODULE_FIELDS, label)
    _validate_overlay_identity(overlay["identity"], f"{label}.identity")
    canonical = _validate_hash_ref(overlay["canonicalSource"], f"{label}.canonicalSource")
    effective = _validate_hash_ref(overlay["effectiveBase"], f"{label}.effectiveBase")
    final = _validate_hash_ref(overlay["finalComposite"], f"{label}.finalComposite")
    if len({canonical["path"], effective["path"], final["path"]}) != 3:
        raise RuntimeError(f"{label} source evidence paths must be distinct")
    manual_ids = _validate_string_list(overlay["manualIds"], f"{label}.manualIds")
    replacements = overlay["manualReplacements"]
    if not isinstance(replacements, list):
        raise RuntimeError(f"{label}.manualReplacements must be an array")
    checked_replacements = []
    for index, raw in enumerate(replacements):
        replacement = _exact_fields(raw, MANUAL_REPLACEMENT_FIELDS, f"{label}.manualReplacements[{index}]")
        for field in ("canonicalId", "kind", "source", "replacementSha256", "renderedSha256"):
            _require_string(replacement[field], f"{label}.manualReplacements[{index}].{field}")
        for field in ("canonicalStartByte", "canonicalEndByte", "effectiveStartByte", "effectiveEndByte"):
            _require_int(replacement[field], f"{label}.manualReplacements[{index}].{field}", nonnegative=True)
        if replacement["canonicalEndByte"] <= replacement["canonicalStartByte"] or replacement["effectiveEndByte"] <= replacement["effectiveStartByte"]:
            raise RuntimeError(f"{label}.manualReplacements[{index}] has an empty range")
        checked_replacements.append(replacement)
    if manual_ids != [str(item["canonicalId"]) for item in checked_replacements]:
        raise RuntimeError(f"{label}.manualIds disagree with manual replacements")
    if len(manual_ids) != len(set(manual_ids)) or len(manual_ids) != manual_count:
        raise RuntimeError(f"{label} manual replacement identities/count disagree")

    mappings = overlay["ordinaryOccurrenceMap"]
    if not isinstance(mappings, list):
        raise RuntimeError(f"{label}.ordinaryOccurrenceMap must be an array")
    checked_mappings = []
    for index, raw in enumerate(mappings):
        mapping = _exact_fields(raw, MANUAL_MAPPING_FIELDS, f"{label}.ordinaryOccurrenceMap[{index}]")
        for field in ("canonicalId", "effectiveId", "kind", "source"):
            _require_string(mapping[field], f"{label}.ordinaryOccurrenceMap[{index}].{field}")
        for field in ("canonicalStartByte", "canonicalEndByte", "effectiveStartByte", "effectiveEndByte"):
            _require_int(mapping[field], f"{label}.ordinaryOccurrenceMap[{index}].{field}", nonnegative=True)
        checked_mappings.append(mapping)
    canonical_ids = manual_ids + [str(item["canonicalId"]) for item in checked_mappings]
    if len(checked_mappings) != len(ordinary_results):
        raise RuntimeError(f"{label} ordinary mapping count disagrees with recorder results")
    effective_ids = [str(item["effectiveId"]) for item in checked_mappings]
    if len(canonical_ids) != canonical_total or len(canonical_ids) != len(set(canonical_ids)):
        raise RuntimeError(f"{label} canonical mapping is not a partition")
    if len(effective_ids) != len(set(effective_ids)):
        raise RuntimeError(f"{label} effective mapping contains duplicate IDs")
    if effective_ids != [str(item["occurrence"]) for item in ordinary_results]:
        raise RuntimeError(f"{label} effective mapping disagrees with occurrence results")
    if set(manual_ids) & set(effective_ids):
        raise RuntimeError(f"{label} manual IDs leaked into recorder occurrence results")
    _validate_hash_ref(
        overlay["canonicalOracleInvocation"], f"{label}.canonicalOracleInvocation"
    )
    _validate_oracle_wrapper(
        overlay["canonicalDeclarationOracle"], f"{label}.canonicalDeclarationOracle",
        compiled_module,
    )
    return overlay


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
    recording_mode = _require_string(module["recordingMode"], f"{label}.recordingMode")
    if recording_mode not in {"stock", "applied"}:
        raise RuntimeError(f"{label}.recordingMode is invalid: {recording_mode!r}")
    _require_string(module["runtime"], f"{label}.runtime")
    _require_string(module["runtimeSha256"], f"{label}.runtimeSha256")
    for field in ("recordingInvocation", "replayInvocation", "oracleInvocation", "recordingLog"):
        _validate_hash_ref(module[field], f"{label}.{field}")
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

    canonical_total_count = _require_int(
        module["canonicalTotalCount"], f"{label}.canonicalTotalCount", nonnegative=True
    )
    manual_replacement_count = _require_int(
        module["manualReplacementCount"],
        f"{label}.manualReplacementCount",
        nonnegative=True,
    )
    total_count = _require_int(module["totalCount"], f"{label}.totalCount", nonnegative=True)
    if module["manualOverlay"] is None:
        if manual_replacement_count != 0 or canonical_total_count != total_count:
            raise RuntimeError(f"{label} null manual overlay has inconsistent counts")
    elif not isinstance(module["manualOverlay"], dict):
        raise RuntimeError(f"{label}.manualOverlay must be null or an object")
    if canonical_total_count != total_count + manual_replacement_count:
        raise RuntimeError(f"{label} canonical/manual occurrence counts disagree")
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
    if module["manualOverlay"] is not None:
        checked_overlay = _validate_manual_module(
            module["manualOverlay"], f"{label}.manualOverlay", expected_compiled,
            occurrence_results, canonical_total_count, manual_replacement_count,
        )
        if checked_overlay["effectiveBase"] != module["original"]:
            raise RuntimeError(f"{label}.manualOverlay effective base disagrees with original")
        if checked_overlay["finalComposite"] != {
            "path": module["materialized"]["path"],
            "sha256": module["materialized"]["sha256"],
        }:
            raise RuntimeError(f"{label}.manualOverlay final composite disagrees with materialized")

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
    """Validate the exact current structure and internal count coherence.

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
        "canonicalTotalCount": sum(int(module["canonicalTotalCount"]) for module in modules),
        "manualReplacementCount": sum(
            int(module["manualReplacementCount"]) for module in modules
        ),
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
    if value["manualOverlay"] is None:
        if totals["manualReplacementCount"] != 0 or any(
            module["manualOverlay"] is not None for module in modules
        ):
            raise RuntimeError("null top-level manual overlay disagrees with modules")
    elif not isinstance(value["manualOverlay"], dict):
        raise RuntimeError("materialization shard report.manualOverlay must be null or an object")
    else:
        top_overlay = _validate_overlay_identity(
            value["manualOverlay"], "materialization shard report.manualOverlay"
        )
        if top_overlay["environment"] != {
            "mathlibCommit": value["mathlibCommit"], "lean": value["lean"]
        }:
            raise RuntimeError("top-level manual overlay environment disagrees with report")
        for module in modules:
            module_overlay = module["manualOverlay"]
            if module_overlay is not None and module_overlay["identity"] != top_overlay:
                raise RuntimeError("module manual overlay identity disagrees with top-level identity")
            selected_counts = {
                "canonicalOccurrences": int(module["canonicalTotalCount"]),
                "manualOverrides": int(module["manualReplacementCount"]),
                "untouchedOccurrences": int(module["totalCount"]),
            }
            for field, selected_count in selected_counts.items():
                if selected_count > int(top_overlay["counts"][field]):
                    raise RuntimeError(
                        f"modules[{module_names.index(module['module'])}] {field} "
                        "exceeds global manual overlay identity"
                    )
        selected_counts = {
            "modules": len(modules),
            "canonicalOccurrences": totals["canonicalTotalCount"],
            "manualOverrides": totals["manualReplacementCount"],
            "untouchedOccurrences": totals["totalCount"],
        }
        for field, selected_count in selected_counts.items():
            if selected_count > int(top_overlay["counts"][field]):
                raise RuntimeError(
                    f"selected {field} exceeds global manual overlay identity"
                )
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
        "canonicalTotalCount": totals["canonicalTotalCount"],
        "manualReplacementCount": totals["manualReplacementCount"],
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
    recorded_input = Path(_require_string(path_value, f"{label}.path"))
    if recorded_input.is_symlink():
        raise RuntimeError(f"{label} evidence path is a symlink: {recorded_input}")
    recorded = recorded_input.resolve()
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


def verify_manual_overlay_evidence(
    module_report: dict[str, Any],
    overlay: manual_overlay.Overlay,
    module: str,
    timeout: int,
    *,
    debug_root: Path,
) -> None:
    """Reproduce manual evidence from the canonical DB and durable source files."""
    section = module_report.get("manualOverlay")
    entries = tuple(overlay.entries_by_module().get(module, ()))
    if not entries:
        if section is not None or module_report.get("manualReplacementCount") != 0:
            raise RuntimeError(f"{module} unexpectedly reports manual overlay evidence")
        return
    if not isinstance(section, dict) or section.get("identity") != overlay.identity():
        raise RuntimeError(f"{module} manual overlay identity mismatch")
    canonical_source = overlay.sources[module]
    effective_source = overlay.apply(module, canonical_source)
    refs = {
        "canonical": section["canonicalSource"],
        "effective": section["effectiveBase"],
        "final": section["finalComposite"],
    }
    module_root = (
        debug_root.resolve()
        / _sanitize_stem(module.removeprefix("Mathlib/").removesuffix(".lean"))
    )
    expected_source_paths = {
        "canonical": module_root / "canonical" / Path(*module.split("/")),
        "effective": module_root / "original" / Path(*module.split("/")),
        "final": module_root / "materialized" / Path(*module.split("/")),
    }
    data: dict[str, bytes] = {}
    for label, ref in refs.items():
        checked = _validate_hash_ref(ref, f"{module} manual {label}")
        data[label] = _read_evidence_file(
            checked["path"], expected_source_paths[label], f"{module} manual {label}"
        )
        _validate_evidence_hash(data[label], checked["sha256"], f"{module} manual {label}")
    if data["canonical"] != canonical_source or data["effective"] != effective_source:
        raise RuntimeError(f"{module} manual canonical/effective source is not reproducible")
    if refs["effective"] != module_report["original"] or refs["final"] != {
        "path": module_report["materialized"]["path"],
        "sha256": module_report["materialized"]["sha256"],
    }:
        raise RuntimeError(f"{module} manual source references disagree with module evidence")

    canonical_records = {str(item["id"]): item for item in overlay.modules[module]}
    expected_manual = []
    delta = 0
    for entry in entries:
        rendered = manual_overrides.render(entry, canonical_source)
        start, end = int(entry["startByte"]), int(entry["endByte"])
        effective_start = start + delta
        expected_manual.append({
            "canonicalId": str(entry["occurrence"]),
            "kind": str(canonical_records[str(entry["occurrence"])]["kind"]),
            "source": str(entry["source"]),
            "canonicalStartByte": start,
            "canonicalEndByte": end,
            "effectiveStartByte": effective_start,
            "effectiveEndByte": effective_start + len(rendered),
            "replacementSha256": sha256(str(entry["replacement"]).encode("utf-8")),
            "renderedSha256": sha256(rendered),
        })
        if rendered not in data["final"]:
            raise RuntimeError(f"{module} final composite dropped manual original comments")
        delta += len(rendered) - (end - start)
    if section["manualReplacements"] != expected_manual or section["manualIds"] != [
        str(entry["occurrence"]) for entry in entries
    ]:
        raise RuntimeError(f"{module} manual replacement report is not reproducible")

    expected_mappings = []
    for item in overlay.shifted_occurrences(module):
        expected_mappings.append({
            "canonicalId": str(item["canonicalId"]),
            "effectiveId": str(item["id"]),
            "kind": str(item["kind"]),
            "source": str(item["source"]),
            "canonicalStartByte": int(item["canonicalStartByte"]),
            "canonicalEndByte": int(item["canonicalEndByte"]),
            "effectiveStartByte": int(item["startByte"]),
            "effectiveEndByte": int(item["endByte"]),
        })
    if section["ordinaryOccurrenceMap"] != expected_mappings:
        raise RuntimeError(f"{module} ordinary shifted mapping is not reproducible")

    oracle = section["canonicalDeclarationOracle"]
    invocation = section["canonicalOracleInvocation"]
    canonical_path = expected_source_paths["canonical"]
    final_path = expected_source_paths["final"]
    invocation_path = module_root / "canonical-oracle" / "oracle-invocation.json"
    oracle_log_path = module_root / "canonical-oracle" / "declaration-oracle.log"
    oracle_report_path = module_root / "canonical-oracle" / "declaration-oracle-report.json"
    nonce = _validate_invocation_ref(
        invocation,
        f"{module} canonical oracle invocation",
        invocation_path,
        corpus.compiled_module_name(module),
        None,
        {
            "stockSource": str(canonical_path),
            "stockSourceSha256": str(refs["canonical"]["sha256"]),
            "appliedSource": str(final_path),
            "appliedSourceSha256": str(refs["final"]["sha256"]),
        },
        expected_kind="boundary_oracle_invocation_v1",
        expected_command=_oracle_command(
            corpus.compiled_module_name(module), canonical_path, final_path
        ),
        expected_runtime=str(_oracle_runtime_path()),
        expected_timeout=timeout,
    )
    if nonce != oracle["replayGuard"]["nonce"]:
        raise RuntimeError(f"{module} canonical oracle nonce disagrees with invocation")
    log_data = _read_evidence_file(
        oracle["path"], oracle_log_path, f"{module} canonical oracle log"
    )
    _validate_evidence_hash(log_data, oracle["sha256"], f"{module} canonical oracle log")
    log_text = log_data.decode("utf-8")
    check_replay_abort_markers(
        log_text, expected_nonce=nonce,
        expected_module=corpus.compiled_module_name(module),
    )
    parsed_log_report = _parse_declaration_oracle(
        log_text, corpus.compiled_module_name(module)
    )
    if parsed_log_report != oracle["report"]:
        raise RuntimeError(f"{module} canonical oracle log differs from embedded report")
    report_data = _read_evidence_file(
        oracle["reportPath"], oracle_report_path, f"{module} canonical oracle report"
    )
    _validate_evidence_hash(
        report_data, oracle["reportSha256"], f"{module} canonical oracle report"
    )
    if json.loads(report_data) != oracle["report"]:
        raise RuntimeError(f"{module} canonical oracle durable report disagrees")


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
    overlay: manual_overlay.Overlay | None = None,
) -> dict[str, object]:
    """Bind the current report schema to selected manifest and durable files."""
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

    # The overlay identity describes the complete manifest corpus, while this
    # report may contain only a selected module subset.  Bind the former to the
    # authenticated manifest and require only the selected counts below it.
    report_overlay = report["manualOverlay"]
    if overlay is None:
        if report_overlay is not None:
            raise RuntimeError("report contains manual overlay without authenticated database")
    else:
        manifest_binding = manifest.get("manualOverrides")
        if not isinstance(manifest_binding, dict):
            raise RuntimeError("manifest manualOverrides binding is invalid")
        expected_identity = overlay.identity()
        if manifest_binding != expected_identity["database"]:
            raise RuntimeError("manual overlay database is not bound to manifest")
        if report_overlay != expected_identity:
            raise RuntimeError("report manual overlay identity is not bound to manifest")
        global_counts = expected_identity["counts"]
        if global_counts != {
            "modules": manifest.get("moduleFileCount"),
            "canonicalOccurrences": manifest.get("occurrenceCount"),
            "manualOverrides": len(overlay.entries),
            "untouchedOccurrences": (
                manifest.get("occurrenceCount", -1) - len(overlay.entries)
            ),
        }:
            raise RuntimeError("manual overlay counts are not bound to manifest totals")

    runner_path = Path(__file__).resolve()
    runner_data = _read_evidence_file(report["runner"]["path"], runner_path, "runner")
    _validate_evidence_hash(runner_data, report["runner"]["sha256"], "runner")
    if report["runnerHash"] != sha256(runner_data):
        raise RuntimeError("report runnerHash does not match the executing runner")

    if report["selectedModules"] != [item.module for item in selected]:
        raise RuntimeError("report selectedModules differ from manifest selection")
    if len(report["modules"]) != len(selected):
        raise RuntimeError("report module count differs from manifest selection")
    if report_overlay is not None:
        global_counts = report_overlay["counts"]
        selected_counts = {
            "modules": len(selected),
            "canonicalOccurrences": int(report["canonicalTotalCount"]),
            "manualOverrides": int(report["manualReplacementCount"]),
            "untouchedOccurrences": int(report["totalCount"]),
        }
        for field, value in selected_counts.items():
            if value > int(global_counts[field]):
                raise RuntimeError(
                    f"selected {field} exceeds global manual overlay identity"
                )

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
            "recordingInvocation": module_root / "recording-invocation.json",
            "replayInvocation": module_root / "replay-invocation.json",
            "oracleInvocation": module_root / "oracle-invocation.json",
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
        recording_mode = module_report["recordingMode"]
        if recording_mode not in {"stock", "applied"}:
            raise RuntimeError(f"{item.module} has invalid recording mode")
        if instrumented_data != instrumented_source(
            item.source, item.replacement_roots, recording_mode=recording_mode
        ):
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
        _validate_module_invocations(module_report, item, module_root, timeout, reports)
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


def _capsule_manifest(
    capsule: Mapping[str, Any], selected_record: Mapping[str, Any],
) -> dict[str, Any]:
    identity = capsule.get("globalIdentity")
    if not isinstance(identity, Mapping):
        raise RuntimeError("capsule global identity is invalid")
    validate_capsule_global_identity(identity)
    manifest = dict(identity)
    manifest["modules"] = [dict(selected_record)]
    # The overlay loader receives a sparse module projection separately.  Its
    # global counts remain those of the authenticated full manifest for report
    # verification, while selected source validation uses the one record.
    manifest["moduleFileCount"] = identity.get("moduleFileCount")
    manifest["occurrenceCount"] = identity.get("occurrenceCount")
    return manifest


def validate_capsule_expectations(
    records: Mapping[str, Mapping[str, Any]],
    modules: Sequence[str],
    expect_total: int | None,
    expect_materialize: int | None,
) -> None:
    if expect_total is None and expect_materialize is None:
        return
    if len(modules) != 1:
        raise RuntimeError(
            "--expect-total/--expect-materialize are only valid for one selected module"
        )
    module = modules[0]
    record = records.get(module)
    if record is None:
        raise RuntimeError(f"capsule selected module is absent: {module}")
    occurrences = record.get("occurrences")
    if not isinstance(occurrences, list):
        raise RuntimeError("capsule selected record has invalid occurrences")
    materialize_count = sum(
        isinstance(item, Mapping) and item.get("action") == "materialize"
        for item in occurrences
    )
    if expect_total is not None and expect_total != len(occurrences):
        raise RuntimeError(
            f"--expect-total mismatch for {module}: expected {expect_total}, found {len(occurrences)}"
        )
    if expect_materialize is not None and expect_materialize != materialize_count:
        raise RuntimeError(
            f"--expect-materialize mismatch for {module}: expected {expect_materialize}, found {materialize_count}"
        )


def run_shard(args: argparse.Namespace) -> dict[str, Any]:
    manual_overrides_arg = getattr(args, "manual_overrides", None)
    capsule_arg = getattr(args, "capsule", None)
    capsule_hash_arg = getattr(args, "capsule_sha256", None)
    manifest_location = Path(args.manifest)
    if not manifest_location.is_absolute():
        manifest_location = ROOT / manifest_location
    # Resolve the real input before lexical cleanup checks: collapsing `..`
    # before following a directory symlink can select a different manifest.
    manifest_location = manifest_location.absolute()
    manifest_path = manifest_location.resolve()
    capsule_path: Path | None = None
    capsule: dict[str, Any] | None = None
    capsule_bytes: bytes | None = None
    if capsule_arg is not None:
        if not isinstance(capsule_hash_arg, str) or len(capsule_hash_arg) != 64:
            raise RuntimeError("--capsule requires a 64-character --capsule-sha256")
        capsule_location = Path(capsule_arg)
        if not capsule_location.is_absolute():
            capsule_location = ROOT / capsule_location
        capsule_location = capsule_location.absolute()
        capsule_path = capsule_location.resolve()
        capsule, capsule_bytes = read_manifest_capsule(capsule_path, expected_hash=capsule_hash_arg)
        if capsule.get("manifestPath") != str(manifest_path):
            raise RuntimeError("capsule is bound to another manifest path")
    # Invalidate the exact requested destination after cleanup safety checks,
    # before manifest validation or compiler work.  A failed rerun must not
    # leave a previous success that a consumer could mistake for the current run.
    output_path = resolve_output_path(args.output, manifest_path)
    debug_root = debug_root_for(output_path)
    if manual_overrides_arg is not None:
        manual_location = Path(manual_overrides_arg).absolute()
        manual_path = manual_location.resolve()
        if (
            manual_location == output_path
            or manual_path == output_path
            or manual_location.is_relative_to(debug_root)
            or manual_path.is_relative_to(debug_root)
        ):
            raise RuntimeError(
                "manual override database must be outside materializer output/cleanup paths"
            )
    protected_inputs: list[Path] = []
    if capsule_path is not None:
        protected_inputs.extend((capsule_path, capsule_location))
    if manual_overrides_arg is not None:
        protected_inputs.extend((Path(manual_overrides_arg).resolve(), manual_location))
    validate_cleanup_targets(
        manifest_path,
        output_path,
        debug_root,
        manifest_location=manifest_location,
        protected_inputs=protected_inputs,
    )
    invalidate_output(output_path)
    clear_debug_root(debug_root)
    if not manifest_path.is_file():
        raise RuntimeError(f"manifest does not exist: {manifest_path}")
    if capsule is not None:
        _manifest_hash, _manifest_size, captured = stream_manifest_capsule(
            manifest_path, capsule, list(args.module)
        )
        if not args.module or len(set(args.module)) != len(args.module):
            raise RuntimeError("selected modules must be nonempty and unique")
        selected_records = capsule.get("selectedModules")
        if not isinstance(selected_records, list):
            raise RuntimeError("capsule selected module projection does not match request")
        by_module: dict[str, Mapping[str, Any]] = {}
        for raw in selected_records:
            if not isinstance(raw, Mapping) or not isinstance(raw.get("module"), str):
                raise RuntimeError("capsule selected module projection is invalid")
            module = str(raw["module"])
            if module not in args.module:
                continue
            try:
                record = json.loads(captured[module])
            except (KeyError, json.JSONDecodeError) as error:
                raise RuntimeError(f"capsule selected record is not valid JSON: {module}") from error
            if not isinstance(record, Mapping):
                raise RuntimeError(f"capsule record is invalid: {module}")
            by_module[module] = record
        if set(by_module) != set(args.module):
            raise RuntimeError("capsule selected modules differ from request")
        validate_capsule_expectations(
            by_module, list(args.module), args.expect_total, args.expect_materialize
        )
        selected_records_by_name = by_module
        selected_modules = []
        for module in args.module:
            source_path = (MATHLIB / Path(*module.split("/"))).resolve()
            try:
                source_path.relative_to(MATHLIB.resolve())
            except ValueError as error:
                raise RuntimeError(f"capsule source escapes pinned Mathlib: {module}") from error
            selected_modules.append(
                validate_capsule_module_record(
                    module, selected_records_by_name[module], source_path,
                )
            )
        # Keep the bytes for the evidence protocol after the streaming
        # authentication pass.  No global JSON decode occurs in this path.
        manifest = _capsule_manifest(capsule, selected_records_by_name[args.module[0]])
        manifest["modules"] = [selected_records_by_name[module] for module in args.module]
        manifest_bytes = manifest_path.read_bytes()
        if (
            len(manifest_bytes) != capsule["manifestSize"]
            or sha256(manifest_bytes) != capsule["manifestHash"]
        ):
            raise RuntimeError("manifest reread does not match authenticated capsule")
    else:
        manifest_bytes = manifest_path.read_bytes()
        try:
            manifest = json.loads(manifest_bytes)
        except json.JSONDecodeError as error:
            raise RuntimeError(f"manifest is not valid JSON: {manifest_path}") from error
        if not isinstance(manifest, dict):
            raise RuntimeError("manifest root must be an object")
        if not args.module or len(set(args.module)) != len(args.module):
            raise RuntimeError("selected modules must be nonempty and unique")

    verify_implementation_hashes(manifest)
    if manifest.get("allowDirty") is not False:
        raise RuntimeError("boundary materialization requires allowDirty=false")
    corpus.assert_repository(
        _require_string(manifest.get("repositoryCommit"), "manifest repositoryCommit"),
        False,
    )
    provenance = verify_environment(manifest, args.timeout)
    if capsule is None:
        canonical_selected = validate_manifest_selection(
            manifest,
            list(args.module),
            expect_total=args.expect_total,
            expect_materialize=args.expect_materialize,
        )
        verify_selected_classifications(canonical_selected, args.timeout)
    else:
        canonical_selected = selected_modules
        # The capsule authenticates the global manifest projection; retain the
        # selected module's independent inventory/scope check from the normal
        # path without paying to revalidate unselected modules.
        verify_selected_classifications(canonical_selected, args.timeout)
    overlay = None
    if manual_overrides_arg is not None:
        if capsule is None:
            overlay = manual_overlay.load_overlay(
                manifest_path, Path(manual_overrides_arg), source_root=MATHLIB
            )
        else:
            manual_records = capsule.get("manualModules", [])
            if not isinstance(manual_records, list):
                raise RuntimeError("capsule manual module projection is invalid")
            record_map: dict[str, Mapping[str, Any]] = {}
            for item in manual_records:
                if not isinstance(item, Mapping) or not isinstance(item.get("module"), str):
                    raise RuntimeError("capsule manual module projection is invalid")
                module = str(item["module"])
                try:
                    record = json.loads(captured[module])
                except (KeyError, json.JSONDecodeError) as error:
                    raise RuntimeError(f"capsule manual record is invalid: {module}") from error
                if not isinstance(record, Mapping):
                    raise RuntimeError(f"capsule manual record is invalid: {module}")
                record_map[module] = record
            sparse = dict(manifest)
            sparse["modules"] = list(record_map.values())
            overlay = manual_overlay._load_overlay_projected(
                manifest_path, Path(manual_overrides_arg), source_root=MATHLIB,
                manifest_value=sparse, manifest_bytes=manifest_bytes,
                module_records=record_map,
            )
            if overlay.identity() != capsule.get("manualOverlay"):
                raise RuntimeError("manual overlay identity does not match capsule")
    selections = (
        [
            prepare_overlay_selection(item, overlay, debug_root, args.timeout)
            for item in canonical_selected
        ]
        if overlay is not None
        else [OverlaySelection(item, item, (), ()) for item in canonical_selected]
    )
    selected = [item.effective for item in selections]
    runner_path = Path(__file__).resolve()
    runner_hash = sha256(runner_path.read_bytes())
    dylib = _query_dynamic_library(args.timeout, debug_root)

    module_results: list[dict[str, Any]] = []
    for selection in selections:
        module_result = _module_result(
            selection.effective, debug_root, dylib, args.timeout
        )
        if overlay is not None:
            attach_manual_overlay_evidence(
                module_result, selection, overlay, debug_root, dylib, args.timeout
            )
        module_results.append(module_result)

    # Recheck the immutable inputs after all compiler invocations.  A report is
    # only published if the same pinned environment and source set survived.
    if capsule is not None:
        if capsule_path is None or capsule_bytes is None:
            raise RuntimeError("capsule state is incomplete")
        try:
            current_capsule_bytes = capsule_path.read_bytes()
        except OSError as error:
            raise RuntimeError(f"cannot reread manifest capsule: {error}") from error
        if current_capsule_bytes != capsule_bytes:
            raise RuntimeError("manifest_capsule_changed_during_run")
        stream_manifest_capsule(manifest_path, capsule, list(args.module))
    elif manifest_path.read_bytes() != manifest_bytes:
        raise RuntimeError("manifest_changed_during_run")
    verify_implementation_hashes(manifest)
    final_provenance = verify_environment(manifest, args.timeout)
    if final_provenance != provenance:
        raise RuntimeError("pinned_environment_changed_during_run")
    for item in canonical_selected:
        current_source = item.source_path.read_bytes()
        if current_source != item.source:
            raise RuntimeError(f"selected Mathlib source changed during run: {item.module}")
    if overlay is not None:
        if capsule is None:
            refreshed_overlay = manual_overlay.load_overlay(
                manifest_path, Path(manual_overrides_arg), source_root=MATHLIB
            )
        else:
            manual_records = capsule.get("manualModules", [])
            if not isinstance(manual_records, list):
                raise RuntimeError("capsule manual module projection is invalid")
            record_map: dict[str, Mapping[str, Any]] = {}
            for item in manual_records:
                if not isinstance(item, Mapping) or not isinstance(item.get("module"), str):
                    raise RuntimeError("capsule manual module projection is invalid")
                module = str(item["module"])
                try:
                    record = json.loads(captured[module])
                except (KeyError, json.JSONDecodeError) as error:
                    raise RuntimeError(f"capsule manual record is invalid: {module}") from error
                if not isinstance(record, Mapping):
                    raise RuntimeError(f"capsule manual record is invalid: {module}")
                record_map[module] = record
            sparse = dict(manifest)
            sparse["modules"] = list(record_map.values())
            refreshed_overlay = manual_overlay._load_overlay_projected(
                manifest_path, Path(manual_overrides_arg), source_root=MATHLIB,
                manifest_value=sparse, manifest_bytes=manifest_bytes,
                module_records=record_map,
            )
        if refreshed_overlay.identity() != overlay.identity():
            raise RuntimeError("manual_override_database_changed_during_run")

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
    canonical_total_count = sum(
        int(module["canonicalTotalCount"]) for module in module_results
    )
    manual_replacement_count = sum(
        int(module["manualReplacementCount"]) for module in module_results
    )
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
        "selectedModules": [item.module for item in canonical_selected],
        "modules": module_results,
        "manualOverlay": overlay.identity() if overlay is not None else None,
        "canonicalTotalCount": canonical_total_count,
        "manualReplacementCount": manual_replacement_count,
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
            "canonicalTotalCount": canonical_total_count,
            "manualReplacementCount": manual_replacement_count,
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
        overlay=overlay,
    )
    if overlay is not None:
        for module_report in module_results:
            verify_manual_overlay_evidence(
                module_report, overlay, str(module_report["module"]), args.timeout,
                debug_root=debug_root,
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
    result.add_argument(
        "--manual-overrides",
        help="authenticated manual override database composed before ordinary recording",
    )
    result.add_argument(
        "--capsule",
        help="authenticated compact manifest projection produced by campaign-worker",
    )
    result.add_argument(
        "--capsule-sha256",
        help="expected SHA-256 of --capsule",
    )
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
