#!/usr/bin/env python3
"""Verify a freshly generated whole-Mathlib simp boundary manifest.

The default pass is deliberately independent of manifest generation: it checks
the JSON contract, repository/package/toolchain provenance (when enabled),
every source and occurrence byte range, and all aggregate partitions.  It does
not rerun Lean's parser.  ``--recompute`` opts into that expensive second
layer and compares the producer's syntax records with a fresh inventory.
"""

from __future__ import annotations

import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any, Iterable

import check_simp_engine_boundary_scope as scope
import simp_engine_inventory as inventory
import simp_engine_boundary_corpus as corpus


SCHEMA = 2
KIND = "simp_engine_boundary_manifest"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
HEX16 = re.compile(r"^[0-9a-f]{16}$")
MANUAL_OVERRIDE_SCHEMA = 1

TOP_LEVEL_FIELDS = frozenset(
    {
        "reportSchema", "kind", "allowDirty", "allowUnresolved",
        "repositoryCommit", "mathlibCommit", "lean", "modulePrefix",
        "moduleFileCount", "inventoriedModuleCount", "occurrenceCount",
        "nestedOccurrenceCount", "duplicateSyntaxRecords",
        "duplicateScopeSyntaxRecords", "fullFrontendFallbacks",
        "scopeFrontendFallbacks", "scopeProbe", "countsByExecutionRole",
        "countsByDeclarationKind", "countsByAction", "implementationHashes",
        "manualOverrides", "modules",
    }
)
OPTIONAL_TOP_LEVEL_FIELDS = frozenset(
    {"selfHash", "manifestHash", "packageIdentity", "packageIdentities"}
)
MODULE_FIELDS = frozenset(
    {
        "module", "compiledModule", "moduleHash", "sourceHash",
        "duplicateSyntaxRecords", "duplicateScopeSyntaxRecords", "occurrences",
    }
)
OCCURRENCE_FIELDS = frozenset(
    {
        "id", "kind", "source", "startByte", "endByte", "line", "column",
        "syntaxKind", "ancestors", "commandKind", "commandStartByte",
        "commandEndByte", "scopePaths", "executionRole", "declarationKind",
        "action", "reason", "declarations",
    }
)
DECLARATION_FIELDS = frozenset(
    {
        "module", "name", "startByte", "endByte", "selectionStartByte",
        "selectionEndByte", "isProof",
    }
)
SCOPE_PATH_FIELDS = frozenset(
    {"ancestors", "commandKind", "commandStartByte", "commandEndByte"}
)
EVIDENCE_FIELDS = frozenset(
    {"status", "executionCount", "callers", "module", "scheduling"}
)
CALLER_FIELDS = frozenset({"caller", "executionCount", "isProofDeclaration"})


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def _error(label: str, detail: str) -> RuntimeError:
    return RuntimeError(f"manifest {label}: {detail}")


def _fields(value: object, required: Iterable[str], label: str, optional: Iterable[str] = ()) -> None:
    if not isinstance(value, dict):
        raise _error(label, "must be an object")
    required_set, optional_set = set(required), set(optional)
    missing = required_set - set(value)
    extra = set(value) - required_set - optional_set
    if missing or extra:
        raise _error(label, f"fields changed: missing={sorted(missing)}, extra={sorted(extra)}")


def _string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise _error(label, "must be a nonempty string")
    return value


def _int(value: object, label: str, *, positive: bool = False) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < (1 if positive else 0):
        qualifier = "positive" if positive else "nonnegative"
        raise _error(label, f"must be a {qualifier} integer")
    return value


def _hash(value: object, label: str, pattern: re.Pattern[str] = HEX64) -> str:
    result = _string(value, label)
    if not pattern.fullmatch(result):
        raise _error(label, "must be a lowercase hexadecimal digest")
    return result


def _strings(value: object, label: str, *, nonempty: bool = True) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) and (item or not nonempty) for item in value):
        raise _error(label, "must be an array of strings")
    return list(value)


def _safe_module_path(mathlib_root: Path, module: str) -> Path:
    # PurePosix validation prevents platform-specific separators and traversal
    # before resolve() handles symlinks.
    parts = module.split("/")
    if (
        not module.startswith("Mathlib/")
        or not module.endswith(".lean")
        or "\\" in module
        or any(part in {"", ".", ".."} for part in parts)
    ):
        raise _error("module path", f"invalid pinned Mathlib path {module!r}")
    root = mathlib_root.resolve()
    candidate = (root / Path(*parts)).resolve()
    try:
        candidate.relative_to(root)
    except ValueError as exc:
        raise _error("module path", f"escapes pinned Mathlib: {module}") from exc
    if not candidate.is_file():
        raise _error("module path", f"source is missing: {module}")
    return candidate


def _compiled_module(module: str) -> str:
    return module[:-5].replace("/", ".")


def _line_column(source: bytes, offset: int) -> tuple[int, int]:
    try:
        prefix = source[:offset].decode("utf-8")
    except UnicodeDecodeError as exc:
        raise _error("occurrence", "range is not on a UTF-8 boundary") from exc
    line = prefix.count("\n") + 1
    column = len(prefix.rsplit("\n", 1)[-1])
    return line, column


def _validate_scope_path(value: object, source_len: int, label: str) -> None:
    _fields(value, SCOPE_PATH_FIELDS, label)
    assert isinstance(value, dict)
    _strings(value.get("ancestors"), f"{label}.ancestors")
    command_kind = value.get("commandKind")
    if command_kind is not None:
        _string(command_kind, f"{label}.commandKind")
    start = value.get("commandStartByte")
    end = value.get("commandEndByte")
    if start is not None:
        _int(start, f"{label}.commandStartByte")
        if start > source_len:
            raise _error(label, "commandStartByte is outside source")
    if end is not None:
        _int(end, f"{label}.commandEndByte")
        if end > source_len:
            raise _error(label, "commandEndByte is outside source")
    if start is not None and end is not None and start > end:
        raise _error(label, "command range is reversed")


def _validate_declaration(value: object, compiled: str, source_len: int, label: str) -> None:
    _fields(value, DECLARATION_FIELDS, label)
    assert isinstance(value, dict)
    if value.get("module") != compiled:
        raise _error(label, f"module disagrees with compiled module {compiled}")
    _string(value.get("name"), f"{label}.name")
    start, end = _int(value.get("startByte"), f"{label}.startByte"), _int(value.get("endByte"), f"{label}.endByte")
    selection_start = _int(value.get("selectionStartByte"), f"{label}.selectionStartByte")
    selection_end = _int(value.get("selectionEndByte"), f"{label}.selectionEndByte")
    if start > end or selection_start > selection_end or end > source_len or selection_end > source_len:
        raise _error(label, "declaration range is invalid or outside source")
    if not start <= selection_start <= selection_end <= end:
        raise _error(label, "selection range is outside declaration range")
    if not isinstance(value.get("isProof"), bool):
        raise _error(label, "isProof must be a boolean")


def _validate_evidence(value: object, label: str, compiled: str | None = None) -> None:
    _fields(value, EVIDENCE_FIELDS, label)
    assert isinstance(value, dict)
    statuses = {
        "missing_execution", "complete_proof_declaration",
        "complete_nonproof_declaration", "mixed_execution_classification",
        "incomplete_execution_evidence",
    }
    if value.get("status") not in statuses:
        raise _error(label, "status is invalid")
    execution_count = _int(value.get("executionCount"), f"{label}.executionCount")
    callers = value.get("callers")
    if not isinstance(callers, list):
        raise _error(label, "callers must be an array")
    caller_total = 0
    proofs: set[bool] = set()
    complete = True
    for index, caller in enumerate(callers):
        caller_label = f"{label}.callers[{index}]"
        _fields(caller, CALLER_FIELDS, caller_label)
        assert isinstance(caller, dict)
        caller_name = caller.get("caller")
        if caller_name is None:
            complete = False
        else:
            _string(caller_name, f"{caller_label}.caller")
        count = _int(caller.get("executionCount"), f"{caller_label}.executionCount", positive=True)
        caller_total += count
        proof = caller.get("isProofDeclaration")
        if proof is None:
            complete = False
        elif not isinstance(proof, bool):
            raise _error(caller_label, "isProofDeclaration is invalid")
        else:
            proofs.add(proof)
    if caller_total != execution_count:
        raise _error(label, "executionCount does not match callers")
    module = value.get("module")
    status = value["status"]
    if module is not None:
        _string(module, f"{label}.module")
        if compiled is not None and module != compiled:
            raise _error(label, f"module disagrees with compiled module {compiled}")
    if value.get("scheduling") != scope.SCOPE_PROBE_SCHEDULING:
        raise _error(label, "scheduling is invalid")
    if status == "missing_execution":
        if callers or execution_count != 0 or module is not None:
            raise _error(label, "missing evidence contains execution data")
    elif module is None:
        raise _error(label, "module is required")
    elif status == "complete_proof_declaration" and (not complete or proofs != {True}):
        raise _error(label, "proof evidence is incomplete")
    elif status == "complete_nonproof_declaration" and (not complete or proofs != {False}):
        raise _error(label, "computational evidence is incomplete")
    elif status == "mixed_execution_classification" and (not complete or proofs != {False, True}):
        raise _error(label, "mixed evidence is incomplete")


def _nested_count(occurrences: list[dict[str, Any]], module: str) -> int:
    nested = 0
    active: list[int] = []
    previous_start: int | None = None
    for occurrence in sorted(occurrences, key=lambda item: (item["startByte"], -item["endByte"])):
        start, end = occurrence["startByte"], occurrence["endByte"]
        if start == previous_start:
            raise _error(module, f"conflicting occurrence starts at {start}")
        previous_start = start
        while active and start >= active[-1]:
            active.pop()
        if active:
            if end > active[-1]:
                raise _error(module, "partially overlapping occurrence ranges")
            nested += 1
        active.append(end)
    return nested


def _count_map(value: object, label: str, allowed: set[str]) -> dict[str, int]:
    if not isinstance(value, dict):
        raise _error(label, "must be an object")
    result: dict[str, int] = {}
    for key, count in value.items():
        if not isinstance(key, str) or key not in allowed:
            raise _error(label, f"unknown key {key!r}")
        result[key] = _int(count, f"{label}.{key}")
    return result


def _verify_self_hash(value: dict[str, Any]) -> None:
    if "manifestHash" in value:
        raise _error(
            "manifestHash",
            "embedded raw-byte self-hashes are ambiguous; use selfHash",
        )
    if "selfHash" not in value:
        return
    expected = _hash(value["selfHash"], "selfHash")
    without = copy.deepcopy(value)
    without.pop("selfHash")
    actual = sha256(canonical_json(without))
    if expected != actual:
        raise _error("selfHash", f"does not match canonical manifest payload: {actual} != {expected}")


def _lake_package_identity(repository_root: Path) -> dict[str, Any]:
    path = repository_root / "lake-manifest.json"
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, json.JSONDecodeError) as exc:
        raise _error("package identity", f"cannot read {path}: {exc}") from exc
    packages = value.get("packages") if isinstance(value, dict) else None
    if not isinstance(packages, list):
        raise _error("package identity", "lake manifest has no package list")
    locked: list[dict[str, str]] = []
    for package in packages:
        if not isinstance(package, dict) or not all(isinstance(package.get(k), str) and package[k] for k in ("name", "type", "rev")):
            raise _error("package identity", "lake manifest contains an incomplete package")
        locked.append({k: package[k] for k in ("name", "type", "rev")})
    return {"manifestSha256": sha256(raw), "packages": locked}


def _validate_package_identity_shape(value: object, label: str) -> None:
    _fields(value, {"manifestSha256", "packages"}, label)
    assert isinstance(value, dict)
    _hash(value.get("manifestSha256"), f"{label}.manifestSha256")
    packages = value.get("packages")
    if not isinstance(packages, list) or not packages:
        raise _error(label, "packages must be a nonempty array")
    names: set[str] = set()
    for index, package in enumerate(packages):
        item_label = f"{label}.packages[{index}]"
        _fields(package, {"name", "type", "rev"}, item_label)
        assert isinstance(package, dict)
        name = _string(package.get("name"), f"{item_label}.name")
        _string(package.get("type"), f"{item_label}.type")
        revision = _string(package.get("rev"), f"{item_label}.rev")
        if not HEX40.fullmatch(revision):
            raise _error(item_label, "rev must be a 40-character lowercase commit")
        if name in names:
            raise _error(label, f"duplicate package {name}")
        names.add(name)


def _repository_root_for_manifest(path: Path) -> Path:
    for candidate in (path.parent, *path.parents):
        if (candidate / "lake-manifest.json").is_file():
            return candidate.resolve()
    return Path(__file__).resolve().parents[1]


def _current_implementation_paths(repository_root: Path) -> set[str]:
    paths: set[str] = set()
    for pattern in corpus.IMPLEMENTATION_SOURCE_PATTERNS:
        matches = [path for path in repository_root.glob(pattern) if path.is_file()]
        if not matches:
            raise _error("implementationHashes", f"active source pattern has no matches: {pattern}")
        paths.update(path.relative_to(repository_root).as_posix() for path in matches)
    return paths


def _verify_environment(
    manifest: dict[str, Any], repository_root: Path, mathlib_root: Path,
    expected_repository_commit: str | None,
) -> None:
    repository = _string(manifest.get("repositoryCommit"), "repositoryCommit")
    if not HEX40.fullmatch(repository):
        raise _error("repositoryCommit", "must be a 40-character lowercase commit")
    if expected_repository_commit is not None and repository != expected_repository_commit:
        raise _error("repositoryCommit", f"expected {expected_repository_commit}, found {repository}")
    def run(*args: str, cwd: Path = repository_root) -> str:
        result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
        if result.returncode:
            raise _error("environment", f"command failed: {' '.join(args)}: {result.stdout.strip()}")
        return result.stdout.strip()
    actual_repository = run("git", "rev-parse", "HEAD")
    if actual_repository != repository:
        raise _error("repositoryCommit", f"moving_ref: checked out {actual_repository}, manifest has {repository}")
    if run("git", "status", "--porcelain", "--untracked-files=all"):
        raise _error("environment", "repository is dirty")

    mathlib_commit = _string(manifest.get("mathlibCommit"), "mathlibCommit")
    if not HEX40.fullmatch(mathlib_commit):
        raise _error("mathlibCommit", "must be a 40-character lowercase commit")
    lake_identity = _lake_package_identity(repository_root)
    mathlib_locked = next((p["rev"] for p in lake_identity["packages"] if p["name"] == "mathlib"), None)
    if mathlib_locked != mathlib_commit:
        raise _error("mathlibCommit", f"lake manifest has {mathlib_locked}, manifest has {mathlib_commit}")
    actual_mathlib = run("git", "rev-parse", "HEAD", cwd=mathlib_root)
    if actual_mathlib != mathlib_commit:
        raise _error("mathlibCommit", f"pinned Mathlib has {actual_mathlib}, manifest has {mathlib_commit}")
    if run("git", "status", "--porcelain", "--untracked-files=all", cwd=mathlib_root):
        raise _error("environment", "pinned Mathlib is dirty")

    lean = manifest.get("lean")
    if not isinstance(lean, dict) or set(lean) != {"version", "commit"}:
        raise _error("lean", "must expose exactly version and commit")
    version, commit = _string(lean.get("version"), "lean.version"), _string(lean.get("commit"), "lean.commit")
    if not HEX40.fullmatch(commit):
        raise _error("lean.commit", "must be a 40-character lowercase commit")
    actual_lean = run("lean", "--version")
    if f"version {version}" not in actual_lean or f"commit {commit}" not in actual_lean:
        raise _error("lean", f"toolchain differs: {actual_lean}")
    if "packageIdentity" in manifest and manifest["packageIdentity"] != lake_identity:
        raise _error("packageIdentity", "does not match pinned lake-manifest.json")
    if "packageIdentities" in manifest and manifest["packageIdentities"] != lake_identity:
        raise _error("packageIdentities", "does not match pinned lake-manifest.json")


def verify_manifest(
    manifest_path: str | Path,
    *,
    repository_root: str | Path | None = None,
    mathlib_root: str | Path | None = None,
    expected_repository_commit: str | None = None,
    require_complete: bool = True,
    check_environment: bool = True,
    require_authenticated_digest: bool = False,
) -> dict[str, Any]:
    """Verify one manifest and return a compact summary.

    ``check_environment=False`` is intended for fixture tests and offline
    structural inspection.  It still reads every module source and checks every
    digest/range.  Production verification should leave it enabled.
    """
    path = Path(manifest_path).resolve()
    try:
        raw = path.read_bytes()
        manifest = json.loads(raw)
    except (OSError, json.JSONDecodeError) as exc:
        raise _error("file", f"cannot read valid JSON: {exc}") from exc
    if not isinstance(manifest, dict):
        raise _error("root", "must be an object")
    _fields(manifest, TOP_LEVEL_FIELDS, "top-level", OPTIONAL_TOP_LEVEL_FIELDS)
    if (
        not isinstance(manifest.get("reportSchema"), int)
        or isinstance(manifest.get("reportSchema"), bool)
        or manifest.get("reportSchema") != SCHEMA
    ):
        raise _error("schema", f"must be {SCHEMA}")
    if manifest.get("kind") != KIND:
        raise _error("kind", f"must be {KIND!r}")
    if manifest.get("allowDirty") is not False:
        raise _error("policy", "allowDirty must be false")
    if manifest.get("allowUnresolved") is not False:
        raise _error("policy", "allowUnresolved must be false")
    _verify_self_hash(manifest)
    if require_authenticated_digest and "selfHash" not in manifest:
        raise _error("selfHash", "strict acceptance requires an authenticated digest")

    repository_root = Path(repository_root or _repository_root_for_manifest(path)).resolve()
    mathlib_root = Path(mathlib_root or repository_root / ".lake" / "packages" / "mathlib").resolve()
    for field in ("packageIdentity", "packageIdentities"):
        if field in manifest:
            _validate_package_identity_shape(manifest[field], field)
    if check_environment:
        _verify_environment(manifest, repository_root, mathlib_root, expected_repository_commit)
    elif expected_repository_commit is not None and manifest.get("repositoryCommit") != expected_repository_commit:
        raise _error("repositoryCommit", f"expected {expected_repository_commit}, found {manifest.get('repositoryCommit')}")

    lean = manifest.get("lean")
    if not isinstance(lean, dict) or set(lean) != {"version", "commit"}:
        raise _error("lean", "must expose exactly version and commit")
    _string(lean.get("version"), "lean.version")
    if not HEX40.fullmatch(_string(lean.get("commit"), "lean.commit")):
        raise _error("lean.commit", "must be a 40-character lowercase commit")
    for field in ("repositoryCommit", "mathlibCommit"):
        if not HEX40.fullmatch(_string(manifest.get(field), field)):
            raise _error(field, "must be a 40-character lowercase commit")
    if not isinstance(manifest.get("modulePrefix"), str) or not manifest["modulePrefix"].startswith("Mathlib/"):
        raise _error("modulePrefix", "must be a Mathlib/ prefix")
    if require_complete and manifest["modulePrefix"] != "Mathlib/":
        raise _error("modulePrefix", "whole-corpus verification requires Mathlib/")

    for field in (
        "moduleFileCount", "inventoriedModuleCount", "occurrenceCount",
        "nestedOccurrenceCount", "duplicateSyntaxRecords", "duplicateScopeSyntaxRecords",
    ):
        _int(manifest.get(field), field)
    _strings(manifest.get("fullFrontendFallbacks"), "fullFrontendFallbacks")
    _strings(manifest.get("scopeFrontendFallbacks"), "scopeFrontendFallbacks")
    probe = manifest.get("scopeProbe")
    _fields(probe, {"module", "scheduling", "temporaryCopyOnly", "reportCommand"}, "scopeProbe")
    assert isinstance(probe, dict)
    if probe != {
        "module": scope.SCOPE_PROBE_IMPORT,
        "scheduling": scope.SCOPE_PROBE_SCHEDULING,
        "temporaryCopyOnly": True,
        "reportCommand": "simp_engine_boundary_scope_report",
    }:
        raise _error("scopeProbe", "metadata is invalid")

    implementation = manifest.get("implementationHashes")
    if not isinstance(implementation, dict) or not implementation:
        raise _error("implementationHashes", "must be a nonempty object")
    for raw_path, digest in implementation.items():
        if not isinstance(raw_path, str) or not raw_path or Path(raw_path).is_absolute() or ".." in Path(raw_path).parts:
            raise _error("implementationHashes", f"invalid repository path {raw_path!r}")
        expected = _hash(digest, f"implementationHashes[{raw_path}]")
        source_path = (repository_root / raw_path).resolve()
        try:
            source_path.relative_to(repository_root)
        except ValueError as exc:
            raise _error("implementationHashes", f"path escapes repository: {raw_path}") from exc
        if not source_path.is_file() or sha256(source_path.read_bytes()) != expected:
            raise _error("implementationHashes", f"stale or missing implementation input: {raw_path}")
    if check_environment:
        current_paths = _current_implementation_paths(repository_root)
        if set(implementation) != current_paths:
            raise _error(
                "implementationHashes",
                f"implementation source set is stale: missing={sorted(current_paths - set(implementation))}, extra={sorted(set(implementation) - current_paths)}",
            )

    manual = manifest.get("manualOverrides")
    _fields(manual, {"sha256", "schema", "environment"}, "manualOverrides")
    assert isinstance(manual, dict)
    _hash(manual.get("sha256"), "manualOverrides.sha256")
    if _int(manual.get("schema"), "manualOverrides.schema") != MANUAL_OVERRIDE_SCHEMA:
        raise _error("manualOverrides.schema", f"must be {MANUAL_OVERRIDE_SCHEMA}")
    if manual.get("environment") != {"mathlibCommit": manifest["mathlibCommit"], "lean": manifest["lean"]}:
        raise _error("manualOverrides", "environment identity disagrees with manifest")
    manual_path = repository_root / "Experiment" / "simp_manual_overrides.json"
    if check_environment:
        if not manual_path.is_file() or sha256(manual_path.read_bytes()) != manual["sha256"]:
            raise _error("manualOverrides", "database is stale or missing")


    modules = manifest.get("modules")
    if not isinstance(modules, list):
        raise _error("modules", "must be an array")
    if require_complete and not modules:
        raise _error("modules", "whole-corpus acceptance requires at least one module")
    seen_modules: set[str] = set()
    seen_ids: set[str] = set()
    role_counts: Counter[str] = Counter()
    declaration_counts: Counter[str] = Counter()
    action_counts: Counter[str] = Counter()
    total_occurrences = inventoried_modules = nested_total = duplicate_syntax_total = duplicate_scope_total = 0
    names: list[str] = []
    for module_value in modules:
        _fields(module_value, MODULE_FIELDS, "module")
        assert isinstance(module_value, dict)
        module = _string(module_value.get("module"), "module.module")
        if module in seen_modules:
            raise _error("modules", f"duplicate module {module}")
        seen_modules.add(module); names.append(module)
        compiled = _string(module_value.get("compiledModule"), f"{module}.compiledModule")
        # Validate lexical identity before deriving the compiled name.  This
        # keeps traversal attempts diagnosable even when their forged compiled
        # name is also inconsistent.
        if not module.startswith("Mathlib/") or ".." in Path(module).parts:
            _safe_module_path(mathlib_root, module)
        if not module.startswith(manifest["modulePrefix"]):
            raise _error(module, "is outside manifest modulePrefix")
        if compiled != _compiled_module(module):
            raise _error(module, "compiledModule disagrees with source path")
        source_path = _safe_module_path(mathlib_root, module)
        source = source_path.read_bytes()
        if module_value.get("moduleHash") != sha256(module.encode()):
            raise _error(module, "moduleHash is stale")
        if module_value.get("sourceHash") != sha256(source):
            raise _error(module, "sourceHash is stale")
        duplicate_syntax_total += _int(module_value.get("duplicateSyntaxRecords"), f"{module}.duplicateSyntaxRecords")
        duplicate_scope_total += _int(module_value.get("duplicateScopeSyntaxRecords"), f"{module}.duplicateScopeSyntaxRecords")
        occurrences = module_value.get("occurrences")
        if not isinstance(occurrences, list):
            raise _error(module, "occurrences must be an array")
        inventoried_modules += bool(occurrences)
        checked_occurrences: list[dict[str, Any]] = []
        for occurrence in occurrences:
            _fields(occurrence, OCCURRENCE_FIELDS, f"{module}.occurrence", {"executionEvidence"})
            assert isinstance(occurrence, dict)
            occurrence_id = _string(occurrence.get("id"), f"{module}.occurrence.id")
            if occurrence_id in seen_ids:
                raise _error("occurrences", f"duplicate occurrence ID {occurrence_id}")
            seen_ids.add(occurrence_id)
            kind = _string(occurrence.get("kind"), f"{module}.occurrence.kind")
            if kind not in inventory.SUPPORTED_KINDS:
                raise _error(module, f"unsupported occurrence kind {kind!r}")
            text = occurrence.get("source")
            if not isinstance(text, str):
                raise _error(module, "occurrence source must be a string")
            start, end = _int(occurrence.get("startByte"), f"{module}.occurrence.startByte"), _int(occurrence.get("endByte"), f"{module}.occurrence.endByte")
            if not start < end <= len(source):
                raise _error(module, f"invalid occurrence range {start}:{end}")
            try:
                actual_text = source[start:end].decode("utf-8")
            except UnicodeDecodeError as exc:
                raise _error(module, "occurrence range splits UTF-8") from exc
            if actual_text != text:
                raise _error(module, f"stale occurrence source at {start}")
            if not text.startswith("simp") or occurrence.get("syntaxKind") != "Lean.Parser.Tactic.simp":
                raise _error(module, f"occurrence syntax is invalid at {start}")
            if occurrence_id != inventory.occurrence_id(module, start, end) or not HEX16.fullmatch(occurrence_id):
                raise _error(module, f"occurrence ID does not match range at {start}")
            if (_int(occurrence.get("line"), f"{module}.occurrence.line"), _int(occurrence.get("column"), f"{module}.occurrence.column")) != _line_column(source, start):
                raise _error(module, f"line/column does not match range at {start}")
            _strings(occurrence.get("ancestors"), f"{module}.occurrence.ancestors")
            if occurrence.get("commandKind") is not None:
                _string(occurrence.get("commandKind"), f"{module}.occurrence.commandKind")
            for field in ("commandStartByte", "commandEndByte"):
                if occurrence.get(field) is not None:
                    _int(occurrence.get(field), f"{module}.occurrence.{field}")
                    if occurrence[field] > len(source):
                        raise _error(module, f"{field} is outside source")
            if occurrence.get("commandStartByte") is not None and occurrence.get("commandEndByte") is not None and occurrence["commandStartByte"] > occurrence["commandEndByte"]:
                raise _error(module, "command range is reversed")
            if (
                occurrence.get("commandStartByte") is not None
                and occurrence.get("commandEndByte") is not None
                and not (
                    occurrence["commandStartByte"] <= start
                    and end <= occurrence["commandEndByte"]
                )
            ):
                raise _error(module, "occurrence is outside command range")
            scope_paths = occurrence.get("scopePaths")
            if not isinstance(scope_paths, list) or not scope_paths:
                raise _error(module, "scopePaths must be a nonempty array")
            for index, path_value in enumerate(scope_paths):
                _validate_scope_path(path_value, len(source), f"{module}.scopePaths[{index}]")
                assert isinstance(path_value, dict)
                for field in ("commandKind", "commandStartByte", "commandEndByte"):
                    if path_value.get(field) != occurrence.get(field):
                        raise _error(module, f"scope path {field} disagrees with occurrence")
            declarations = occurrence.get("declarations")
            if not isinstance(declarations, list):
                raise _error(module, "declarations must be an array")
            for index, declaration in enumerate(declarations):
                _validate_declaration(declaration, compiled, len(source), f"{module}.declarations[{index}]")
            if declarations and not any(
                declaration["startByte"] <= start and end <= declaration["endByte"]
                for declaration in declarations
            ):
                raise _error(module, "occurrence range is outside all declarations")
            declaration_kind = occurrence.get("declarationKind")
            proof_values = {declaration["isProof"] for declaration in declarations}
            if declaration_kind in {"proof", "computational", "mixed", "signature_or_default"}:
                if not declarations:
                    raise _error(module, "scope declaration list is empty for classified declaration")
                if declaration_kind == "proof" and proof_values != {True}:
                    raise _error(module, "proof classification disagrees with declaration isProof")
                if declaration_kind == "computational" and proof_values != {False}:
                    raise _error(module, "computational classification disagrees with declaration isProof")
                if declaration_kind == "mixed" and proof_values != {False, True}:
                    raise _error(module, "mixed classification disagrees with declaration isProof")
            _string(occurrence.get("reason"), f"{module}.occurrence.reason")
            if "executionEvidence" in occurrence:
                _validate_evidence(
                    occurrence["executionEvidence"],
                    f"{module}.executionEvidence",
                    compiled,
                )
            try:
                role, declaration_kind, action = scope.validate_scope_dimensions(occurrence.get("executionRole"), occurrence.get("declarationKind"), occurrence.get("action"))
            except RuntimeError as exc:
                raise _error(module, f"invalid scope dimensions: {exc}") from exc
            role_counts[role] += 1; declaration_counts[declaration_kind] += 1; action_counts[action] += 1
            checked_occurrences.append(occurrence)
        nested_total += _nested_count(checked_occurrences, module)
        total_occurrences += len(checked_occurrences)

    if names != sorted(names):
        raise _error("modules", "records are not in canonical path order")
    if require_complete:
        expected_names = sorted(path.relative_to(mathlib_root).as_posix() for path in mathlib_root.glob("Mathlib/**/*.lean") if path.is_file() and not path.is_symlink())
        if names != expected_names:
            missing, extra = sorted(set(expected_names) - set(names)), sorted(set(names) - set(expected_names))
            raise _error("modules", f"whole-corpus set differs: missing={missing[:5]}, extra={extra[:5]}")
    if manifest["moduleFileCount"] != len(modules) or manifest["inventoriedModuleCount"] != inventoried_modules or manifest["occurrenceCount"] != total_occurrences or manifest["nestedOccurrenceCount"] != nested_total or manifest["duplicateSyntaxRecords"] != duplicate_syntax_total or manifest["duplicateScopeSyntaxRecords"] != duplicate_scope_total:
        raise _error("counts", "top-level counts do not match module records")
    if dict(sorted(_count_map(manifest.get("countsByExecutionRole"), "countsByExecutionRole", set(scope.EXECUTION_ROLES)).items())) != dict(sorted(role_counts.items())):
        raise _error("countsByExecutionRole", "does not match occurrence records")
    if dict(sorted(_count_map(manifest.get("countsByDeclarationKind"), "countsByDeclarationKind", set(scope.DECLARATION_KINDS)).items())) != dict(sorted(declaration_counts.items())):
        raise _error("countsByDeclarationKind", "does not match occurrence records")
    if dict(sorted(_count_map(manifest.get("countsByAction"), "countsByAction", set(scope.ACTIONS)).items())) != dict(sorted(action_counts.items())):
        raise _error("countsByAction", "does not match occurrence records")
    if action_counts.get("unresolved", 0):
        raise _error("policy", "unresolved occurrences are not accepted")
    return {"kind": KIND, "reportSchema": SCHEMA, "modules": len(modules), "occurrences": total_occurrences, "actions": dict(sorted(action_counts.items()))}


def recompute_inventory(manifest_path: str | Path, *, mathlib_root: str | Path, repository_root: str | Path, timeout: int = 3600) -> None:
    """Freshly run the syntax inventory and compare source-backed records.

    This pass intentionally omits scope/declaration recomputation: those are
    compiler/frontend observations and remain covered by their own producer
    protocol.  It is separate from :func:`verify_manifest` because it launches
    a potentially long Lean process over the complete corpus.
    """
    path = Path(manifest_path).resolve(); manifest = json.loads(path.read_bytes())
    mathlib = Path(mathlib_root).resolve(); repository = Path(repository_root).resolve()
    before = _freshness_snapshot(path, manifest, repository, mathlib)
    source_paths = [mathlib / module["module"] for module in manifest["modules"]]
    command = [sys.executable, str(repository / "Experiment" / "lean_toolchain_cache.py"), "inventory", "--header-imports", *(str(p) for p in source_paths)]
    result = subprocess.run(command, cwd=repository, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, check=False)
    if result.returncode:
        raise _error("recompute", result.stdout[-4000:])
    actual: dict[str, list[tuple[int, int, str, str, int, int, str]]] = {}
    fallbacks: set[str] = set()
    deferred: set[str] = set()
    by_path = {str(p.resolve()): module["module"] for p, module in zip(source_paths, manifest["modules"])}
    for line in result.stdout.splitlines():
        if line.startswith("SIMP_ENGINE_INVENTORY_FULL_FALLBACK file="):
            fallback = by_path.get(str(Path(line.split("=", 1)[1]).resolve()))
            if fallback is None:
                raise _error("recompute", "inventory fallback named an unrequested source")
            fallbacks.add(fallback)
            continue
        if line.startswith("SIMP_ENGINE_INVENTORY_DEFERRED_FALLBACK file="):
            deferred_path = line.split("=", 1)[1]
            deferred_module = by_path.get(str(Path(deferred_path).resolve()))
            if deferred_module is None:
                raise _error("recompute", "inventory deferred an unrequested source")
            deferred.add(deferred_module)
            continue
        if not line.startswith("{"):
            continue
        record = json.loads(line); module = by_path.get(str(Path(record.get("file", "")).resolve()))
        if module is None:
            continue
        actual.setdefault(module, []).append((
            int(record["line"]), int(record["column"]), record["syntaxKind"],
            record["kind"], int(record["startByte"]), int(record["endByte"]),
            record["source"],
        ))
    for module in manifest["modules"]:
        expected = sorted((
            o["line"], o["column"], o["syntaxKind"], o["kind"],
            o["startByte"], o["endByte"], o["source"],
        ) for o in module["occurrences"])
        if sorted(actual.get(module["module"], [])) != expected:
            raise _error("recompute", f"fresh syntax inventory differs for {module['module']}")
    if fallbacks != set(manifest["fullFrontendFallbacks"]):
        raise _error("recompute", f"inventory fallback set differs: {sorted(fallbacks)} != {sorted(manifest['fullFrontendFallbacks'])}")
    if deferred:
        raise _error("recompute", f"inventory left deferred fallbacks unresolved: {sorted(deferred)}")
    _assert_fresh(before, path, manifest, repository, mathlib, "inventory subprocess")


def _freshness_snapshot(
    manifest_path: Path, manifest: dict[str, Any], repository_root: Path, mathlib_root: Path
) -> dict[str, Any]:
    """Capture mutable inputs that must remain fixed across fresh subprocesses."""
    source_hashes = {
        path.relative_to(mathlib_root).as_posix(): sha256(path.read_bytes())
        for path in mathlib_root.glob("Mathlib/**/*.lean")
        if path.is_file() and not path.is_symlink()
    }
    implementation = {
        relative: sha256((repository_root / relative).resolve().read_bytes())
        for relative in _current_implementation_paths(repository_root)
    }
    environment = {}
    for relative in ("lake-manifest.json", "lean-toolchain"):
        input_path = repository_root / relative
        if input_path.is_file():
            environment[relative] = sha256(input_path.read_bytes())
    def git_state(root: Path) -> tuple[str, str]:
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
        status = subprocess.run(
            ["git", "status", "--porcelain", "--untracked-files=all"], cwd=root,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
        if commit.returncode or status.returncode:
            raise _error("recompute", f"cannot snapshot git state under {root}")
        return commit.stdout.strip(), status.stdout
    return {
        "manifest": sha256(manifest_path.read_bytes()),
        "sources": source_hashes,
        "implementation": implementation,
        "environment": environment,
        "repositoryGit": git_state(repository_root),
        "mathlibGit": git_state(mathlib_root),
    }


def _assert_fresh(
    before: dict[str, Any], manifest_path: Path, manifest: dict[str, Any],
    repository_root: Path, mathlib_root: Path, label: str,
) -> None:
    after = _freshness_snapshot(manifest_path, manifest, repository_root, mathlib_root)
    if after != before:
        changed = [key for key in before if before.get(key) != after.get(key)]
        raise _error("recompute", f"{label} changed authenticated inputs: {changed}")


def _scope_record_key(record: dict[str, Any]) -> tuple[Any, ...]:
    return (
        record["line"], record["column"], record["kind"], record["source"],
        tuple(record["ancestors"]), record.get("commandKind"),
        record.get("commandStartByte"), record.get("commandEndByte"),
    )


def _manifest_scope_key(path: dict[str, Any], occurrence: dict[str, Any]) -> tuple[Any, ...]:
    return (
        occurrence["line"], occurrence["column"], occurrence["kind"], occurrence["source"],
        tuple(path["ancestors"]), path.get("commandKind"),
        path.get("commandStartByte"), path.get("commandEndByte"),
    )


def _declaration_key(value: dict[str, Any]) -> tuple[Any, ...]:
    return tuple(value[field] for field in (
        "module", "name", "startByte", "endByte", "selectionStartByte",
        "selectionEndByte", "isProof",
    ))


def _fresh_scope_and_declarations(
    manifest_path: Path, manifest: dict[str, Any], repository_root: Path,
    mathlib_root: Path, timeout: int,
) -> None:
    """Compare fresh Scope.lean records with every authenticated manifest fact.

    The scope classifier is the current checked frontend implementation, so
    this is a fresh-output consistency check rather than a proof that its
    semantic policy is independent.  The independent checks here bind its
    output to source ranges, parser ancestry, declarations, and manifest IDs;
    the policy's semantic trust boundary remains the Scope.lean implementation.
    """
    specs = [
        scope.ModuleSpec(
            _compiled_module(module["module"]),
            mathlib_root / module["module"],
            len(module["occurrences"]),
        )
        for module in manifest["modules"]
    ]
    before = _freshness_snapshot(manifest_path, manifest, repository_root, mathlib_root)
    occurrences, declarations, fallbacks = scope.load_records_with_fallbacks(
        specs, batch_size=128, timeout=timeout
    )
    _assert_fresh(before, manifest_path, manifest, repository_root, mathlib_root, "scope subprocess")
    if set(fallbacks) != set(manifest["scopeFrontendFallbacks"]):
        raise _error("recompute", f"scope fallback set differs: {fallbacks} != {manifest['scopeFrontendFallbacks']}")

    for module_value in manifest["modules"]:
        module = module_value["module"]
        compiled = module_value["compiledModule"]
        manifest_occurrences = module_value["occurrences"]
        fresh_occurrences = occurrences.get(compiled, [])
        expected_paths: Counter[tuple[Any, ...]] = Counter()
        for occurrence in manifest_occurrences:
            for path in occurrence["scopePaths"]:
                expected_paths[_manifest_scope_key(path, occurrence)] += 1
        actual_paths: Counter[tuple[Any, ...]] = Counter()
        for occurrence in fresh_occurrences:
            if occurrence.get("module") != compiled:
                raise _error("recompute", f"scope occurrence has wrong module for {module}")
            actual_paths[_scope_record_key(occurrence)] += 1
        if actual_paths != expected_paths:
            raise _error("recompute", f"scope occurrence/ancestor records differ for {module}")

        fresh_declarations = declarations.get(compiled, [])
        by_fresh_key = {
            (int(occurrence["startByte"]), int(occurrence["endByte"]), occurrence["kind"], occurrence["source"]): occurrence
            for occurrence in fresh_occurrences
        }
        for manifest_occurrence in manifest_occurrences:
            identity = (
                manifest_occurrence["startByte"], manifest_occurrence["endByte"],
                manifest_occurrence["kind"], manifest_occurrence["source"],
            )
            fresh_occurrence = by_fresh_key.get(identity)
            if fresh_occurrence is None:
                raise _error("recompute", f"scope occurrence missing for {module}:{manifest_occurrence['id']}")
            expected_declarations = scope.containing_declarations(
                fresh_occurrence, fresh_declarations
            )
            actual_declarations = manifest_occurrence["declarations"]
            if [_declaration_key(value) for value in actual_declarations] != [
                _declaration_key(value) for value in expected_declarations
            ]:
                raise _error("recompute", f"declarations differ for {module}:{manifest_occurrence['id']}")

            classification = scope.classify(fresh_occurrence, expected_declarations)
            expected_dimensions = (
                classification["executionRole"], classification["declarationKind"],
                classification["action"], classification["reason"],
            )
            evidence = manifest_occurrence.get("executionEvidence")
            if evidence is not None:
                # Resolve the evidence in a separate temporary source process;
                # this also authenticates every occurrence ID/caller join.
                selected_entry = dict(manifest_occurrence)
                evidence_before = _freshness_snapshot(
                    manifest_path, manifest, repository_root, mathlib_root
                )
                fresh_evidence = scope.resolve_execution_evidence(
                    compiled,
                    (mathlib_root / module).read_bytes(),
                    [selected_entry],
                    [fresh_occurrence],
                    timeout=timeout,
                )[manifest_occurrence["id"]]
                _assert_fresh(
                    evidence_before, manifest_path, manifest, repository_root,
                    mathlib_root, "execution evidence subprocess"
                )
                if fresh_evidence != evidence:
                    raise _error("recompute", f"executionEvidence differs for {module}:{manifest_occurrence['id']}")
                status = evidence["status"]
                quoted = scope._quotation_context(fresh_occurrence["ancestors"]) == "quotation"
                generated = quoted and not expected_declarations
                if status == "complete_proof_declaration":
                    expected_dimensions = ("direct_executable", "generated_proof" if generated else "proof", "materialize", "temporary source instrumentation observed executions whose final caller declarations are all proof-valued")
                elif status == "complete_nonproof_declaration":
                    expected_dimensions = ("direct_executable", "generated_computational" if generated else "computational", "materialize", "temporary source instrumentation observed executions whose final caller declarations are all non-proof-valued")
                elif status == "mixed_execution_classification":
                    expected_dimensions = ("unresolved" if quoted else "direct_executable", "mixed", "unresolved", "executions resolved to both proof and non-proof declarations; scope action fails closed")
                else:
                    expected_dimensions = ("unresolved" if quoted else "direct_executable", "unknown", "unresolved", "selected source occurrence did not execute in the temporary probe copy; scope action fails closed")
            actual_dimensions = tuple(manifest_occurrence[field] for field in ("executionRole", "declarationKind", "action", "reason"))
            if actual_dimensions != expected_dimensions:
                raise _error("recompute", f"scope classification differs for {module}:{manifest_occurrence['id']}")


def recompute_acceptance(
    manifest_path: str | Path, *, repository_root: Path, mathlib_root: Path, timeout: int
) -> None:
    """Run all fresh parser/frontend checks required for acceptance."""
    path = Path(manifest_path).resolve()
    manifest = json.loads(path.read_bytes())
    recompute_inventory(
        path, mathlib_root=mathlib_root, repository_root=repository_root, timeout=timeout
    )
    _fresh_scope_and_declarations(
        path, manifest, repository_root, mathlib_root, timeout
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("accept", "inspect"):
        command = commands.add_parser(name)
        command.add_argument("manifest")
        command.add_argument("--repository-root", type=Path)
        command.add_argument("--mathlib-root", type=Path)
        command.add_argument("--expected-repository-commit")
        command.add_argument("--timeout", type=int, default=3600)
        if name == "inspect":
            command.add_argument("--allow-partial", action="store_true", help="inspect a prefix/fixture")
            command.add_argument("--skip-environment", action="store_true", help="offline structural/source checks")
            command.add_argument("--recompute", action="store_true", help="run the expensive parser inventory only")
    args = parser.parse_args()
    manifest_path = Path(args.manifest).resolve()
    repository = (args.repository_root or _repository_root_for_manifest(manifest_path)).resolve()
    mathlib = (args.mathlib_root or repository / ".lake" / "packages" / "mathlib").resolve()
    try:
        if args.command == "accept":
            summary = verify_manifest(
                manifest_path,
                repository_root=repository,
                mathlib_root=mathlib,
                expected_repository_commit=args.expected_repository_commit,
                require_complete=True,
                check_environment=True,
                require_authenticated_digest=True,
            )
            recompute_acceptance(
                manifest_path,
                repository_root=repository,
                mathlib_root=mathlib,
                timeout=args.timeout,
            )
            print(json.dumps({**summary, "accepted": True, "recomputed": "syntax_scope_declarations"}, sort_keys=True))
        else:
            summary = verify_manifest(
                manifest_path,
                repository_root=repository,
                mathlib_root=mathlib,
                expected_repository_commit=args.expected_repository_commit,
                require_complete=not args.allow_partial,
                check_environment=not args.skip_environment,
            )
            if args.recompute:
                recompute_inventory(
                    manifest_path,
                    mathlib_root=mathlib,
                    repository_root=repository,
                    timeout=args.timeout,
                )
            print(json.dumps({**summary, "accepted": False, "recomputed": "syntax" if args.recompute else False}, sort_keys=True))
    except Exception as exc:
        print(f"simp boundary manifest verification failed: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc


if __name__ == "__main__":
    main()
