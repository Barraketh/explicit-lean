#!/usr/bin/env python3
"""Verify a freshly generated whole-Mathlib simp boundary manifest.

``verify`` authenticates the exact raw manifest bytes supplied by the caller,
checks the JSON/source/environment contract, and performs fresh parser,
scope, and declaration consistency checks.  Its receipt reports source
consistency only; campaign acceptance still needs independent semantic
oracles.  ``inspect`` is an explicitly partial structural or syntax-only
diagnostic mode and never emits an acceptance result.
"""

from __future__ import annotations

import argparse
from collections import Counter
from contextlib import contextmanager, nullcontext
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
import threading
from typing import Any, Iterable, Mapping

import check_simp_engine_boundary_scope as scope
import simp_engine_inventory as inventory
import simp_engine_boundary_corpus as corpus
from process_runner import run_process


_LAKE_ENV_LOCK = threading.RLock()


SCHEMA = 2
KIND = "simp_engine_boundary_manifest"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
HEX16 = re.compile(r"^[0-9a-f]{16}$")
MANUAL_OVERRIDE_SCHEMA = 1
# Header-import inventory retains the imported environment for every source in
# one invocation.  A file-count bound therefore does not bound RSS: the first
# 32-file batch reached a 1,556-module import closure on a 64GB Mac.  The
# dependency-map bound below limits the union of transitive Mathlib modules in
# each fresh child.  A child whose own closure exceeds this bound is still run
# alone (there is no sound way to split one source's imports).
FRESH_INVENTORY_MAX_IMPORT_MODULES = 512
# Keep enough headroom for the verifier, the desktop, and the next child.  A
# strict run that cannot maintain this reserve is a failed verification, never
# a partial acceptance.
FRESH_INVENTORY_MIN_FREE_MEMORY_BYTES = 12 * 1024**3

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


@dataclass(frozen=True)
class ManifestSnapshot:
    path: Path
    raw: bytes
    digest: str
    device: int
    inode: int
    size: int
    mtime_ns: int


def _read_manifest_snapshot(manifest_path: str | Path) -> ManifestSnapshot:
    path = Path(manifest_path).resolve()
    try:
        with path.open("rb") as stream:
            before = os.fstat(stream.fileno())
            raw = stream.read()
            after = os.fstat(stream.fileno())
    except OSError as exc:
        raise _error("file", f"cannot read manifest: {exc}") from exc
    before_identity = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
    after_identity = (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
    if before_identity != after_identity:
        raise _error("file", "manifest changed while it was being read")
    return ManifestSnapshot(path, raw, sha256(raw), *after_identity)


def _parse_manifest(raw: bytes) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise _error("file", f"cannot parse valid JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise _error("root", "must be an object")
    return value


def _assert_manifest_snapshot(snapshot: ManifestSnapshot) -> None:
    try:
        current_stat = snapshot.path.stat()
        current_identity = (
            current_stat.st_dev, current_stat.st_ino,
            current_stat.st_size, current_stat.st_mtime_ns,
        )
        if current_identity != (snapshot.device, snapshot.inode, snapshot.size, snapshot.mtime_ns):
            raise _error("file", "manifest path identity changed during verification")
        current_raw = snapshot.path.read_bytes()
    except OSError as exc:
        raise _error("file", f"manifest disappeared during verification: {exc}") from exc
    if current_raw != snapshot.raw:
        raise _error("file", "manifest content changed during verification")


def verify_raw_manifest_digest(manifest_path: str | Path, expected_sha256: str) -> str:
    """Authenticate the exact bytes from one opened manifest read."""
    expected = _hash(expected_sha256, "expected-sha256")
    snapshot = _read_manifest_snapshot(manifest_path)
    if snapshot.digest != expected:
        raise _error("expected-sha256", f"raw manifest bytes differ: {snapshot.digest} != {expected}")
    return snapshot.digest


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


def _checked_binary_digest(path: Path, expected: str, label: str) -> tuple[Path, str, os.stat_result]:
    resolved = path.resolve()
    if not resolved.is_file() or not resolved.stat().st_mode & 0o111:
        raise _error(label, f"explicit executable is not runnable: {resolved}")
    expected_digest = _hash(expected, f"expected-{label}-sha256")
    try:
        stat = resolved.stat()
        digest = sha256(resolved.read_bytes())
    except OSError as exc:
        raise _error(label, f"cannot read explicit executable: {exc}") from exc
    if digest != expected_digest:
        raise _error(label, f"explicit executable digest differs: {digest}")
    return resolved, digest, stat


def _assert_pinned_lake(lake_path: Path, expected_sha256: str) -> dict[str, str]:
    resolved, digest, stat = _checked_binary_digest(lake_path, expected_sha256, "lake")
    discovered = shutil.which("lake")
    if discovered is None or Path(discovered).resolve() != resolved:
        raise _error("recompute", f"PATH lake does not resolve to authenticated executable {resolved}")
    discovered_stat = resolved.stat()
    if (discovered_stat.st_dev, discovered_stat.st_ino) != (stat.st_dev, stat.st_ino):
        raise _error("recompute", "PATH lake executable identity changed")
    return {"path": str(resolved), "sha256": digest, "PATH": os.environ.get("PATH", "")}


@contextmanager
def _pinned_lake_environment(lake_path: Path, expected_sha256: str):
    if not _LAKE_ENV_LOCK.acquire(blocking=False):
        raise _error("recompute", "concurrent pinned Lake verification is unsafe")
    old_path = os.environ.get("PATH")
    try:
        resolved, _, _ = _checked_binary_digest(lake_path, expected_sha256, "lake")
        entries = [] if old_path is None else old_path.split(os.pathsep)
        os.environ["PATH"] = os.pathsep.join([str(resolved.parent), *[entry for entry in entries if entry != str(resolved.parent)]])
        effective = _assert_pinned_lake(resolved, expected_sha256)
        yield effective
        _assert_pinned_lake(resolved, expected_sha256)
    finally:
        if old_path is None:
            os.environ.pop("PATH", None)
        else:
            os.environ["PATH"] = old_path
        _LAKE_ENV_LOCK.release()


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
            "embedded raw-byte hashes are rejected; authenticate with external --expected-sha256",
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
    expected_repository_commit: str | None, *, lake_path: Path,
    expected_lake_sha256: str, lean_path: Path, expected_lean_sha256: str,
) -> dict[str, str]:
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
    lake_path, lake_digest, _ = _checked_binary_digest(lake_path, expected_lake_sha256, "lake")
    lean_path, lean_digest, _ = _checked_binary_digest(lean_path, expected_lean_sha256, "lean")
    prefix = Path(run(str(lake_path), "env", "lean", "--print-prefix")).resolve()
    expected_prefix = lean_path.parent.parent
    if prefix != expected_prefix:
        raise _error("lean", f"lake env prefix {prefix} does not contain explicit Lean {lean_path}")
    actual_lean = run(str(lake_path), "env", "lean", "--version")
    direct_lean = run(str(lean_path), "--version")
    expected_version = f"version {version}"
    expected_commit = f"commit {commit}"
    if (
        expected_version not in actual_lean
        or expected_commit not in actual_lean
        or direct_lean != actual_lean
    ):
        raise _error("lean", f"pinned toolchain differs: lake={actual_lean!r}, executable={direct_lean!r}")
    toolchain_path = repository_root / "lean-toolchain"
    if not toolchain_path.is_file() or version not in toolchain_path.read_text(encoding="utf-8").strip():
        raise _error("lean", "lean-toolchain does not identify the manifest version")
    if "packageIdentity" in manifest and manifest["packageIdentity"] != lake_identity:
        raise _error("packageIdentity", "does not match pinned lake-manifest.json")
    if "packageIdentities" in manifest and manifest["packageIdentities"] != lake_identity:
        raise _error("packageIdentities", "does not match pinned lake-manifest.json")
    return {
        "lakePath": str(lake_path), "lakeBinarySha256": lake_digest,
        "leanPath": str(lean_path), "leanBinarySha256": lean_digest,
    }


def _verify_manifest(
    manifest_path: str | Path,
    *,
    raw: bytes,
    repository_root: str | Path | None = None,
    mathlib_root: str | Path | None = None,
    expected_repository_commit: str | None = None,
    require_complete: bool = True,
    check_environment: bool = True,
    lake_path: Path | None = None, expected_lake_sha256: str | None = None,
    lean_path: Path | None = None, expected_lean_sha256: str | None = None,
) -> dict[str, Any]:
    path = Path(manifest_path).resolve()
    manifest = _parse_manifest(raw)
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
    repository_root = Path(repository_root or _repository_root_for_manifest(path)).resolve()
    mathlib_root = Path(mathlib_root or repository_root / ".lake" / "packages" / "mathlib").resolve()
    for field in ("packageIdentity", "packageIdentities"):
        if field in manifest:
            _validate_package_identity_shape(manifest[field], field)
    environment_identity = None
    if check_environment:
        if None in (lake_path, expected_lake_sha256, lean_path, expected_lean_sha256):
            raise _error("environment", "strict verification requires explicit Lake and Lean paths and digests")
        environment_identity = _verify_environment(
            manifest, repository_root, mathlib_root, expected_repository_commit,
            lake_path=lake_path, expected_lake_sha256=expected_lake_sha256,
            lean_path=lean_path, expected_lean_sha256=expected_lean_sha256,
        )
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
            evidence_status = None
            if "executionEvidence" in occurrence:
                _validate_evidence(
                    occurrence["executionEvidence"],
                    f"{module}.executionEvidence",
                    compiled,
                )
                assert isinstance(occurrence["executionEvidence"], dict)
                evidence_status = occurrence["executionEvidence"]["status"]
            declaration_kind = occurrence.get("declarationKind")
            proof_values = {declaration["isProof"] for declaration in declarations}
            if declaration_kind in {"proof", "computational", "mixed", "signature_or_default"}:
                empty_example_proof = (
                    not declarations
                    and declaration_kind == "proof"
                    and occurrence.get("commandKind") == "Lean.Parser.Command.example"
                    and evidence_status == "complete_proof_declaration"
                )
                empty_variable_signature = (
                    not declarations
                    and declaration_kind == "signature_or_default"
                    and occurrence.get("commandKind") == "Lean.Parser.Command.variable"
                    and "executionEvidence" not in occurrence
                )
                if not declarations and not (empty_example_proof or empty_variable_signature):
                    raise _error(module, "scope declaration list is empty for classified declaration")
                if declaration_kind == "proof" and proof_values != {True}:
                    if not empty_example_proof:
                        raise _error(module, "proof classification disagrees with declaration isProof")
                if declaration_kind == "computational" and proof_values != {False}:
                    irreducible_with_proof_helper = (
                        proof_values == {False, True}
                        and "Lean.Elab.Command.command_Irreducible_def____"
                        in occurrence.get("ancestors", [])
                    )
                    if not irreducible_with_proof_helper:
                        raise _error(module, "computational classification disagrees with declaration isProof")
                if declaration_kind == "mixed" and proof_values != {False, True}:
                    raise _error(module, "mixed classification disagrees with declaration isProof")
            _string(occurrence.get("reason"), f"{module}.occurrence.reason")
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
    summary = {"kind": KIND, "reportSchema": SCHEMA, "modules": len(modules), "occurrences": total_occurrences, "actions": dict(sorted(action_counts.items()))}
    if environment_identity is not None:
        summary["leanIdentity"] = environment_identity
    return summary


def verify_manifest(
    manifest_path: str | Path,
    *,
    repository_root: str | Path | None = None,
    mathlib_root: str | Path | None = None,
    expected_repository_commit: str | None = None,
    require_complete: bool = True,
    check_environment: bool = False,
) -> dict[str, Any]:
    """Diagnostic structural/source verification only.

    Strict verification is exposed separately as :func:`verify_strict`; this
    API intentionally permits fixture/partial checks and must not be used as
    a campaign acceptance decision.
    """
    snapshot = _read_manifest_snapshot(manifest_path)
    return _verify_manifest(
        snapshot.path, raw=snapshot.raw, repository_root=repository_root,
        mathlib_root=mathlib_root, expected_repository_commit=expected_repository_commit,
        require_complete=require_complete, check_environment=check_environment,
    )


def verify_strict(
    manifest_path: str | Path, *, repository_root: str | Path, mathlib_root: str | Path,
    expected_sha256: str, lake_path: str | Path, expected_lake_sha256: str,
    lean_path: str | Path, expected_lean_sha256: str,
    expected_repository_commit: str | None = None, timeout: int = 3600,
    dependency_map: str | Path | Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Run non-bypassable production verification and fresh consistency checks."""
    snapshot = _read_manifest_snapshot(manifest_path)
    expected = _hash(expected_sha256, "expected-sha256")
    if snapshot.digest != expected:
        raise _error("expected-sha256", f"raw manifest bytes differ: {snapshot.digest} != {expected}")
    manifest = _parse_manifest(snapshot.raw)
    repository = Path(repository_root).resolve()
    mathlib = Path(mathlib_root).resolve()
    lake = Path(lake_path).resolve()
    lean = Path(lean_path).resolve()
    summary = _verify_manifest(
        snapshot.path, raw=snapshot.raw, repository_root=repository, mathlib_root=mathlib,
        expected_repository_commit=expected_repository_commit, require_complete=True,
        check_environment=True, lake_path=lake, expected_lake_sha256=expected_lake_sha256,
        lean_path=lean, expected_lean_sha256=expected_lean_sha256,
    )
    effective_subprocess = recompute_source_consistency(
        snapshot.path, repository_root=repository, mathlib_root=mathlib, timeout=timeout,
        manifest=manifest, manifest_snapshot=snapshot, lake_path=lake, lean_path=lean,
        expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
        dependency_map=dependency_map,
    )
    _assert_manifest_snapshot(snapshot)
    _, lake_digest, _ = _checked_binary_digest(lake, expected_lake_sha256, "lake")
    _, lean_digest, _ = _checked_binary_digest(lean, expected_lean_sha256, "lean")
    return {
        **summary,
        "kind": "simp_engine_boundary_manifest_source_verification",
        "expectedSha256": snapshot.digest,
        "manifestSha256": snapshot.digest,
        "lakePath": str(lake), "lakeSha256": lake_digest,
        "leanPath": str(lean), "leanSha256": lean_digest,
        "subprocessEnvironment": effective_subprocess,
        "sourceConsistencyVerified": True,
        "independentSemanticOracleVerified": False,
        "recomputed": "syntax_scope_declarations",
    }


def _import_module_path(name: str) -> str | None:
    """Translate a Mathlib header import name to its source module path."""
    if not name.startswith("Mathlib."):
        return None
    return name.replace(".", "/") + ".lean"


def _dependency_map_records(
    dependency_map: str | Path | Mapping[str, Any],
) -> dict[str, dict[str, Any]]:
    """Read and validate a source-bound dependency map for scheduling.

    The map is intentionally not treated as evidence of inventory contents.
    Its source hashes and exact module membership only authorize use of its
    import edges to choose child boundaries.
    """
    if isinstance(dependency_map, Mapping):
        value: object = dependency_map
    else:
        map_path = Path(dependency_map).resolve()
        try:
            value = json.loads(map_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise _error("recompute", f"cannot read dependency map: {exc}") from exc
    if not isinstance(value, dict) or not value:
        raise _error("recompute", "dependency map must be a nonempty object")
    result: dict[str, dict[str, Any]] = {}
    for key, raw in value.items():
        if not isinstance(key, str) or "@" not in key:
            raise _error("recompute", "dependency map key is invalid")
        module, source_hash = key.rsplit("@", 1)
        if not module.startswith("Mathlib/") or not module.endswith(".lean"):
            raise _error("recompute", f"dependency map module is invalid: {module!r}")
        _hash(source_hash, f"dependency map source hash for {module}")
        if not isinstance(raw, Mapping):
            raise _error("recompute", f"dependency map record is invalid: {module}")
        if set(raw) != {"module", "sourceHash", "dependencies"}:
            raise _error("recompute", f"dependency map fields are invalid: {module}")
        if raw.get("module") != module or raw.get("sourceHash") != source_hash:
            raise _error("recompute", f"dependency map identity disagrees for {module}")
        dependencies = raw.get("dependencies")
        if not isinstance(dependencies, list) or not all(
            isinstance(name, str) and name for name in dependencies
        ):
            raise _error("recompute", f"dependency map imports are invalid: {module}")
        if module in result:
            raise _error("recompute", f"dependency map contains duplicate module: {module}")
        result[module] = {
            "sourceHash": source_hash,
            "dependencies": list(dependencies),
        }
    return result


def _fresh_inventory_batches_by_closure(
    source_paths: list[Path], module_names: list[str], *,
    dependency_map: str | Path | Mapping[str, Any] | None,
    max_import_modules: int,
) -> list[list[Path]]:
    """Partition sources so every child has a bounded transitive import union."""
    if dependency_map is None:
        return [[path] for path in source_paths]
    records = _dependency_map_records(dependency_map)
    requested = set(module_names)
    if len(requested) != len(module_names):
        raise _error("recompute", "duplicate module name in inventory request")
    mapped = set(records)
    if mapped != requested:
        missing = sorted(requested - mapped)
        extra = sorted(mapped - requested)
        raise _error(
            "recompute",
            f"dependency map module set differs: missing={missing[:5]}, extra={extra[:5]}",
        )

    # The map's source hash is the identity that makes its scheduling edges
    # applicable to this run.  Check each live source before launching any
    # child; this also catches a map copied from a different manifest.
    for path, module in zip(source_paths, module_names):
        try:
            actual_hash = sha256(path.read_bytes())
        except OSError as exc:
            raise _error("recompute", f"cannot read inventory source {path}: {exc}") from exc
        if actual_hash != records[module]["sourceHash"]:
            raise _error("recompute", f"dependency map source hash differs for {module}")

    direct = {
        module: tuple(
            dependency for dependency in (
                _import_module_path(name) for name in records[module]["dependencies"]
            ) if dependency is not None and dependency in records
        )
        for module in module_names
    }
    closures: dict[str, frozenset[str]] = {}

    def closure(module: str, stack: tuple[str, ...] = ()) -> frozenset[str]:
        cached = closures.get(module)
        if cached is not None:
            return cached
        if module in stack:
            # Lean rejects cyclic imports, but treating a malformed map's cycle
            # as the current node keeps this scheduler total before the strict
            # child check fails on the actual source imports.
            return frozenset({module})
        result = {module}
        for dependency in direct[module]:
            result.update(closure(dependency, (*stack, module)))
        checked = frozenset(result)
        closures[module] = checked
        return checked

    batches: list[list[Path]] = []
    current: list[Path] = []
    current_closure: set[str] = set()
    for path, module in zip(source_paths, module_names):
        module_closure = set(closure(module))
        if current and len(current_closure | module_closure) > max_import_modules:
            batches.append(current)
            current = []
            current_closure = set()
        current.append(path)
        current_closure.update(module_closure)
    if current:
        batches.append(current)
    return batches


def _available_memory_bytes() -> int:
    """Return conservative immediately free memory on supported local hosts."""
    if sys.platform == "darwin":
        result = subprocess.run(
            ["vm_stat"], text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=5, check=False,
        )
        if result.returncode:
            raise RuntimeError(f"vm_stat failed: {result.stderr.strip()}")
        lines = result.stdout.splitlines()
        if not lines:
            raise RuntimeError("vm_stat returned no output")
        match = re.search(r"page size of (\d+) bytes", lines[0])
        if match is None:
            raise RuntimeError("vm_stat omitted page size")
        page_size = int(match.group(1))
        pages: dict[str, int] = {}
        for line in lines[1:]:
            item = re.fullmatch(r"([^:]+):\s*(\d+)\.?", line.strip())
            if item is not None:
                pages[item.group(1)] = int(item.group(2))
        try:
            return page_size * (pages["Pages free"] + pages["Pages speculative"])
        except KeyError as exc:
            raise RuntimeError(f"vm_stat omitted {exc.args[0]}") from exc
    if sys.platform.startswith("linux"):
        try:
            text = Path("/proc/meminfo").read_text(encoding="utf-8")
        except OSError as exc:
            raise RuntimeError(f"cannot read /proc/meminfo: {exc}") from exc
        match = re.search(r"^MemAvailable:\s*(\d+)\s+kB$", text, re.MULTILINE)
        if match is None:
            raise RuntimeError("/proc/meminfo omitted MemAvailable")
        return int(match.group(1)) * 1024
    raise RuntimeError(f"memory telemetry is unsupported on {sys.platform}")


def _inventory_memory_guard(_pid: int) -> str | None:
    """Stop a child before it consumes the host's final memory reserve."""
    try:
        available = _available_memory_bytes()
    except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
        return f"memory telemetry unavailable: {exc}"
    if available < FRESH_INVENTORY_MIN_FREE_MEMORY_BYTES:
        return (
            f"available memory {available} is below the strict verifier reserve "
            f"{FRESH_INVENTORY_MIN_FREE_MEMORY_BYTES}"
        )
    return None


def _run_fresh_inventory_batches(
    source_paths: list[Path], *, repository: Path, timeout: int,
    lake_path: Path | None = None, expected_lake_sha256: str | None = None,
    module_names: list[str] | None = None,
    dependency_map: str | Path | Mapping[str, Any] | None = None,
    max_import_modules: int = FRESH_INVENTORY_MAX_IMPORT_MODULES,
) -> list[str]:
    """Run the independent header-import inventory in bounded fresh processes.

    ``lean_toolchain_cache.py --header-imports`` creates one import environment
    for each requested source and keeps those environments alive until the
    child exits.  Grouping by source count consequently gives no useful memory
    bound.  When a source-bound header dependency map is supplied, batches are
    formed by the union of each source's transitive Mathlib closure.  The map
    is a scheduling input only: every requested module must be present, every
    source hash is checked against the live file, and no inventory result is
    read from it.  A missing map deliberately selects singleton children.
    """
    if max_import_modules <= 0:
        raise _error("recompute", "max_import_modules must be positive")
    dependency_map_identity: tuple[Path, tuple[int, int, int, int], bytes] | None = None
    if module_names is not None and len(module_names) != len(source_paths):
        raise _error("recompute", "module name count does not match source paths")
    if module_names is None:
        # Arbitrary fixture paths have no authenticated Mathlib module names.
        # Keep the safe process-isolation behavior rather than guessing names.
        batches = [[path] for path in source_paths]
    else:
        scheduled_map = dependency_map
        if isinstance(dependency_map, (str, Path)):
            map_path = Path(dependency_map).resolve()
            try:
                map_stat = map_path.stat()
                map_raw = map_path.read_bytes()
                scheduled_map = json.loads(map_raw)
            except (OSError, json.JSONDecodeError) as exc:
                raise _error("recompute", f"cannot read dependency map: {exc}") from exc
            dependency_map_identity = (
                map_path,
                (map_stat.st_dev, map_stat.st_ino, map_stat.st_size, map_stat.st_mtime_ns),
                map_raw,
            )
        batches = _fresh_inventory_batches_by_closure(
            source_paths,
            module_names,
            dependency_map=scheduled_map,
            max_import_modules=max_import_modules,
        )
    command_prefix = [
        sys.executable,
        str(repository / "Experiment" / "lean_toolchain_cache.py"),
        "inventory",
        "--header-imports",
    ]
    if lake_path is not None and expected_lake_sha256 is not None:
        _assert_pinned_lake(lake_path, expected_lake_sha256)
        environment = _pinned_lake_environment(lake_path, expected_lake_sha256)
    else:
        environment = nullcontext()
    outputs: list[str] = []
    with environment:
        for batch_index, batch in enumerate(batches, start=1):
            command = [*command_prefix, *(str(path) for path in batch)]
            result = run_process(
                command, cwd=repository, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=timeout, check=False,
                resource_guard=_inventory_memory_guard,
            )
            if result.returncode:
                raise _error(
                    "recompute",
                    f"inventory batch {batch_index} failed with status "
                    f"{result.returncode}:\n{result.stdout[-4000:]}",
                )
            outputs.append(result.stdout)
    if dependency_map_identity is not None:
        map_path, identity, raw = dependency_map_identity
        try:
            current_stat = map_path.stat()
            current_raw = map_path.read_bytes()
        except OSError as exc:
            raise _error("recompute", f"dependency map changed during inventory: {exc}") from exc
        current_identity = (
            current_stat.st_dev, current_stat.st_ino,
            current_stat.st_size, current_stat.st_mtime_ns,
        )
        if current_identity != identity or current_raw != raw:
            raise _error("recompute", "dependency map changed during inventory")
    return outputs


def recompute_inventory(
    manifest_path: str | Path, *, mathlib_root: str | Path, repository_root: str | Path,
    timeout: int = 3600, manifest: dict[str, Any] | None = None,
    manifest_snapshot: ManifestSnapshot | None = None,
    lake_path: Path | None = None, lean_path: Path | None = None,
    expected_lake_sha256: str | None = None, expected_lean_sha256: str | None = None,
    dependency_map: str | Path | Mapping[str, Any] | None = None,
) -> None:
    """Freshly run the syntax inventory and compare source-backed records.

    This pass intentionally omits scope/declaration recomputation: those are
    compiler/frontend observations and remain covered by their own producer
    protocol.  It is separate from :func:`verify_manifest` because it launches
    a potentially long Lean process over the complete corpus.
    """
    path = Path(manifest_path).resolve()
    snapshot = manifest_snapshot or _read_manifest_snapshot(path)
    manifest = manifest or _parse_manifest(snapshot.raw)
    mathlib = Path(mathlib_root).resolve(); repository = Path(repository_root).resolve()
    before = _freshness_snapshot(path, manifest, repository, mathlib, manifest_snapshot=snapshot, lake_path=lake_path, lean_path=lean_path, expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256)
    source_paths = [mathlib / module["module"] for module in manifest["modules"]]
    module_names = [module["module"] for module in manifest["modules"]]
    outputs = _run_fresh_inventory_batches(
        source_paths,
        repository=repository,
        timeout=timeout,
        lake_path=lake_path,
        expected_lake_sha256=expected_lake_sha256,
        module_names=module_names,
        dependency_map=dependency_map,
    )
    actual: dict[str, list[tuple[int, int, str, str, int, int, str]]] = {}
    fallbacks: set[str] = set()
    deferred: set[str] = set()
    by_path = {str(p.resolve()): module["module"] for p, module in zip(source_paths, manifest["modules"])}
    for output in outputs:
        for line in output.splitlines():
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
    _assert_fresh(before, path, manifest, repository, mathlib, "inventory subprocess", manifest_snapshot=snapshot, lake_path=lake_path, lean_path=lean_path, expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256)


def _freshness_snapshot(
    manifest_path: Path, manifest: dict[str, Any], repository_root: Path, mathlib_root: Path,
    *, manifest_snapshot: ManifestSnapshot | None = None,
    lake_path: Path | None = None, lean_path: Path | None = None,
    expected_lake_sha256: str | None = None, expected_lean_sha256: str | None = None,
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
    binaries = {}
    subprocess_identity = None
    if lake_path is not None and expected_lake_sha256 is not None:
        subprocess_identity = _assert_pinned_lake(lake_path, expected_lake_sha256)
    for label, executable, expected in (
        ("lake", lake_path, expected_lake_sha256), ("lean", lean_path, expected_lean_sha256)
    ):
        if executable is not None:
            try:
                resolved = executable.resolve()
                if expected is not None:
                    resolved, digest, stat = _checked_binary_digest(resolved, expected, label)
                else:
                    stat = resolved.stat()
                    digest = sha256(resolved.read_bytes())
                binaries[label] = {
                    "path": str(resolved),
                    "sha256": digest,
                    "device": stat.st_dev, "inode": stat.st_ino,
                    "size": stat.st_size, "mtime_ns": stat.st_mtime_ns,
                }
            except OSError as exc:
                raise _error("recompute", f"cannot snapshot {label} executable: {exc}") from exc
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
        "manifest": manifest_snapshot.digest if manifest_snapshot is not None else sha256(manifest_path.read_bytes()),
        "sources": source_hashes,
        "implementation": implementation,
        "environment": environment,
        "binaries": binaries,
        "subprocess": subprocess_identity,
        "repositoryGit": git_state(repository_root),
        "mathlibGit": git_state(mathlib_root),
    }


def _assert_fresh(
    before: dict[str, Any], manifest_path: Path, manifest: dict[str, Any],
    repository_root: Path, mathlib_root: Path, label: str,
    *, manifest_snapshot: ManifestSnapshot | None = None,
    lake_path: Path | None = None, lean_path: Path | None = None,
    expected_lake_sha256: str | None = None, expected_lean_sha256: str | None = None,
) -> None:
    if manifest_snapshot is not None:
        _assert_manifest_snapshot(manifest_snapshot)
    after = _freshness_snapshot(
        manifest_path, manifest, repository_root, mathlib_root,
        manifest_snapshot=manifest_snapshot, lake_path=lake_path, lean_path=lean_path,
        expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
    )
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


def _scope_recompute_root(repository_root: Path) -> Path:
    """Return the only checkout whose imported scope helpers can safely use."""
    root = repository_root.resolve()
    verifier_root = Path(__file__).resolve().parents[1]
    if root != verifier_root:
        raise _error(
            "recompute",
            "fresh scope/evidence helpers are bound to the verifier checkout; "
            f"requested repository_root is {root}",
        )
    return root


def _declaration_key(value: dict[str, Any]) -> tuple[Any, ...]:
    return tuple(value[field] for field in (
        "module", "name", "startByte", "endByte", "selectionStartByte",
        "selectionEndByte", "isProof",
    ))


def _fresh_scope_and_declarations(
    manifest_path: Path, manifest: dict[str, Any], repository_root: Path,
    mathlib_root: Path, timeout: int, *, manifest_snapshot: ManifestSnapshot | None = None,
    lake_path: Path | None = None, lean_path: Path | None = None,
    expected_lake_sha256: str | None = None, expected_lean_sha256: str | None = None,
) -> None:
    """Compare fresh Scope.lean records with every authenticated manifest fact.

    The scope classifier is the current checked frontend implementation, so
    this is a fresh-output consistency check rather than a proof that its
    semantic policy is independent.  The independent checks here bind its
    output to source ranges, parser ancestry, declarations, and manifest IDs;
    the policy's semantic trust boundary remains the Scope.lean implementation.
    """
    _scope_recompute_root(repository_root)
    specs = [
        scope.ModuleSpec(
            _compiled_module(module["module"]),
            mathlib_root / module["module"],
            len(module["occurrences"]),
        )
        for module in manifest["modules"]
    ]
    before = _freshness_snapshot(
        manifest_path, manifest, repository_root, mathlib_root,
        manifest_snapshot=manifest_snapshot, lake_path=lake_path, lean_path=lean_path,
        expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
    )
    occurrences, declarations, fallbacks = scope.load_records_with_fallbacks(
        specs, batch_size=128, timeout=timeout
    )
    _assert_fresh(
        before, manifest_path, manifest, repository_root, mathlib_root, "scope subprocess",
        manifest_snapshot=manifest_snapshot, lake_path=lake_path, lean_path=lean_path,
        expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
    )
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
                    manifest_path, manifest, repository_root, mathlib_root,
                    manifest_snapshot=manifest_snapshot, lake_path=lake_path, lean_path=lean_path,
                    expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
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
                    mathlib_root, "execution evidence subprocess",
                    manifest_snapshot=manifest_snapshot, lake_path=lake_path, lean_path=lean_path,
                    expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
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


def _recompute_source_consistency_body(
    manifest_path: str | Path, *, repository_root: Path, mathlib_root: Path, timeout: int,
    manifest: dict[str, Any] | None = None, manifest_snapshot: ManifestSnapshot | None = None,
    lake_path: Path | None = None, lean_path: Path | None = None,
    expected_lake_sha256: str | None = None, expected_lean_sha256: str | None = None,
    dependency_map: str | Path | Mapping[str, Any] | None = None,
) -> None:
    """Run fresh parser/frontend checks for same-producer source consistency.

    This result is deliberately not campaign acceptance.  Final acceptance
    still requires independent declaration/replay, cold-tree, and policy
    oracles; the imported Scope.lean implementation is part of this check's
    trust boundary.
    """
    path = Path(manifest_path).resolve()
    snapshot = manifest_snapshot or _read_manifest_snapshot(path)
    manifest = manifest or _parse_manifest(snapshot.raw)
    recompute_inventory(
        path, mathlib_root=mathlib_root, repository_root=repository_root, timeout=timeout,
        manifest=manifest, manifest_snapshot=snapshot, lake_path=lake_path, lean_path=lean_path,
        expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
        dependency_map=dependency_map,
    )
    _fresh_scope_and_declarations(
        path, manifest, repository_root, mathlib_root, timeout,
        manifest_snapshot=snapshot, lake_path=lake_path, lean_path=lean_path,
        expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
    )


def recompute_source_consistency(
    manifest_path: str | Path, *, repository_root: Path, mathlib_root: Path, timeout: int,
    manifest: dict[str, Any] | None = None, manifest_snapshot: ManifestSnapshot | None = None,
    lake_path: Path | None = None, lean_path: Path | None = None,
    expected_lake_sha256: str | None = None, expected_lean_sha256: str | None = None,
    dependency_map: str | Path | Mapping[str, Any] | None = None,
) -> dict[str, str] | None:
    """Run fresh checks under the authenticated Lake environment."""
    if lake_path is None or expected_lake_sha256 is None:
        return _recompute_source_consistency_body(
            manifest_path, repository_root=repository_root, mathlib_root=mathlib_root,
            timeout=timeout, manifest=manifest, manifest_snapshot=manifest_snapshot,
            lake_path=lake_path, lean_path=lean_path,
            expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
            dependency_map=dependency_map,
        )
    with _pinned_lake_environment(lake_path, expected_lake_sha256) as effective:
        _assert_pinned_lake(lake_path, expected_lake_sha256)
        _recompute_source_consistency_body(
            manifest_path, repository_root=repository_root, mathlib_root=mathlib_root,
            timeout=timeout, manifest=manifest, manifest_snapshot=manifest_snapshot,
            lake_path=lake_path, lean_path=lean_path,
            expected_lake_sha256=expected_lake_sha256, expected_lean_sha256=expected_lean_sha256,
            dependency_map=dependency_map,
        )
        return effective


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("verify", "inspect"):
        command = commands.add_parser(name)
        command.add_argument("manifest")
        command.add_argument("--repository-root", type=Path)
        command.add_argument("--mathlib-root", type=Path)
        command.add_argument("--expected-repository-commit")
        command.add_argument(
            "--dependency-map", type=Path,
            help="fresh source-bound header map used only to bound inventory child closures",
        )
        command.add_argument("--timeout", type=int, default=3600)
        if name == "verify":
            command.add_argument("--expected-sha256", required=True, help="SHA-256 of the exact manifest bytes")
            command.add_argument("--lake-path", type=Path, required=True)
            command.add_argument("--expected-lake-sha256", required=True)
            command.add_argument("--lean-path", type=Path, required=True)
            command.add_argument("--expected-lean-sha256", required=True)
        else:
            command.add_argument("--allow-partial", action="store_true", help="inspect a prefix/fixture")
            command.add_argument("--skip-environment", action="store_true", help="offline structural/source checks")
            command.add_argument("--recompute", action="store_true", help="run the expensive parser inventory only")
    args = parser.parse_args()
    manifest_path = Path(args.manifest).resolve()
    repository = (args.repository_root or _repository_root_for_manifest(manifest_path)).resolve()
    mathlib = (args.mathlib_root or repository / ".lake" / "packages" / "mathlib").resolve()
    try:
        if args.command == "verify":
            receipt = verify_strict(
                manifest_path,
                repository_root=repository,
                mathlib_root=mathlib,
                expected_sha256=args.expected_sha256,
                lake_path=args.lake_path,
                expected_lake_sha256=args.expected_lake_sha256,
                lean_path=args.lean_path,
                expected_lean_sha256=args.expected_lean_sha256,
                expected_repository_commit=args.expected_repository_commit,
                timeout=args.timeout,
                dependency_map=args.dependency_map,
            )
            print(json.dumps(receipt, sort_keys=True))
        else:
            summary = verify_manifest(
                manifest_path,
                repository_root=repository,
                mathlib_root=mathlib,
                expected_repository_commit=args.expected_repository_commit,
                require_complete=not args.allow_partial,
                # Inspection is diagnostic-only.  Strict environment and
                # executable authentication belong exclusively to verify.
                check_environment=False,
            )
            if args.recompute:
                recompute_inventory(
                    manifest_path,
                    mathlib_root=mathlib,
                    repository_root=repository,
                    timeout=args.timeout,
                    dependency_map=args.dependency_map,
                )
            print(json.dumps({
                **summary,
                "kind": "simp_engine_boundary_manifest_inspection",
                "inspection": "syntax" if args.recompute else "structural",
            }, sort_keys=True))
    except Exception as exc:
        print(f"simp boundary manifest verification failed: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc


if __name__ == "__main__":
    main()
