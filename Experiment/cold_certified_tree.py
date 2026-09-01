#!/usr/bin/env python3
"""Closed, deterministic orchestration for cold Mathlib certificates.

This module owns the part of a full-tree run that must be true before a Lean
process is started: the source manifest and dependency map form one closed
join, their hashes are stable, and the graph has a deterministic topological
order.  Compilation is deliberately a sequential callback.  A callback may
return a :class:`cold_certified_module.Certification` or an already materialized
record; either way a checkpoint is written only after its bytes have been
revalidated.  Existing checkpoints are accepted only when every identity they
carry still agrees with the immutable plan.

The runner is intentionally conservative.  It never guesses a missing edge,
uses stock output as a translated dependency, repairs a partial family, or
reuses a receipt whose plan/source/dependency identity has changed.
"""
from __future__ import annotations

from dataclasses import dataclass
import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

import certified_module as base
import cold_certified_module as cold
import cold_certified_cone_publication as publication
from translated_imports import ImportEnvironment, build_import_environment


KIND = "cold_certified_tree_plan"
SCHEMA = 1
CHECKPOINT_KIND = "cold_certified_tree_checkpoint"
CHECKPOINT_SCHEMA = 1
REPORT_KIND = "cold_certified_tree_run"
REPORT_SCHEMA = 1


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _digest(path: Path) -> str:
    return base.sha256(path)


def _regular(path: str | Path, *, label: str) -> Path:
    if not isinstance(path, (str, Path)):
        raise RuntimeError(f"{label} is not an immutable regular file: {path!r}")
    value = Path(path).expanduser().absolute()
    if value.is_symlink() or not value.is_file():
        raise RuntimeError(f"{label} is not an immutable regular file: {value}")
    return value


def _directory(path: str | Path, *, label: str) -> Path:
    if not isinstance(path, (str, Path)):
        raise RuntimeError(f"{label} is not an immutable directory: {path!r}")
    value = Path(path).expanduser().absolute()
    if value.is_symlink() or not value.is_dir():
        raise RuntimeError(f"{label} is not an immutable directory: {value}")
    return value


def _read_json(path: str | Path, *, label: str) -> tuple[Path, bytes, dict[str, Any], str]:
    checked = _regular(path, label=label)
    payload = checked.read_bytes()
    try:
        value = json.loads(payload)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"{label} is not valid JSON: {checked}: {error}") from error
    if not isinstance(value, dict):
        raise RuntimeError(f"{label} root must be an object")
    return checked, payload, value, sha256_bytes(payload)


def _canonical_module(raw: Any) -> str:
    if not isinstance(raw, str) or not raw:
        raise RuntimeError(f"invalid Mathlib module identity: {raw!r}")
    value = raw.replace("\\", "/")
    if value.endswith(".lean"):
        if not value.startswith("Mathlib/"):
            raise RuntimeError(f"module is outside Mathlib: {raw!r}")
        relative = value
    else:
        if value.startswith("Mathlib."):
            relative = value.replace(".", "/") + ".lean"
        elif value == "Mathlib":
            relative = "Mathlib.lean"
        else:
            raise RuntimeError(f"module is outside Mathlib: {raw!r}")
    parts = relative.split("/")
    if any(not part or part in {".", ".."} or "\0" in part for part in parts):
        raise RuntimeError(f"invalid Mathlib module identity: {raw!r}")
    return relative


def dotted_module(module: str) -> str:
    """Return the Lean dotted spelling for a canonical ``.lean`` module."""
    canonical = _canonical_module(module)
    return canonical[:-5].replace("/", ".")


def _hash_field(row: Mapping[str, Any], *, label: str) -> str:
    values = [row.get(key) for key in ("sourceHash", "moduleHash", "sourceSha256")]
    found = [value for value in values if value is not None]
    if not found or any(not isinstance(value, str) or len(value) != 64 or any(char not in "0123456789abcdef" for char in value) for value in found):
        raise RuntimeError(f"{label} has no valid source hash")
    if len(set(found)) != 1:
        raise RuntimeError(f"{label} has conflicting source hashes")
    return found[0]


def _dependency_names(raw: Any, *, label: str) -> tuple[str, ...]:
    if isinstance(raw, Mapping):
        if "dependencies" not in raw:
            raise RuntimeError(f"{label} dependencies are missing")
        raw = raw.get("dependencies")
    if not isinstance(raw, (list, tuple)):
        raise RuntimeError(f"{label} dependencies are not an array")
    result = tuple(sorted({_canonical_module(value) for value in raw}))
    return result


def _source_file(path: str | Path, module: str, *, label: str) -> Path:
    checked = _regular(path, label=label)
    relative = Path(module)
    if tuple(checked.parts[-len(relative.parts):]) != relative.parts:
        raise RuntimeError(f"{label} has a non-canonical module path for {module}")
    return checked


@dataclass(frozen=True)
class PlanNode:
    module: str
    source_hash: str
    dependencies: tuple[str, ...]
    disposition: str
    source_path: str | None
    applied_path: str | None
    applied_hash: str

    def result(self) -> dict[str, Any]:
        return {
            "module": self.module,
            "sourceHash": self.source_hash,
            "dependencies": list(self.dependencies),
            "disposition": self.disposition,
            "sourcePath": self.source_path,
            "appliedPath": self.applied_path,
            "appliedHash": self.applied_hash,
        }


@dataclass(frozen=True)
class TreePlan:
    manifest_path: Path
    manifest_hash: str
    dependency_map_path: Path
    dependency_map_hash: str
    order: tuple[str, ...]
    nodes: Mapping[str, PlanNode]
    excluded: tuple[str, ...]
    complete_corpus: bool
    plan_hash: str

    def result(self) -> dict[str, Any]:
        return {
            "kind": KIND,
            "schema": SCHEMA,
            "manifest": {"path": str(self.manifest_path), "sha256": self.manifest_hash},
            "dependencyMap": {"path": str(self.dependency_map_path), "sha256": self.dependency_map_hash},
            "order": list(self.order),
            "modules": {module: self.nodes[module].result() for module in sorted(self.nodes)},
            "excludedModules": list(self.excluded),
            "completeCorpus": self.complete_corpus,
            "planHash": self.plan_hash,
        }


def _plan_hash(value: Mapping[str, Any]) -> str:
    identity = {key: value[key] for key in value if key != "planHash"}
    encoded = json.dumps(identity, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
    return sha256_bytes(encoded)


def _topological(nodes: Mapping[str, PlanNode]) -> tuple[str, ...]:
    remaining = {module: set(node.dependencies) for module, node in nodes.items()}
    reverse: dict[str, set[str]] = {module: set() for module in nodes}
    for module, dependencies in remaining.items():
        for dependency in dependencies:
            reverse[dependency].add(module)
    ready = sorted(module for module, deps in remaining.items() if not deps)
    order: list[str] = []
    while ready:
        module = ready.pop(0)
        order.append(module)
        for consumer in sorted(reverse[module]):
            remaining[consumer].discard(module)
            if not remaining[consumer]:
                ready.append(consumer)
        ready.sort()
    if len(order) != len(nodes):
        cyclic = sorted(module for module, deps in remaining.items() if deps)
        raise RuntimeError(f"dependency graph contains a cycle: {cyclic}")
    return tuple(order)


def build_plan(
    manifest: str | Path,
    dependency_map: str | Path,
    *,
    source_root: str | Path | None = None,
    applied_root: str | Path | None = None,
    source_bundle: Mapping[str, Mapping[str, Any]] | None = None,
    excluded_modules: Sequence[str] = (),
) -> TreePlan:
    """Validate a closed manifest/dependency join and construct its plan.

    Every manifest module is represented, including deliberately excluded
    source modules.  Exclusions affect execution disposition only; they cannot
    silently remove nodes needed by dependency closure.
    """
    manifest_path, manifest_bytes, manifest_value, manifest_hash = _read_json(manifest, label="manifest")
    if manifest_value.get("kind") != "simp_engine_boundary_manifest":
        raise RuntimeError("manifest kind is not the pinned boundary manifest")
    if manifest_value.get("allowDirty") is not False:
        raise RuntimeError("dirty manifest is not accepted")
    if manifest_value.get("allowUnresolved") is not False:
        raise RuntimeError("unresolved manifest is not accepted")
    if manifest_value.get("allowUnclassified") is True:
        raise RuntimeError("unclassified manifest is not accepted")
    records = manifest_value.get("modules")
    if not isinstance(records, list) or not records:
        raise RuntimeError("manifest modules are incomplete")
    manifest_rows: dict[str, Mapping[str, Any]] = {}
    for raw in records:
        if not isinstance(raw, Mapping):
            raise RuntimeError("manifest contains an invalid module record")
        module = _canonical_module(raw.get("module"))
        if module in manifest_rows:
            raise RuntimeError(f"manifest contains duplicate module: {module}")
        source_hash = _hash_field(raw, label=f"manifest module {module}")
        if raw.get("unresolved") is True or raw.get("dirty") is True or raw.get("status") in {"dirty", "unresolved"}:
            raise RuntimeError(f"manifest module is dirty or unresolved: {module}")
        manifest_rows[module] = raw

    dep_path, dep_bytes, dep_value, dependency_map_hash = _read_json(dependency_map, label="dependency map")
    if isinstance(dep_value.get("modules"), list):
        dep_records = dep_value["modules"]
        dep_rows: dict[str, Any] = {}
        for raw in dep_records:
            if not isinstance(raw, Mapping):
                raise RuntimeError("dependency map contains an invalid module record")
            module = _canonical_module(raw.get("module"))
            if module in dep_rows:
                raise RuntimeError(f"dependency map contains duplicate module: {module}")
            if raw.get("module") is not None and _canonical_module(raw["module"]) != module:
                raise RuntimeError(f"dependency map module identity mismatch for {module}")
            dep_rows[module] = raw
    else:
        dep_rows = {}
        for key, value in dep_value.items():
            # Durable dependency maps use ``module@sourceHash`` keys so a
            # stale map cannot be mistaken for the same module at a new
            # source revision.  Plain module keys remain accepted for small
            # callers and fixtures.
            if not isinstance(key, str):
                raise RuntimeError("dependency map key is invalid")
            module_key, separator, key_hash = key.partition("@")
            module = _canonical_module(module_key)
            if separator and (len(key_hash) != 64 or any(char not in "0123456789abcdef" for char in key_hash)):
                raise RuntimeError(f"dependency map key has invalid source hash: {key}")
            if module in dep_rows:
                raise RuntimeError(f"dependency map contains duplicate module: {module}")
            if separator:
                if not isinstance(value, Mapping) or _hash_field(value, label=f"dependency map module {module}") != key_hash:
                    raise RuntimeError(f"dependency map key/source hash mismatch for {module}")
            if isinstance(value, Mapping) and value.get("module") is not None and _canonical_module(value["module"]) != module:
                raise RuntimeError(f"dependency map module identity mismatch for {module}")
            dep_rows[module] = value
    if set(dep_rows) != set(manifest_rows):
        missing = sorted(set(manifest_rows) - set(dep_rows))
        extra = sorted(set(dep_rows) - set(manifest_rows))
        raise RuntimeError(f"manifest/dependency join is incomplete (missing={missing}, extra={extra})")

    excluded = tuple(sorted({_canonical_module(module) for module in excluded_modules}))
    unknown_excluded = sorted(set(excluded) - set(manifest_rows))
    if unknown_excluded:
        raise RuntimeError(f"excluded module is absent from manifest: {unknown_excluded}")
    manifest_excluded = tuple(sorted(module for module, row in manifest_rows.items()
                                     if row.get("disposition") == "excluded"))
    if manifest_excluded != excluded:
        raise RuntimeError("manifest excluded disposition does not match plan exclusions")
    nodes: dict[str, PlanNode] = {}
    if source_root is None and source_bundle is None:
        raise RuntimeError("complete stock/applied source bundle is required")
    source_base = _directory(source_root, label="source root") if source_root is not None else None
    applied_base = _directory(applied_root, label="applied source root") if applied_root is not None else source_base
    if source_bundle is not None and set(source_bundle) != set(manifest_rows):
        raise RuntimeError("canonical source bundle/module join is incomplete")
    for module in sorted(manifest_rows):
        manifest_row = manifest_rows[module]
        dep_row = dep_rows[module]
        if not isinstance(dep_row, Mapping):
            raise RuntimeError(f"dependency map record is invalid: {module}")
        source_hash = _hash_field(manifest_row, label=f"manifest module {module}")
        dependency_source_hash = _hash_field(dep_row, label=f"dependency map module {module}")
        if dependency_source_hash != source_hash:
            raise RuntimeError(f"source hash mismatch for {module}")
        dependencies = _dependency_names(dep_row, label=f"dependency map module {module}")
        unknown = sorted(set(dependencies) - set(manifest_rows))
        if unknown:
            raise RuntimeError(f"dependency is missing from manifest/plan for {module}: {unknown}")
        bundle = source_bundle.get(module) if source_bundle is not None else None
        if bundle is not None and not isinstance(bundle, Mapping):
            raise RuntimeError(f"source bundle record is invalid for {module}")
        stock_candidate = bundle.get("stockPath") if bundle is not None else None
        applied_candidate = bundle.get("appliedPath") if bundle is not None else None
        if stock_candidate is None:
            stock_candidate = manifest_row.get("sourcePath") or manifest_row.get("source")
        stock_path = _source_file(stock_candidate, module, label=f"stock source for {module}") if stock_candidate is not None else _source_file(source_base / Path(module), module, label=f"stock source for {module}")
        if applied_candidate is None:
            applied_candidate = manifest_row.get("appliedSourcePath")
        applied_path = _source_file(applied_candidate, module, label=f"applied source for {module}") if applied_candidate is not None else _source_file(applied_base / Path(module), module, label=f"applied source for {module}")
        if _digest(stock_path) != source_hash:
            raise RuntimeError(f"source hash mismatch for {module}")
        applied_hash = _digest(applied_path)
        if bundle is not None:
            expected_stock = bundle.get("stockHash")
            if expected_stock is None:
                expected_stock = bundle.get("sourceHash")
            expected_applied = bundle.get("appliedHash")
            if expected_applied is None:
                expected_applied = bundle.get("appliedSourceHash")
            if expected_stock != source_hash or expected_applied != applied_hash:
                raise RuntimeError(f"source bundle hash mismatch for {module}")
        source_path = str(stock_path)
        disposition = str(manifest_row.get("disposition", "eligible"))
        if disposition not in {"eligible", "excluded"}:
            raise RuntimeError(f"manifest module disposition is invalid for {module}")
        if module in excluded:
            disposition = "excluded"
        nodes[module] = PlanNode(module, source_hash, dependencies, disposition, source_path, str(applied_path), applied_hash)
    order = _topological(nodes)
    provisional = {
        "kind": KIND, "schema": SCHEMA,
        "manifest": {"path": str(manifest_path), "sha256": manifest_hash},
        "dependencyMap": {"path": str(dep_path), "sha256": dependency_map_hash},
        "order": list(order), "modules": {m: nodes[m].result() for m in sorted(nodes)},
        "excludedModules": list(excluded),
        # A manifest count is diagnostic metadata.  Whole-corpus status is
        # granted only by run_production_tree after an independently pinned
        # corpus identity and final publication audit are supplied.
        "completeCorpus": False,
    }
    return TreePlan(manifest_path, manifest_hash, dep_path, dependency_map_hash, order, nodes, excluded,
                    False, _plan_hash(provisional))


def verify_plan(plan: Mapping[str, Any] | TreePlan) -> TreePlan:
    """Reconstruct and verify a serialized plan without trusting its hash."""
    if isinstance(plan, TreePlan):
        value = plan.result()
    else:
        value = dict(plan)
    if value.get("kind") != KIND or value.get("schema") != SCHEMA:
        raise RuntimeError("invalid cold tree plan identity")
    supplied = value.get("planHash")
    if not isinstance(supplied, str) or supplied != _plan_hash(value):
        raise RuntimeError("plan hash mismatch")
    manifest = value.get("manifest"); dependency_map = value.get("dependencyMap")
    if not isinstance(manifest, Mapping) or not isinstance(dependency_map, Mapping):
        raise RuntimeError("plan input identities are incomplete")
    manifest_path = _regular(manifest.get("path"), label="manifest")
    dependency_path = _regular(dependency_map.get("path"), label="dependency map")
    if _digest(manifest_path) != manifest.get("sha256") or _digest(dependency_path) != dependency_map.get("sha256"):
        raise RuntimeError("plan input changed")
    nodes_raw = value.get("modules"); order_raw = value.get("order")
    if not isinstance(nodes_raw, Mapping) or not isinstance(order_raw, list):
        raise RuntimeError("plan graph is incomplete")
    if set(nodes_raw) != set(order_raw) or len(order_raw) != len(set(order_raw)):
        raise RuntimeError("plan module order is incomplete")
    nodes: dict[str, PlanNode] = {}
    source_bundle_for_rebuild: dict[str, dict[str, Any]] = {}
    for key, raw in nodes_raw.items():
        module = _canonical_module(key)
        if module != key or not isinstance(raw, Mapping):
            raise RuntimeError("plan module identity is invalid")
        source_hash = _hash_field(raw, label=f"plan module {module}")
        deps = _dependency_names(raw, label=f"plan module {module}")
        if any(dep not in nodes_raw for dep in deps):
            raise RuntimeError(f"plan dependency is absent: {module}")
        source_path = raw.get("sourcePath")
        applied_path = raw.get("appliedPath")
        applied_hash = raw.get("appliedHash")
        if source_path is not None:
            source = _source_file(source_path, module, label=f"source for {module}")
            if _digest(source) != source_hash:
                raise RuntimeError(f"source hash mismatch for {module}")
            source_path = str(source)
        if not isinstance(applied_path, str) or not isinstance(applied_hash, str):
            raise RuntimeError(f"complete applied source bundle is missing for {module}")
        applied = _source_file(applied_path, module, label=f"applied source for {module}")
        if _digest(applied) != applied_hash:
            raise RuntimeError(f"applied source hash mismatch for {module}")
        nodes[module] = PlanNode(module, source_hash, deps, str(raw.get("disposition", "eligible")), source_path, str(applied), applied_hash)
        source_bundle_for_rebuild[module] = {"stockPath": source_path, "stockHash": source_hash,
                                              "appliedPath": str(applied), "appliedHash": applied_hash}
    expected_order = _topological(nodes)
    if tuple(order_raw) != expected_order:
        raise RuntimeError("plan order is not stable topological order")
    excluded_raw = value.get("excludedModules", [])
    if not isinstance(excluded_raw, list):
        raise RuntimeError("plan exclusions are invalid")
    try:
        exclusions = tuple(_canonical_module(module) for module in excluded_raw)
    except RuntimeError as error:
        raise RuntimeError("plan exclusions are invalid") from error
    if tuple(sorted(exclusions)) != exclusions or len(set(exclusions)) != len(exclusions) or any(module not in nodes for module in exclusions):
        raise RuntimeError("plan exclusions are invalid")
    if type(value.get("completeCorpus")) is not bool:
        raise RuntimeError("plan corpus completeness is missing")
    canonical = build_plan(manifest_path, dependency_path, source_bundle=source_bundle_for_rebuild,
                           excluded_modules=exclusions)
    if canonical.result() != value:
        raise RuntimeError("plan graph does not match canonical manifest/dependency inputs")
    return TreePlan(manifest_path, str(manifest["sha256"]), dependency_path,
                    str(dependency_map["sha256"]), expected_order, nodes, exclusions,
                    canonical.complete_corpus, supplied)


def write_plan(path: str | Path, plan: Mapping[str, Any] | TreePlan) -> str:
    """Publish a plan once, returning its immutable byte hash."""
    checked = verify_plan(plan)
    destination = Path(path).expanduser().absolute()
    return _write_exclusive(destination, checked.result())


def load_plan(path: str | Path, *, expected_sha256: str | None = None) -> TreePlan:
    """Load one immutable serialized plan and optionally bind its byte hash."""
    _path, _payload, value, actual = _read_json(path, label="plan")
    if expected_sha256 is not None and actual != expected_sha256:
        raise RuntimeError("plan hash mismatch")
    return verify_plan(value)


def _family_complete(family: Mapping[str, Any], *, module: str, is_module: bool = True) -> dict[str, str]:
    if not isinstance(family, Mapping):
        raise RuntimeError(f"artifact family is invalid for {module}")
    suffixes = base.SUFFIXES if is_module else base.SUFFIXES[:1]
    expected = {suffix for suffix in suffixes}
    found: dict[str, str] = {}
    relative = base._module_path(dotted_module(module))
    for path_text, digest in family.items():
        path = _regular(path_text, label=f"artifact for {module}")
        if not isinstance(digest, str) or len(digest) != 64 or _digest(path) != digest:
            raise RuntimeError(f"artifact hash mismatch for {module}")
        suffix = next((suffix for suffix in suffixes if path.name == relative.with_suffix(suffix).name), None)
        if suffix is None or suffix in found:
            raise RuntimeError(f"unexpected artifact family member for {module}")
        found[suffix] = digest
    if set(found) != expected:
        raise RuntimeError(f"partial artifact family for {module}")
    return {str(Path(path_text)): digest for path_text, digest in sorted(family.items())}


def validate_checkpoint(
    checkpoint: str | Path,
    plan: Mapping[str, Any] | TreePlan,
    *,
    expected_sha256: str | None = None,
) -> dict[str, Any]:
    """Validate one immutable checkpoint and its cold certificate receipt."""
    checked_plan = verify_plan(plan)
    path, payload, value, actual_hash = _read_json(checkpoint, label="checkpoint")
    if expected_sha256 is not None and actual_hash != expected_sha256:
        raise RuntimeError("checkpoint hash mismatch")
    if value.get("kind") != CHECKPOINT_KIND or value.get("schema") != CHECKPOINT_SCHEMA or value.get("status") != "completed":
        raise RuntimeError("invalid checkpoint identity")
    if value.get("planHash") != checked_plan.plan_hash:
        raise RuntimeError("checkpoint plan hash mismatch")
    module = value.get("module")
    if not isinstance(module, str) or module not in checked_plan.nodes:
        raise RuntimeError("checkpoint module is absent from plan")
    node = checked_plan.nodes[module]
    if value.get("sourceHash") != node.source_hash or tuple(value.get("dependencies", [])) != node.dependencies:
        raise RuntimeError(f"stale checkpoint identity for {module}")
    if type(value.get("isModule")) is not bool:
        raise RuntimeError(f"checkpoint module mode is invalid for {module}")
    is_module = value["isModule"]
    family = _family_complete(value.get("artifactFamily"), module=module, is_module=is_module)
    receipt = value.get("certification")
    if not isinstance(receipt, Mapping) or not isinstance(receipt.get("path"), str) or not isinstance(receipt.get("sha256"), str):
        raise RuntimeError(f"checkpoint receipt identity is incomplete for {module}")
    receipt_path = _regular(receipt["path"], label=f"receipt for {module}")
    if _digest(receipt_path) != receipt["sha256"]:
        raise RuntimeError(f"receipt hash mismatch for {module}")
    receipt_value = json.loads(receipt_path.read_bytes())
    cert = cold.Certification(receipt_path, receipt["sha256"], receipt_value)
    # A published target is expected after the publication receipt has been
    # checked and its complete family bytes have been revalidated.  Before
    # publication, retaining the default absent-target guard catches stale
    # output roots.
    publication_ref = value.get("publication")
    cold_record = cold.verify_certification(cert, require_target_absent=publication_ref is None)
    if cold_record.get("module") != dotted_module(module) or cold_record.get("isModule") is not is_module or cold_record.get("outputArtifactFamily") != family:
        raise RuntimeError(f"checkpoint certificate does not match {module}")
    if publication_ref is not None:
        if cold_record.get("planHash") != checked_plan.plan_hash:
            raise RuntimeError(f"checkpoint certificate plan hash does not match {module}")
        if (not isinstance(cold_record.get("stock"), Mapping)
                or cold_record["stock"].get("sha256") != node.source_hash
                or not isinstance(cold_record.get("applied"), Mapping)
                or cold_record["applied"].get("sha256") != node.applied_hash):
            raise RuntimeError(f"checkpoint certificate source hashes do not match {module}")
    if publication_ref is not None:
        if not isinstance(publication_ref, Mapping) or not isinstance(publication_ref.get("path"), str) or not isinstance(publication_ref.get("sha256"), str):
            raise RuntimeError(f"checkpoint publication identity is incomplete for {module}")
        publication_path = _regular(publication_ref["path"], label=f"publication receipt for {module}")
        if _digest(publication_path) != publication_ref["sha256"]:
            raise RuntimeError(f"publication receipt hash mismatch for {module}")
        try:
            publication_value = json.loads(publication_path.read_bytes())
        except json.JSONDecodeError as error:
            raise RuntimeError(f"publication receipt changed for {module}") from error
        if not isinstance(publication_value, Mapping) or publication_value.get("module") != dotted_module(module) or publication_value.get("certification") != dict(receipt):
            raise RuntimeError(f"checkpoint publication does not match {module}")
        if type(publication_value.get("isModule")) is not bool or publication_value["isModule"] is not is_module:
            raise RuntimeError(f"checkpoint publication mode does not match {module}")
        if publication._family(publication_value.get("artifactFamily", {}), dotted_module(module), is_module) != dict(publication_value.get("artifactFamily", {})):
            raise RuntimeError(f"checkpoint publication family is incomplete for {module}")
    result = dict(value)
    result["artifactFamily"] = family
    return result


def load_checkpoints(plan: Mapping[str, Any] | TreePlan, checkpoint_root: str | Path) -> dict[str, dict[str, Any]]:
    """Validate every existing checkpoint, rejecting stale or extra records."""
    checked_plan = verify_plan(plan)
    root = _directory(checkpoint_root, label="checkpoint root")
    expected_paths = {_checkpoint_path(root, module) for module in checked_plan.order}
    unexpected = sorted(path for path in root.rglob("*") if path.is_file() or path.is_symlink() if path not in expected_paths)
    if unexpected:
        raise RuntimeError(f"unexpected or stale checkpoint: {unexpected[0]}")
    result: dict[str, dict[str, Any]] = {}
    for module in checked_plan.order:
        path = _checkpoint_path(root, module)
        if path.exists() or path.is_symlink():
            result[module] = validate_checkpoint(path, checked_plan)
    return result


def _write_exclusive(path: Path, value: Mapping[str, Any]) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2).encode() + b"\n"
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    except FileExistsError as error:
        raise RuntimeError(f"refusing to overwrite immutable record: {path}") from error
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
    except Exception:
        path.unlink(missing_ok=True)
        raise
    return sha256_bytes(encoded)


def _checkpoint_path(root: Path, module: str) -> Path:
    """Return a module checkpoint path and reject symlinked intermediate dirs."""
    path = root / (module[:-5] + ".json")
    relative = path.relative_to(root)
    current = root
    for part in relative.parts[:-1]:
        current /= part
        if current.is_symlink():
            raise RuntimeError(f"checkpoint path escapes through a symlink: {current}")
    return path


def run_tree(
    plan: Mapping[str, Any] | TreePlan,
    *,
    checkpoint_root: str | Path,
    certify: Callable[..., Any] | None = None,
    resume: bool = True,
    max_modules: int | None = None,
) -> dict[str, Any]:
    """Run modules in stable order with immutable sequential checkpoints.

    ``certify`` is a deliberately small test injection and receives
    ``(module, node, dependency_checkpoints)``.  It must
    return a ``Certification``, a checkpoint-shaped mapping, or a mapping with
    ``certification`` and ``artifactFamily`` fields.  The callback is required
    for modules not already checkpointed, which makes accidental partial runs
    fail closed instead of pretending to certify the tree.
    """
    checked_plan = verify_plan(plan)
    root = _directory(checkpoint_root, label="checkpoint root")
    if max_modules is not None and (isinstance(max_modules, bool) or max_modules <= 0):
        raise RuntimeError("max_modules must be positive")
    completed: dict[str, dict[str, Any]] = {}
    if resume:
        completed = load_checkpoints(checked_plan, root)
    elif load_checkpoints(checked_plan, root):
        raise RuntimeError("checkpoint exists while resume is disabled")
    processed = 0
    for module in checked_plan.order:
        if module in completed:
            continue
        if max_modules is not None and processed >= max_modules:
            break
        if module in checked_plan.excluded:
            raise RuntimeError(f"excluded module has no checkpoint: {module}")
        if certify is None:
            raise RuntimeError(f"no certifier supplied for uncheckpointed module: {module}")
        node = checked_plan.nodes[module]
        dependencies = {dependency: completed[dependency] for dependency in node.dependencies}
        if set(dependencies) != set(node.dependencies):
            raise RuntimeError(f"dependency checkpoint join is incomplete for {module}")
        parameters = (module, node, dependencies)
        produced = certify(*parameters)
        if isinstance(produced, cold.Certification):
            receipt = {"path": str(produced.receipt_path), "sha256": produced.receipt_sha256}
            record = produced.receipt
            family = record.get("outputArtifactFamily")
            is_module = record.get("isModule", True)
        elif isinstance(produced, Mapping):
            record = dict(produced)
            receipt = record.get("certification") or record.get("receipt")
            family = record.get("artifactFamily") or record.get("outputArtifactFamily")
            is_module = record.get("isModule", True)
        else:
            raise RuntimeError(f"certifier returned an unsupported result for {module}")
        if not isinstance(receipt, Mapping) or not isinstance(family, Mapping):
            raise RuntimeError(f"certifier returned incomplete evidence for {module}")
        checkpoint = {"kind": CHECKPOINT_KIND, "schema": CHECKPOINT_SCHEMA, "status": "completed",
                      "planHash": checked_plan.plan_hash, "module": module,
                      "sourceHash": node.source_hash, "dependencies": list(node.dependencies),
                      "isModule": is_module, "certification": dict(receipt), "artifactFamily": dict(family)}
        if isinstance(produced, Mapping) and "publication" in produced:
            publication_ref = produced["publication"]
            if not isinstance(publication_ref, Mapping):
                raise RuntimeError(f"certifier returned an invalid publication reference for {module}")
            checkpoint["publication"] = dict(publication_ref)
        path = _checkpoint_path(root, module)
        checkpoint_hash = _write_exclusive(path, checkpoint)
        completed[module] = validate_checkpoint(path, checked_plan, expected_sha256=checkpoint_hash)
        processed += 1
    report = {"kind": REPORT_KIND, "schema": REPORT_SCHEMA,
              "status": "completed" if len(completed) == len(checked_plan.order) else "partial",
              "wholeMathlib": False,
              "planComplete": len(completed) == len(checked_plan.order),
              "planHash": checked_plan.plan_hash, "order": list(checked_plan.order),
              "completed": [{"module": module, "path": str(_checkpoint_path(root, module)),
                             "sha256": _digest(_checkpoint_path(root, module))} for module in checked_plan.order if module in completed]}
    return report


def _dependency_closure(plan: TreePlan, module: str) -> tuple[str, ...]:
    seen: set[str] = set()
    pending = list(plan.nodes[module].dependencies)
    while pending:
        dependency = pending.pop()
        if dependency in seen:
            continue
        seen.add(dependency)
        pending.extend(plan.nodes[dependency].dependencies)
    return tuple(sorted(seen))


def _validate_corpus_identity(identity: Mapping[str, Any], plan: TreePlan) -> dict[str, Any]:
    """Validate an independently produced, pinned complete-corpus identity."""
    if not isinstance(identity, Mapping) or not isinstance(identity.get("path"), str) or not isinstance(identity.get("sha256"), str):
        raise RuntimeError("complete corpus identity is incomplete")
    path = _regular(identity["path"], label="complete corpus identity")
    if _digest(path) != identity["sha256"]:
        raise RuntimeError("complete corpus identity hash mismatch")
    try:
        value = json.loads(path.read_bytes())
    except json.JSONDecodeError as error:
        raise RuntimeError("complete corpus identity is not valid JSON") from error
    if not isinstance(value, Mapping) or value.get("kind") != "cold_pinned_complete_corpus" or value.get("schema") != 1 or value.get("complete") is not True:
        raise RuntimeError("complete corpus identity is not pinned")
    if value.get("manifestHash") != plan.manifest_hash or value.get("dependencyMapHash") != plan.dependency_map_hash:
        raise RuntimeError("complete corpus identity does not match plan inputs")
    modules = value.get("modules")
    if not isinstance(modules, Mapping) or set(modules) != set(plan.nodes):
        raise RuntimeError("complete corpus identity module join is incomplete")
    for module, node in plan.nodes.items():
        entry = modules.get(module)
        if not isinstance(entry, Mapping) or entry.get("sourceHash") != node.source_hash:
            raise RuntimeError(f"complete corpus identity source mismatch for {module}")
    return {"path": str(path), "sha256": identity["sha256"]}


def _read_publication_records(plan: TreePlan, receipt_root: Path,
                              expected_hashes: Mapping[str, str] | None = None) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    expected = {_checkpoint_path(receipt_root, module) for module in plan.order}
    actual = {path for path in receipt_root.rglob("*") if path.is_file() or path.is_symlink()}
    if not actual.issubset(expected):
        raise RuntimeError("unexpected or stale publication receipt")
    for module in plan.order:
        path = _checkpoint_path(receipt_root, module)
        if path.exists() or path.is_symlink():
            _regular(path, label=f"publication receipt for {module}")
            if expected_hashes is not None and str(path) in expected_hashes and _digest(path) != expected_hashes[str(path)]:
                raise RuntimeError(f"publication receipt hash mismatch for {module}")
            try:
                value = json.loads(path.read_bytes())
            except json.JSONDecodeError as error:
                raise RuntimeError(f"publication receipt changed for {module}") from error
            if not isinstance(value, dict):
                raise RuntimeError(f"publication receipt is invalid for {module}")
            records.append({"path": str(path), "sha256": _digest(path), **value})
    return records


def run_production_tree(
    plan: Mapping[str, Any] | TreePlan,
    *,
    imports: ImportEnvironment,
    oracle: base.InputFile,
    auditor: base.InputFile,
    checkpoint_root: str | Path,
    output_root: str | Path,
    staging_parent: str | Path,
    receipt_root: str | Path,
    work_parent: str | Path,
    corpus_identity: Mapping[str, Any] | None = None,
    resume: bool = True,
    timeout: float = 900,
    max_modules: int | None = None,
) -> dict[str, Any]:
    """Run the maintained cold certifier and publication lifecycle.

    This is the production entry point.  It wires strict translated imports,
    transitive certified artifact families, five-process cold certification,
    single-writer publication, and output/receipt audits.  ``run_tree`` above
    remains only the deterministic fixture seam used by unit controls.
    """
    checked_plan = verify_plan(plan)
    pinned_corpus = (_validate_corpus_identity(corpus_identity, checked_plan)
                     if corpus_identity is not None else None)
    checkpoint_dir = _directory(checkpoint_root, label="checkpoint root")
    output_dir = _directory(output_root, label="output root")
    staging_dir = _directory(staging_parent, label="staging root")
    receipt_dir = _directory(receipt_root, label="receipt root")
    work_dir = _directory(work_parent, label="certificate work root")
    if type(resume) is not bool:
        raise RuntimeError("invalid resume policy")
    if not resume:
        for label, root in (("checkpoint", checkpoint_dir), ("output", output_dir),
                            ("staging", staging_dir), ("receipt", receipt_dir), ("work", work_dir)):
            if any(path.is_file() or path.is_symlink() for path in root.rglob("*")):
                raise RuntimeError(f"--no-resume requires an empty {label} root")
    oracle = base._checked_file(oracle); auditor = base._checked_file(auditor)
    if not os.access(oracle.path, os.X_OK) or not os.access(auditor.path, os.X_OK):
        raise RuntimeError("certification tool is not executable")
    existing = load_checkpoints(checked_plan, checkpoint_dir)
    expected_publication_hashes = {
        str(item["publication"]["path"]): item["publication"]["sha256"]
        for item in existing.values() if isinstance(item.get("publication"), Mapping)
        and isinstance(item["publication"].get("path"), str)
        and isinstance(item["publication"].get("sha256"), str)
    }
    records = _read_publication_records(checked_plan, receipt_dir, expected_publication_hashes)
    publication.verify_publications(records, output_dir, receipt_root=receipt_dir)
    publications = {_canonical_module(record["module"]): record for record in records}
    for module in existing:
        publication_record = publications.get(module)
        checkpoint_publication = existing[module].get("publication")
        publication_ref = ({"path": publication_record.get("path"), "sha256": publication_record.get("sha256")}
                           if publication_record is not None else None)
        if (publication_record is None or publication_record.get("certification") != existing[module].get("certification")
                or checkpoint_publication != publication_ref):
            raise RuntimeError(f"checkpoint/publication join is incomplete for {module}")

    def certify(module: str, node: PlanNode, _ignored: Mapping[str, Any]) -> Mapping[str, Any]:
        dependency_families: dict[str, Mapping[str, str]] = {}
        for dependency in _dependency_closure(checked_plan, module):
            dependency_record = publications.get(dependency)
            if dependency_record is None:
                raise RuntimeError(f"transitive dependency publication is missing for {module}: {dependency}")
            family = dependency_record.get("artifactFamily")
            if not isinstance(family, Mapping):
                raise RuntimeError(f"dependency artifact family is missing for {module}: {dependency}")
            dependency_families[dotted_module(dependency)] = dict(family)
        cert = cold.certify_module(
            module=dotted_module(module),
            stock=base.InputFile(Path(node.source_path), node.source_hash),
            applied=base.InputFile(Path(node.applied_path), node.applied_hash),
            is_module=True, oracle=oracle, auditor=auditor, imports=imports,
            dependencies=dependency_families, work_parent=work_dir, timeout=timeout,
            plan_hash=checked_plan.plan_hash,
        )
        cold_record = cold.verify_certification(cert)
        if (cold_record.get("planHash") != checked_plan.plan_hash
                or not isinstance(cold_record.get("stock"), Mapping)
                or cold_record["stock"].get("sha256") != node.source_hash
                or not isinstance(cold_record.get("applied"), Mapping)
                or cold_record["applied"].get("sha256") != node.applied_hash):
            raise RuntimeError(f"cold receipt identity does not match plan for {module}")
        published = publication.publish(cert, output_root=output_dir,
                                        staging_parent=staging_dir, receipt_root=receipt_dir)
        publications[module] = published
        records.append(published)
        publication.verify_publications(records, output_dir, receipt_root=receipt_dir)
        return {"certification": {"path": str(cert.receipt_path), "sha256": cert.receipt_sha256},
                "artifactFamily": cert.receipt["outputArtifactFamily"], "isModule": True,
                "publication": {"path": published["path"], "sha256": published["sha256"]}}

    report = run_tree(checked_plan, checkpoint_root=checkpoint_dir, certify=certify,
                      resume=resume, max_modules=max_modules)
    publication.verify_publications(records, output_dir, receipt_root=receipt_dir)
    if pinned_corpus is not None and _validate_corpus_identity(corpus_identity, checked_plan) != pinned_corpus:
        raise RuntimeError("complete corpus identity changed during certification")
    complete = (report["status"] == "completed" and len(publications) == len(checked_plan.order)
                and pinned_corpus is not None and not checked_plan.excluded)
    report["planComplete"] = report["status"] == "completed"
    report["wholeMathlib"] = complete
    report["corpusIdentity"] = pinned_corpus
    report["publicationAudit"] = {"modules": len(publications), "artifacts": sum(len(record["artifactFamily"]) for record in records), "verified": True}
    return report


__all__ = ["TreePlan", "PlanNode", "build_plan", "verify_plan", "write_plan", "load_plan", "validate_checkpoint", "load_checkpoints", "run_tree", "run_production_tree", "dotted_module"]


def main(argv: Sequence[str] | None = None) -> int:
    """Build or validate a plan from the command line.

    Compilation remains an injected callback so a production caller can bind
    its own source materializer and cold certificate publication policy.  The
    command line mode is useful for immutable plan creation and checkpoint
    validation; it never claims completion when an uncheckpointed module has
    no certifier.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--dependency-map", type=Path, required=True)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--applied-root", type=Path)
    parser.add_argument("--translated-olean-root", type=Path)
    parser.add_argument("--plan-output", type=Path)
    parser.add_argument("--checkpoint-root", type=Path)
    parser.add_argument("--output-root", type=Path)
    parser.add_argument("--staging-parent", type=Path)
    parser.add_argument("--receipt-root", type=Path)
    parser.add_argument("--work-parent", type=Path)
    parser.add_argument("--oracle", type=Path)
    parser.add_argument("--auditor", type=Path)
    parser.add_argument("--corpus-identity", type=Path)
    parser.add_argument("--timeout", type=float, default=900)
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--max-modules", type=int)
    args = parser.parse_args(argv)
    plan = build_plan(args.manifest, args.dependency_map, source_root=args.source_root,
                      applied_root=args.applied_root)
    if args.plan_output is not None:
        plan_hash = write_plan(args.plan_output, plan)
        print(json.dumps({"plan": str(args.plan_output.absolute()), "sha256": plan_hash}, sort_keys=True))
    if args.checkpoint_root is not None:
        production = (args.output_root, args.staging_parent, args.receipt_root, args.work_parent,
                      args.translated_olean_root, args.oracle, args.auditor)
        if any(item is None for item in production):
            raise RuntimeError("production checkpoint runs require output, staging, receipt, work, import, oracle, and auditor paths")
        args.output_root.mkdir(parents=True, exist_ok=True)
        args.staging_parent.mkdir(parents=True, exist_ok=True)
        args.receipt_root.mkdir(parents=True, exist_ok=True)
        args.work_parent.mkdir(parents=True, exist_ok=True)
        imports = build_import_environment(args.source_root, args.translated_olean_root)
        oracle = base.InputFile(args.oracle, _digest(args.oracle))
        auditor = base.InputFile(args.auditor, _digest(args.auditor))
        report = run_production_tree(plan, imports=imports, oracle=oracle, auditor=auditor,
                                     checkpoint_root=args.checkpoint_root, output_root=args.output_root,
                                     staging_parent=args.staging_parent, receipt_root=args.receipt_root,
                                     work_parent=args.work_parent, timeout=args.timeout,
                                     corpus_identity=({"path": str(args.corpus_identity), "sha256": _digest(args.corpus_identity)}
                                                      if args.corpus_identity is not None else None),
                                     resume=not args.no_resume,
                                     max_modules=args.max_modules)
        print(json.dumps(report, sort_keys=True))
    elif args.plan_output is None:
        print(json.dumps(plan.result(), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
