#!/usr/bin/env python3
"""Build the deterministic closed-world input manifest for boundary translation."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from typing import Any, Sequence

import check_simp_engine_boundary_scope as scope
import check_simp_engine_pin as pin
from inventory_checkpoint import CheckpointStore
import analysis_checkpoint_identity
import simp_engine_inventory as inventory
import simp_manual_overrides as manual_overrides
from process_runner import run_process


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = inventory.MATHLIB
REPORT_SCHEMA = 2

# Re-export the shared schema vocabulary for manifest consumers.  Keeping one
# source of truth prevents a classifier/consumer drift from silently changing
# the closed-world partition.
EXECUTION_ROLES = scope.EXECUTION_ROLES
DECLARATION_KINDS = scope.DECLARATION_KINDS
ACTIONS = scope.ACTIONS

MANIFEST_FIELDS = {
    "reportSchema",
    "kind",
    "allowDirty",
    "allowUnresolved",
    "repositoryCommit",
    "mathlibCommit",
    "lean",
    "modulePrefix",
    "moduleFileCount",
    "inventoriedModuleCount",
    "occurrenceCount",
    "nestedOccurrenceCount",
    "duplicateSyntaxRecords",
    "duplicateScopeSyntaxRecords",
    "fullFrontendFallbacks",
    "scopeFrontendFallbacks",
    "scopeProbe",
    "countsByExecutionRole",
    "countsByDeclarationKind",
    "countsByAction",
    "implementationHashes",
    "manualOverrides",
    "modules",
}
MODULE_FIELDS = {
    "module",
    "compiledModule",
    "moduleHash",
    "sourceHash",
    "duplicateSyntaxRecords",
    "duplicateScopeSyntaxRecords",
    "occurrences",
}
OCCURRENCE_FIELDS = {
    "id",
    "kind",
    "source",
    "startByte",
    "endByte",
    "line",
    "column",
    "syntaxKind",
    "ancestors",
    "commandKind",
    "commandStartByte",
    "commandEndByte",
    "scopePaths",
    "executionRole",
    "declarationKind",
    "action",
    "reason",
    "declarations",
}
OCCURRENCE_OPTIONAL_FIELDS = {"executionEvidence"}

IMPLEMENTATION_SOURCE_PATTERNS = (
    "ExplicitLean.lean",
    "ExplicitLean/SimpEngine/Inventory.lean",
    "ExplicitLean/SimpEngine/FrontendOptions.lean",
    "ExplicitLean/SimpEngine/CommandAudit.lean",
    "ExplicitLean/SimpEngine/Boundary.lean",
    "ExplicitLean/SimpEngine/Boundary/*.lean",
    "Experiment/SimpEngineInventory.lean",
    "Experiment/SimpEngineBoundary*.lean",
    "Experiment/SimpEngineCommandAudit.lean",
    "Experiment/SimpEngineDeclarationOracle.lean",
    "Experiment/lean_toolchain_cache.py",
    "Experiment/process_runner.py",
    "Experiment/boundary_materialize_shard.py",
    "Experiment/check_simp_engine_boundary*.py",
    "Experiment/boundary_protocol.py",
    "Experiment/check_simp_engine_declaration_oracle.py",
    "Experiment/check_simp_engine_pin.py",
    "Experiment/simp_engine_inventory.py",
    "Experiment/simp_engine_boundary_corpus.py",
    "Experiment/manual_overlay.py",
    "Experiment/simp_manual_overrides.py",
    "Experiment/simp_manual_overrides.json",
    "Experiment/inventory_checkpoint.py",
    "Experiment/analysis_checkpoint_identity.py",
    "Experiment/boundary_expr_codec.py",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def command_output(command: list[str], timeout: int = 60) -> str:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(
            f"command failed ({completed.returncode}): {command}\n{completed.stdout}"
        )
    return completed.stdout.strip()


def current_commit() -> str:
    return command_output(["git", "rev-parse", "HEAD"])


def assert_repository(expected_commit: str | None, allow_dirty: bool) -> str:
    commit = current_commit()
    if expected_commit and commit != expected_commit:
        raise RuntimeError(
            f"moving_ref: expected {expected_commit}, checked out {commit}"
        )
    if not allow_dirty:
        status = command_output(
            ["git", "status", "--porcelain", "--untracked-files=all"]
        )
        if status:
            raise RuntimeError("dirty_worktree")
    return commit


def pinned_mathlib_commit() -> str:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    matches = [
        package
        for package in manifest.get("packages", [])
        if package.get("name") == "mathlib"
    ]
    if len(matches) != 1 or not isinstance(matches[0].get("rev"), str):
        raise RuntimeError("lake manifest has no unique pinned Mathlib revision")
    return str(matches[0]["rev"])


def pinned_package_identity() -> dict[str, Any]:
    """Return the complete locked package identity used by checkpoint keys."""
    manifest_path = ROOT / "lake-manifest.json"
    raw = manifest_path.read_bytes()
    manifest = json.loads(raw)
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise RuntimeError("lake manifest has no package list")
    locked: list[dict[str, object]] = []
    for package in packages:
        if not isinstance(package, dict):
            raise RuntimeError("lake manifest contains an invalid package")
        name, package_type, revision = (
            package.get("name"), package.get("type"), package.get("rev")
        )
        if not all(isinstance(value, str) and value for value in (name, package_type, revision)):
            raise RuntimeError("lake manifest package identity is incomplete")
        locked.append({"name": name, "type": package_type, "rev": revision})
    return {"manifestSha256": sha256(raw), "packages": locked}


def verify_environment() -> tuple[str, dict[str, str]]:
    expected_mathlib = pinned_mathlib_commit()
    actual_mathlib = command_output(
        ["git", "-C", str(MATHLIB), "rev-parse", "HEAD"]
    )
    if actual_mathlib != expected_mathlib:
        raise RuntimeError(
            f"mathlib_commit_mismatch:{actual_mathlib}!={expected_mathlib}"
        )
    mathlib_status = command_output(
        [
            "git",
            "-C",
            str(MATHLIB),
            "status",
            "--porcelain",
            "--untracked-files=all",
        ]
    )
    if mathlib_status:
        raise RuntimeError("mathlib_dirty_worktree")
    version = command_output(["lean", "--version"])
    if (
        f"version {pin.LEAN_VERSION}" not in version
        or f"commit {pin.LEAN_COMMIT}" not in version
    ):
        raise RuntimeError(f"unexpected Lean toolchain: {version}")
    return actual_mathlib, {
        "version": pin.LEAN_VERSION,
        "commit": pin.LEAN_COMMIT,
    }


def implementation_hashes() -> dict[str, str]:
    relatives: set[str] = set()
    for pattern in IMPLEMENTATION_SOURCE_PATTERNS:
        matches = [path for path in ROOT.glob(pattern) if path.is_file()]
        if not matches:
            raise RuntimeError(
                f"manifest implementation source pattern has no matches: {pattern}"
            )
        relatives.update(path.relative_to(ROOT).as_posix() for path in matches)
    result: dict[str, str] = {}
    for relative in sorted(relatives):
        path = ROOT / relative
        result[relative] = sha256(path.read_bytes())
    return result


def require_unchanged_hashes(
    label: str, before: dict[str, str], after: dict[str, str]
) -> None:
    if before == after:
        return
    names = sorted(set(before) | set(after))
    changed = [name for name in names if before.get(name) != after.get(name)]
    raise RuntimeError(f"{label}_changed_during_run:{changed}")


def module_paths(prefix: str, maximum: int | None) -> list[Path]:
    paths = sorted((MATHLIB / "Mathlib").rglob("*.lean"))
    if prefix:
        paths = [
            path
            for path in paths
            if path.relative_to(MATHLIB).as_posix().startswith(prefix)
        ]
    if maximum is not None:
        if maximum <= 0:
            raise ValueError("maximum module count must be positive")
        paths = paths[:maximum]
    if not paths:
        raise RuntimeError(f"manifest selected no Mathlib modules for prefix {prefix!r}")
    return paths


def module_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        relative = resolved.relative_to(MATHLIB.resolve())
    except ValueError as error:
        raise RuntimeError(f"module is outside pinned Mathlib: {path}") from error
    if relative.suffix != ".lean" or not relative.parts or relative.parts[0] != "Mathlib":
        raise RuntimeError(f"invalid Mathlib module source: {path}")
    return relative.as_posix()


def compiled_module_name(module: str) -> str:
    if not module.endswith(".lean"):
        raise RuntimeError(f"module path has no .lean suffix: {module}")
    return module[: -len(".lean")].replace("/", ".")


def _decode_inventory_output(
    payload: object,
) -> tuple[list[dict[str, Any]], list[str]]:
    if not isinstance(payload, dict) or set(payload) != {"stdout"}:
        raise RuntimeError("inventory checkpoint payload fields are invalid")
    output = payload.get("stdout")
    if not isinstance(output, str):
        raise RuntimeError("inventory checkpoint stdout is not a string")
    entries: list[dict[str, Any]] = []
    fallbacks: list[str] = []
    for line in output.splitlines():
        if line.startswith("{"):
            value = json.loads(line)
            if not isinstance(value, dict):
                raise RuntimeError("syntax inventory output record is not an object")
            entries.append(value)
        elif line.startswith("SIMP_ENGINE_INVENTORY_FULL_FALLBACK file="):
            fallbacks.append(line.split("=", 1)[1])
    return entries, fallbacks


def _inventory_batch_result(
    paths: Sequence[Path],
    timeout: int,
    checkpoint: CheckpointStore | None = None,
    freshness: Any = None,
) -> tuple[list[dict[str, Any]], list[str], bool]:
    command = [
        sys.executable,
        str(ROOT / "Experiment" / "lean_toolchain_cache.py"),
        "inventory",
        *(str(path.resolve()) for path in paths),
    ]
    def produce() -> dict[str, str]:
        completed = run_process(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        if completed.returncode:
            diagnostics = "\n".join(completed.stderr.splitlines()[-200:])
            raise RuntimeError(
                f"syntax inventory batch failed ({completed.returncode}):\n{diagnostics}"
            )
        return {"stdout": completed.stdout}

    if checkpoint is None:
        payload = produce()
        hit = False
    else:
        modules = [module_path(path) for path in paths]
        source_hashes = [sha256(path.read_bytes()) for path in paths]

        def batch_freshness() -> None:
            current_hashes = [sha256(path.read_bytes()) for path in paths]
            if current_hashes != source_hashes:
                raise RuntimeError("inventory source changed during checkpointed batch")
            if freshness is not None:
                if not callable(freshness):
                    raise RuntimeError("inventory checkpoint freshness is not callable")
                freshness()

        def validate_payload(value: object) -> object:
            entries, _fallbacks = _decode_inventory_output(value)
            expected_files = {str(path.resolve()) for path in paths}
            for entry in entries:
                required = {
                    "file", "kind", "startByte", "endByte", "line", "column",
                    "syntaxKind", "source",
                }
                if not required <= set(entry):
                    raise RuntimeError("syntax inventory output record is incomplete")
                if str(entry["file"]) not in expected_files:
                    raise RuntimeError("syntax inventory output file is not in this batch")
            return value

        result = checkpoint.get_or_compute(
            "inventory",
            modules,
            source_hashes,
            produce,
            parameters={"timeout": timeout},
            validator=validate_payload,
            freshness=batch_freshness,
        )
        payload = result.payload
        hit = result.hit
    entries, fallbacks = _decode_inventory_output(payload)
    return entries, fallbacks, hit


def inventory_batch(
    paths: Sequence[Path], timeout: int, checkpoint: CheckpointStore | None = None
) -> tuple[list[dict[str, Any]], list[str]]:
    """Run one inventory batch, retaining the historical two-result API."""
    entries, fallbacks, _hit = _inventory_batch_result(paths, timeout, checkpoint)
    return entries, fallbacks


def inventory_paths(
    paths: Sequence[Path],
    batch_size: int,
    timeout: int,
    checkpoint: CheckpointStore | None = None,
    freshness: Any = None,
) -> tuple[dict[str, list[dict[str, Any]]], list[str]]:
    if batch_size <= 0:
        raise ValueError("inventory batch size must be positive")
    path_to_module = {path.resolve(): module_path(path) for path in paths}
    if len(path_to_module) != len(paths):
        raise RuntimeError("manifest module list contains duplicate paths")
    by_module: defaultdict[str, list[dict[str, Any]]] = defaultdict(list)
    fallback_modules: set[str] = set()
    batch_count = (len(paths) + batch_size - 1) // batch_size
    for batch_index, start in enumerate(range(0, len(paths), batch_size), start=1):
        batch_paths = paths[start : start + batch_size]
        started = time.monotonic()
        if checkpoint is None:
            entries, fallbacks = inventory_batch(batch_paths, timeout)
            hit = False
        else:
            entries, fallbacks, hit = _inventory_batch_result(
                batch_paths, timeout, checkpoint, freshness
            )
        elapsed = time.monotonic() - started
        if checkpoint is not None:
            print(
                f"inventory batch {batch_index}/{batch_count}: "
                f"{'hit' if hit else 'completed'} modules={len(batch_paths)} "
                f"seconds={elapsed:.2f}",
                file=sys.stderr,
            )
        for fallback in fallbacks:
            fallback_path = Path(fallback)
            if not fallback_path.is_absolute():
                fallback_path = ROOT / fallback_path
            module = path_to_module.get(fallback_path.resolve())
            if module is None:
                raise RuntimeError(
                    f"inventory fallback returned an unrequested file: {fallback}"
                )
            fallback_modules.add(module)
        for raw in entries:
            raw = dict(raw)
            raw_path = Path(str(raw.pop("file")))
            if not raw_path.is_absolute():
                raw_path = ROOT / raw_path
            module = path_to_module.get(raw_path.resolve())
            if module is None:
                raise RuntimeError(
                    f"inventory returned an unrequested file: {raw_path}"
                )
            if raw.get("kind") not in inventory.SUPPORTED_KINDS:
                continue
            raw["module"] = module
            raw["id"] = inventory.occurrence_id(
                module, int(raw["startByte"]), int(raw["endByte"])
            )
            by_module[module].append(raw)
    return dict(by_module), sorted(fallback_modules)


def validate_module_inventory(
    module: str, source: bytes, entries: Sequence[dict[str, Any]]
) -> tuple[list[dict[str, Any]], int, int]:
    by_range: dict[tuple[int, int], dict[str, Any]] = {}
    duplicate_records = 0
    for entry in entries:
        byte_range = (int(entry["startByte"]), int(entry["endByte"]))
        previous = by_range.get(byte_range)
        if previous is not None:
            if previous != entry:
                raise RuntimeError(
                    f"conflicting inventory records at {module}:{byte_range}"
                )
            # Parser/macro syntax can share the same source-backed subtree in
            # more than one parent position. It is still one replaceable source
            # occurrence. Collapse only byte-identical records and expose the
            # count in the manifest; any disagreement remains an error.
            duplicate_records += 1
            continue
        by_range[byte_range] = entry
    ordered = sorted(
        by_range.values(),
        key=lambda item: (int(item["startByte"]), -int(item["endByte"])),
    )
    containing_ends: list[int] = []
    previous_start: int | None = None
    nested = 0
    for entry in ordered:
        inventory.validate_occurrence(source, entry)
        if entry.get("syntaxKind") != "Lean.Parser.Tactic.simp":
            raise RuntimeError(
                f"unexpected syntax kind at {module}:{entry.get('line')}: "
                f"{entry.get('syntaxKind')!r}"
            )
        start = int(entry["startByte"])
        end = int(entry["endByte"])
        if start == previous_start:
            raise RuntimeError(f"conflicting occurrence starts in {module}:{start}")
        previous_start = start
        while containing_ends and start >= containing_ends[-1]:
            containing_ends.pop()
        if containing_ends:
            if end > containing_ends[-1]:
                raise RuntimeError(
                    f"partially overlapping occurrences in {module}:{start}:{end}"
                )
            nested += 1
        containing_ends.append(end)
    return ordered, nested, duplicate_records


def occurrence_key(entry: dict[str, Any]) -> tuple[int, int, str, str]:
    return (
        int(entry["startByte"]),
        int(entry["endByte"]),
        str(entry["kind"]),
        str(entry["source"]),
    )


def scope_action(execution_role: str, declaration_kind: str) -> str:
    """Return the schema-2 action implied by a scope classification."""
    return scope.expected_action(execution_role, declaration_kind)


def join_scope_records(
    module: str,
    entries: Sequence[dict[str, Any]],
    occurrences: Sequence[dict[str, Any]],
    declarations: Sequence[dict[str, Any]],
) -> tuple[list[dict[str, Any]], int]:
    """Strictly join syntax and scope records, then emit manifest occurrences."""
    inventory_by_key: defaultdict[tuple[int, int, str, str], list[dict[str, Any]]] = (
        defaultdict(list)
    )
    scope_by_key: defaultdict[tuple[int, int, str, str], list[dict[str, Any]]] = (
        defaultdict(list)
    )
    for entry in entries:
        inventory_by_key[occurrence_key(entry)].append(entry)
    for occurrence in occurrences:
        scope_by_key[occurrence_key(occurrence)].append(occurrence)
    duplicate_inventory = sorted(
        key for key, values in inventory_by_key.items() if len(values) != 1
    )
    missing = sorted(set(inventory_by_key) - set(scope_by_key))
    extra = sorted(set(scope_by_key) - set(inventory_by_key))
    if duplicate_inventory or missing or extra:
        raise RuntimeError(
            f"scope/inventory join is not one-to-one for {module}: "
            f"duplicate inventory={duplicate_inventory}, "
            f"missing={missing}, extra={extra}"
        )

    declaration_list = list(declarations)
    result: list[dict[str, Any]] = []
    duplicate_scope_records = 0
    for key in sorted(inventory_by_key):
        entry = inventory_by_key[key][0]
        scope_records = scope_by_key[key]
        duplicate_scope_records += len(scope_records) - 1
        classified_records = [
            scope.classify(occurrence, declaration_list)
            for occurrence in scope_records
        ]
        semantic_classifications = {
            json.dumps(
                {
                    "executionRole": classified["executionRole"],
                    "declarationKind": classified["declarationKind"],
                    "action": classified["action"],
                    "reason": classified["reason"],
                    "declarations": classified["declarations"],
                },
                sort_keys=True,
                separators=(",", ":"),
            )
            for classified in classified_records
        }
        if len(semantic_classifications) != 1:
            raise RuntimeError(
                f"ambiguous scope classification for {module}:{key}: "
                f"{sorted(semantic_classifications)}"
            )
        classified = classified_records[0]
        execution_role = str(classified["executionRole"])
        declaration_kind = str(classified["declarationKind"])
        action = str(classified["action"])
        scope.validate_scope_dimensions(execution_role, declaration_kind, action)
        scope_paths_by_key: dict[str, dict[str, Any]] = {}
        for occurrence in scope_records:
            path = {
                "ancestors": list(occurrence.get("ancestors", [])),
                "commandKind": occurrence.get("commandKind"),
                "commandStartByte": occurrence.get("commandStartByte"),
                "commandEndByte": occurrence.get("commandEndByte"),
            }
            path_key = json.dumps(path, sort_keys=True, separators=(",", ":"))
            scope_paths_by_key[path_key] = path
        scope_paths = [
            scope_paths_by_key[path_key]
            for path_key in sorted(scope_paths_by_key)
        ]
        canonical_path = scope_paths[0]
        result.append(
            {
                "id": str(entry["id"]),
                "kind": str(entry["kind"]),
                "source": str(entry["source"]),
                "startByte": int(entry["startByte"]),
                "endByte": int(entry["endByte"]),
                "line": int(entry["line"]),
                "column": int(entry["column"]),
                "syntaxKind": str(entry["syntaxKind"]),
                "ancestors": canonical_path["ancestors"],
                "commandKind": canonical_path["commandKind"],
                "commandStartByte": canonical_path["commandStartByte"],
                "commandEndByte": canonical_path["commandEndByte"],
                "scopePaths": scope_paths,
                "executionRole": execution_role,
                "declarationKind": declaration_kind,
                "action": action,
                "reason": str(classified["reason"]),
                "declarations": list(classified["declarations"]),
            }
        )
    return result, duplicate_scope_records


def build_manifest(
    paths: Sequence[Path],
    *,
    module_prefix: str,
    expected_commit: str | None = None,
    allow_dirty: bool = False,
    allow_unresolved: bool = False,
    inventory_batch_size: int = 2048,
    scope_batch_size: int = 128,
    timeout: int = 3600,
    checkpoint_root: Path | None = None,
) -> dict[str, Any]:
    selected = sorted((Path(path).resolve() for path in paths), key=module_path)
    if not selected:
        raise RuntimeError("boundary manifest requires at least one module")
    repository_commit = assert_repository(expected_commit, allow_dirty)
    mathlib_commit, lean = verify_environment()
    manual_database_bytes = manual_overrides.DEFAULT_PATH.read_bytes()
    manual_environment, _manual_entries = manual_overrides.load_database()
    if manual_environment != {"mathlibCommit": mathlib_commit, "lean": lean}:
        raise RuntimeError("manual_override_environment_mismatch")
    initial_implementation_hashes = implementation_hashes()
    checkpoint = None
    implementation_freshness = None
    analysis_identity_snapshot = None
    if checkpoint_root is not None:
        checkpoint_path = Path(checkpoint_root).resolve()
        package_root = (ROOT / ".lake/packages").resolve()
        try:
            checkpoint_path.relative_to(package_root)
        except ValueError:
            pass
        else:
            raise RuntimeError(
                "checkpoint root must be outside the shared .lake/packages tree"
            )
        run_process(
            ["lake", "build", "simpEngineInventory", "simpEngineBoundaryScope",
             "ExplicitLean.SimpEngine.Boundary.ScopeFixture",
             "ExplicitLean.SimpEngine.Boundary.ScopeProbe"],
            cwd=ROOT, check=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True, timeout=timeout,
        )
        analysis_arguments = {
            "inventory_binary": ROOT / ".lake/build/bin/simpEngineInventory",
            "scope_binary": ROOT / ".lake/build/bin/simpEngineBoundaryScope",
        }
        analysis_freshness_snapshot = analysis_checkpoint_identity.cheap_snapshot(
            ROOT, **analysis_arguments
        )
        analysis_identity_snapshot = analysis_checkpoint_identity.identity(
            ROOT, **analysis_arguments
        )
        checkpoint = CheckpointStore(
            checkpoint_path,
            identity={
                **analysis_identity_snapshot,
                "mathlibCommit": mathlib_commit,
                "python": sys.version,
            },
        )
        def implementation_freshness() -> None:
            require_unchanged_hashes(
                "implementation", initial_implementation_hashes, implementation_hashes()
            )
            if analysis_checkpoint_identity.cheap_snapshot(
                ROOT, **analysis_arguments
            ) != analysis_freshness_snapshot:
                raise RuntimeError("analysis inputs changed during checkpointed run")

        implementation_freshness()
    sources = {module_path(path): path.read_bytes() for path in selected}
    by_module, fallbacks = inventory_paths(
        selected,
        inventory_batch_size,
        timeout,
        checkpoint=checkpoint,
        freshness=implementation_freshness,
    )

    inventories: dict[str, list[dict[str, Any]]] = {}
    nested_count = 0
    duplicate_syntax_records = 0
    duplicate_syntax_by_module: dict[str, int] = {}
    seen_ids: set[str] = set()
    for path in selected:
        module = module_path(path)
        source = sources[module]
        entries, nested, duplicates = validate_module_inventory(
            module, source, by_module.get(module, [])
        )
        for entry in entries:
            occurrence_id = str(entry["id"])
            if occurrence_id in seen_ids:
                raise RuntimeError(f"duplicate occurrence id: {occurrence_id}")
            seen_ids.add(occurrence_id)
        inventories[module] = entries
        nested_count += nested
        duplicate_syntax_records += duplicates
        duplicate_syntax_by_module[module] = duplicates

    specs = [
        scope.ModuleSpec(
            compiled_module_name(module),
            MATHLIB / module,
            len(entries),
        )
        for module, entries in sorted(inventories.items())
        if entries
    ]
    if specs:
        scope_occurrences, scope_declarations, scope_fallbacks = (
            scope.load_records_with_fallbacks(
                specs,
                batch_size=scope_batch_size,
                timeout=timeout,
                **(
                    {
                        "checkpoint": checkpoint,
                        "freshness": implementation_freshness,
                    }
                    if checkpoint is not None
                    else {}
                ),
            )
        )
    else:
        scope_occurrences, scope_declarations, scope_fallbacks = {}, {}, []

    modules: list[dict[str, Any]] = []
    execution_role_counts: Counter[str] = Counter()
    declaration_kind_counts: Counter[str] = Counter()
    action_counts: Counter[str] = Counter()
    duplicate_scope_records = 0
    for module in sorted(inventories):
        compiled = compiled_module_name(module)
        entries = inventories[module]
        classified, module_scope_duplicates = join_scope_records(
            module,
            entries,
            scope_occurrences.get(compiled, []),
            scope_declarations.get(compiled, []),
        )
        unresolved = [
            occurrence
            for occurrence in classified
            if occurrence["action"] == "unresolved"
        ]
        if unresolved:
            unknown_ids = {str(occurrence["id"]) for occurrence in unresolved}
            unknown_entries = [
                entry for entry in entries if str(entry["id"]) in unknown_ids
            ]
            scope.apply_execution_evidence(
                compiled,
                sources[module],
                unresolved,
                entries=unknown_entries,
                timeout=timeout,
            )
        duplicate_scope_records += module_scope_duplicates
        execution_role_counts.update(
            occurrence["executionRole"] for occurrence in classified
        )
        declaration_kind_counts.update(
            occurrence["declarationKind"] for occurrence in classified
        )
        action_counts.update(occurrence["action"] for occurrence in classified)
        modules.append(
            {
                "module": module,
                "compiledModule": compiled,
                "moduleHash": sha256(module.encode("utf-8")),
                "sourceHash": sha256(sources[module]),
                "duplicateSyntaxRecords": duplicate_syntax_by_module[module],
                "duplicateScopeSyntaxRecords": module_scope_duplicates,
                "occurrences": classified,
            }
        )

    changed_sources = [
        module
        for module in sorted(sources)
        if (MATHLIB / module).read_bytes() != sources[module]
    ]
    if changed_sources:
        raise RuntimeError(f"mathlib_sources_changed_during_run:{changed_sources}")
    require_unchanged_hashes(
        "implementation",
        initial_implementation_hashes,
        implementation_hashes(),
    )
    assert_repository(repository_commit, allow_dirty)
    if analysis_identity_snapshot is not None:
        assert implementation_freshness is not None
        implementation_freshness()
        analysis_identity_final = analysis_checkpoint_identity.identity(
            ROOT, **analysis_arguments
        )
        if analysis_identity_final != analysis_identity_snapshot:
            raise RuntimeError("analysis identity changed during run")
        implementation_freshness()
    final_mathlib_commit, final_lean = verify_environment()
    if final_mathlib_commit != mathlib_commit or final_lean != lean:
        raise RuntimeError("pinned_environment_changed_during_run")

    return {
        "reportSchema": REPORT_SCHEMA,
        "kind": "simp_engine_boundary_manifest",
        "allowDirty": allow_dirty,
        "allowUnresolved": allow_unresolved,
        "repositoryCommit": repository_commit,
        "mathlibCommit": mathlib_commit,
        "lean": lean,
        "modulePrefix": module_prefix,
        "moduleFileCount": len(modules),
        "inventoriedModuleCount": sum(bool(module["occurrences"]) for module in modules),
        "occurrenceCount": len(seen_ids),
        "nestedOccurrenceCount": nested_count,
        "duplicateSyntaxRecords": duplicate_syntax_records,
        "duplicateScopeSyntaxRecords": duplicate_scope_records,
        "fullFrontendFallbacks": fallbacks,
        "scopeFrontendFallbacks": scope_fallbacks,
        "scopeProbe": {
            "module": scope.SCOPE_PROBE_IMPORT,
            "scheduling": scope.SCOPE_PROBE_SCHEDULING,
            "temporaryCopyOnly": True,
            "reportCommand": "simp_engine_boundary_scope_report",
        },
        "countsByExecutionRole": dict(sorted(execution_role_counts.items())),
        "countsByDeclarationKind": dict(sorted(declaration_kind_counts.items())),
        "countsByAction": dict(sorted(action_counts.items())),
        "implementationHashes": initial_implementation_hashes,
        "manualOverrides": {
            "sha256": sha256(manual_database_bytes),
            "schema": manual_overrides.SCHEMA,
            "environment": manual_environment,
        },
        "modules": modules,
    }


def write_manifest(path: Path, manifest: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(
        manifest,
        indent=2,
        sort_keys=True,
        ensure_ascii=False,
    ) + "\n"
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(encoded, encoding="utf-8")
    temporary.replace(path)


def _exact_fields(
    value: dict[str, Any], required: set[str], label: str, optional: set[str] | None = None
) -> None:
    optional = optional or set()
    missing = required - set(value)
    extra = set(value) - required - optional
    if missing or extra:
        raise RuntimeError(
            f"boundary manifest {label} fields changed: "
            f"missing={sorted(missing)}, extra={sorted(extra)}"
        )


def _nonnegative_int(value: object, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise RuntimeError(f"boundary manifest {label} must be a nonnegative integer")
    return value


def _string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise RuntimeError(f"boundary manifest {label} must be a nonempty string")
    return value


def _optional_int(value: object, label: str) -> int | None:
    if value is None:
        return None
    return _nonnegative_int(value, label)


def _string_array(value: object, label: str) -> list[str]:
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item for item in value
    ):
        raise RuntimeError(f"boundary manifest {label} must be an array of strings")
    return value


def _validate_scope_path(value: object, label: str) -> None:
    if not isinstance(value, dict):
        raise RuntimeError(f"boundary manifest {label} must be an object")
    _exact_fields(
        value,
        {"ancestors", "commandKind", "commandStartByte", "commandEndByte"},
        label,
    )
    _string_array(value.get("ancestors"), f"{label}.ancestors")
    command_kind = value.get("commandKind")
    if command_kind is not None and (
        not isinstance(command_kind, str) or not command_kind
    ):
        raise RuntimeError(f"boundary manifest {label}.commandKind is invalid")
    _optional_int(value.get("commandStartByte"), f"{label}.commandStartByte")
    _optional_int(value.get("commandEndByte"), f"{label}.commandEndByte")


def _validate_declaration(value: object, label: str) -> None:
    if not isinstance(value, dict):
        raise RuntimeError(f"boundary manifest {label} must be an object")
    _exact_fields(
        value,
        {
            "module",
            "name",
            "startByte",
            "endByte",
            "selectionStartByte",
            "selectionEndByte",
            "isProof",
        },
        label,
    )
    _string(value.get("module"), f"{label}.module")
    _string(value.get("name"), f"{label}.name")
    start = _nonnegative_int(value.get("startByte"), f"{label}.startByte")
    end = _nonnegative_int(value.get("endByte"), f"{label}.endByte")
    selection_start = _nonnegative_int(
        value.get("selectionStartByte"), f"{label}.selectionStartByte"
    )
    selection_end = _nonnegative_int(
        value.get("selectionEndByte"), f"{label}.selectionEndByte"
    )
    if start > end or selection_start > selection_end:
        raise RuntimeError(f"boundary manifest {label} has an invalid range")
    if not isinstance(value.get("isProof"), bool):
        raise RuntimeError(f"boundary manifest {label}.isProof must be a boolean")


def _validate_execution_evidence(value: object, label: str) -> None:
    if not isinstance(value, dict):
        raise RuntimeError(f"boundary manifest {label} must be an object")
    _exact_fields(
        value,
        {"status", "executionCount", "callers", "module", "scheduling"},
        label,
    )
    if value.get("status") not in {
        "missing_execution",
        "complete_proof_declaration",
        "complete_nonproof_declaration",
        "mixed_execution_classification",
        "incomplete_execution_evidence",
    }:
        raise RuntimeError(f"boundary manifest {label}.status is invalid")
    execution_count = _nonnegative_int(
        value.get("executionCount"), f"{label}.executionCount"
    )
    callers = value.get("callers")
    if not isinstance(callers, list):
        raise RuntimeError(f"boundary manifest {label}.callers must be an array")
    caller_count = 0
    proof_values: set[bool] = set()
    complete_callers = True
    for index, caller in enumerate(callers):
        caller_label = f"{label}.callers[{index}]"
        if not isinstance(caller, dict):
            raise RuntimeError(f"boundary manifest {caller_label} must be an object")
        _exact_fields(
            caller,
            {"caller", "executionCount", "isProofDeclaration"},
            caller_label,
        )
        caller_name = caller.get("caller")
        if caller_name is not None:
            _string(caller_name, f"{caller_label}.caller")
        else:
            complete_callers = False
        item_count = _nonnegative_int(
            caller.get("executionCount"), f"{caller_label}.executionCount"
        )
        if item_count == 0:
            raise RuntimeError(
                f"boundary manifest {caller_label}.executionCount must be positive"
            )
        caller_count += item_count
        proof = caller.get("isProofDeclaration")
        if proof is not None and not isinstance(proof, bool):
            raise RuntimeError(
                f"boundary manifest {caller_label}.isProofDeclaration is invalid"
            )
        if isinstance(proof, bool):
            proof_values.add(proof)
        else:
            complete_callers = False
    if caller_count != execution_count:
        raise RuntimeError(
            f"boundary manifest {label}.executionCount does not match callers"
        )
    module = value.get("module")
    if module is not None:
        _string(module, f"{label}.module")
    if value.get("scheduling") != scope.SCOPE_PROBE_SCHEDULING:
        raise RuntimeError(f"boundary manifest {label}.scheduling is invalid")
    status = value["status"]
    if status == "missing_execution":
        if callers or execution_count != 0 or module is not None:
            raise RuntimeError(f"boundary manifest {label} has invalid missing evidence")
    elif module is None:
        raise RuntimeError(f"boundary manifest {label}.module is required")
    elif status == "complete_proof_declaration" and (
        not complete_callers or proof_values != {True}
    ):
        raise RuntimeError(f"boundary manifest {label} has invalid proof evidence")
    elif status == "complete_nonproof_declaration" and (
        not complete_callers or proof_values != {False}
    ):
        raise RuntimeError(
            f"boundary manifest {label} has invalid computational evidence"
        )
    elif status == "mixed_execution_classification" and (
        not complete_callers or proof_values != {False, True}
    ):
        raise RuntimeError(f"boundary manifest {label} has invalid mixed evidence")


def _nested_occurrence_count(occurrences: list[dict[str, Any]], module: str) -> int:
    nested = 0
    containing_ends: list[int] = []
    previous_start: int | None = None
    for occurrence in sorted(
        occurrences,
        key=lambda item: (int(item["startByte"]), -int(item["endByte"])),
    ):
        start = int(occurrence["startByte"])
        end = int(occurrence["endByte"])
        if start == previous_start:
            raise RuntimeError(
                f"boundary manifest has conflicting occurrence starts in {module}:{start}"
            )
        previous_start = start
        while containing_ends and start >= containing_ends[-1]:
            containing_ends.pop()
        if containing_ends:
            if end > containing_ends[-1]:
                raise RuntimeError(
                    f"boundary manifest has partially overlapping occurrences in {module}"
                )
            nested += 1
        containing_ends.append(end)
    return nested


def _declared_count_map(
    value: object, label: str, allowed: set[str]
) -> dict[str, int]:
    if not isinstance(value, dict):
        raise RuntimeError(f"boundary manifest {label} must be an object")
    result: dict[str, int] = {}
    for key, count in value.items():
        if (
            key not in allowed
            or not isinstance(count, int)
            or isinstance(count, bool)
            or count < 0
        ):
            raise RuntimeError(f"boundary manifest {label} has an invalid count")
        result[key] = count
    return result


def enforce_manifest_policy(manifest: dict[str, Any]) -> None:
    _exact_fields(manifest, MANIFEST_FIELDS, "top-level")
    if (
        not isinstance(manifest.get("reportSchema"), int)
        or isinstance(manifest.get("reportSchema"), bool)
        or manifest.get("reportSchema") != REPORT_SCHEMA
    ):
        raise RuntimeError(
            f"boundary manifest schema must be {REPORT_SCHEMA}: "
            f"{manifest.get('reportSchema')!r}"
        )
    if manifest.get("kind") != "simp_engine_boundary_manifest":
        raise RuntimeError(
            f"unexpected boundary manifest kind: {manifest.get('kind')!r}"
        )
    for field in ("allowDirty", "allowUnresolved"):
        if not isinstance(manifest.get(field), bool):
            raise RuntimeError(f"boundary manifest {field} must be a boolean")
    _string(manifest.get("repositoryCommit"), "repositoryCommit")
    _string(manifest.get("mathlibCommit"), "mathlibCommit")
    if not isinstance(manifest.get("modulePrefix"), str):
        raise RuntimeError("boundary manifest modulePrefix must be a string")
    lean = manifest.get("lean")
    if not isinstance(lean, dict):
        raise RuntimeError("boundary manifest lean must be an object")
    _exact_fields(lean, {"version", "commit"}, "lean")
    _string(lean.get("version"), "lean.version")
    _string(lean.get("commit"), "lean.commit")
    for field in (
        "moduleFileCount",
        "inventoriedModuleCount",
        "occurrenceCount",
        "nestedOccurrenceCount",
        "duplicateSyntaxRecords",
        "duplicateScopeSyntaxRecords",
    ):
        _nonnegative_int(manifest.get(field), field)
    for field in ("fullFrontendFallbacks", "scopeFrontendFallbacks"):
        _string_array(manifest.get(field), field)
    probe = manifest.get("scopeProbe")
    if not isinstance(probe, dict):
        raise RuntimeError("boundary manifest scopeProbe must be an object")
    _exact_fields(
        probe,
        {"module", "scheduling", "temporaryCopyOnly", "reportCommand"},
        "scopeProbe",
    )
    if probe != {
        "module": scope.SCOPE_PROBE_IMPORT,
        "scheduling": scope.SCOPE_PROBE_SCHEDULING,
        "temporaryCopyOnly": True,
        "reportCommand": "simp_engine_boundary_scope_report",
    }:
        raise RuntimeError("boundary manifest scopeProbe metadata is invalid")
    hashes = manifest.get("implementationHashes")
    if not isinstance(hashes, dict) or not hashes or not all(
        isinstance(path, str)
        and path
        and isinstance(digest, str)
        and digest
        for path, digest in hashes.items()
    ):
        raise RuntimeError("boundary manifest implementationHashes is invalid")
    manual_database = manifest.get("manualOverrides")
    if not isinstance(manual_database, dict):
        raise RuntimeError("boundary manifest manualOverrides is invalid")
    _exact_fields(
        manual_database, {"sha256", "schema", "environment"}, "manualOverrides"
    )
    digest = _string(manual_database.get("sha256"), "manualOverrides.sha256")
    if len(digest) != 64 or any(ch not in "0123456789abcdef" for ch in digest):
        raise RuntimeError("boundary manifest manualOverrides.sha256 is invalid")
    if manual_database.get("schema") != manual_overrides.SCHEMA:
        raise RuntimeError("boundary manifest manualOverrides.schema is invalid")
    if manual_database.get("environment") != {
        "mathlibCommit": manifest["mathlibCommit"], "lean": manifest["lean"]
    }:
        raise RuntimeError("boundary manifest manualOverrides.environment is invalid")
    modules = manifest.get("modules")
    if not isinstance(modules, list):
        raise RuntimeError("boundary manifest modules must be an array")
    execution_role_counts: Counter[str] = Counter()
    declaration_kind_counts: Counter[str] = Counter()
    action_counts: Counter[str] = Counter()
    occurrence_count = 0
    inventoried_module_count = 0
    nested_occurrence_count = 0
    duplicate_syntax_count = 0
    duplicate_scope_count = 0
    seen_modules: set[str] = set()
    seen_ids: set[str] = set()
    for module in modules:
        if not isinstance(module, dict):
            raise RuntimeError("boundary manifest has an invalid module record")
        _exact_fields(module, MODULE_FIELDS, "module")
        module_name = _string(module.get("module"), "module.module")
        if module_name in seen_modules:
            raise RuntimeError(f"boundary manifest has duplicate module: {module_name}")
        seen_modules.add(module_name)
        if not module_name.startswith("Mathlib/") or not module_name.endswith(".lean"):
            raise RuntimeError(f"boundary manifest has invalid module path: {module_name}")
        if module.get("compiledModule") != compiled_module_name(module_name):
            raise RuntimeError(f"boundary manifest compiled module mismatch: {module_name}")
        if module.get("moduleHash") != sha256(module_name.encode("utf-8")):
            raise RuntimeError(f"boundary manifest module hash mismatch: {module_name}")
        _string(module.get("sourceHash"), f"{module_name}.sourceHash")
        module_duplicate_syntax = _nonnegative_int(
            module.get("duplicateSyntaxRecords"),
            f"{module_name}.duplicateSyntaxRecords",
        )
        module_duplicate_scope = _nonnegative_int(
            module.get("duplicateScopeSyntaxRecords"),
            f"{module_name}.duplicateScopeSyntaxRecords",
        )
        duplicate_syntax_count += module_duplicate_syntax
        duplicate_scope_count += module_duplicate_scope
        occurrences = module.get("occurrences")
        if not isinstance(occurrences, list):
            raise RuntimeError("boundary manifest module occurrences must be an array")
        inventoried_module_count += bool(occurrences)
        for occurrence in occurrences:
            if not isinstance(occurrence, dict):
                raise RuntimeError("boundary manifest has an invalid occurrence record")
            _exact_fields(
                occurrence,
                OCCURRENCE_FIELDS,
                f"occurrence in {module_name}",
                OCCURRENCE_OPTIONAL_FIELDS,
            )
            occurrence_id = _string(
                occurrence.get("id"), f"{module_name} occurrence id"
            )
            if occurrence_id in seen_ids:
                raise RuntimeError(
                    f"boundary manifest has duplicate occurrence id: {occurrence_id}"
                )
            seen_ids.add(occurrence_id)
            kind = _string(occurrence.get("kind"), f"{module_name} occurrence kind")
            if kind not in inventory.SUPPORTED_KINDS:
                raise RuntimeError(
                    f"boundary manifest has unsupported occurrence kind: {kind}"
                )
            if not isinstance(occurrence.get("source"), str):
                raise RuntimeError("boundary manifest occurrence source must be a string")
            start = _nonnegative_int(
                occurrence.get("startByte"), f"{module_name} occurrence startByte"
            )
            end = _nonnegative_int(
                occurrence.get("endByte"), f"{module_name} occurrence endByte"
            )
            if not start < end:
                raise RuntimeError("boundary manifest occurrence range is invalid")
            if occurrence_id != inventory.occurrence_id(module_name, start, end):
                raise RuntimeError("boundary manifest occurrence ID does not match its range")
            _nonnegative_int(occurrence.get("line"), f"{module_name} occurrence line")
            _nonnegative_int(occurrence.get("column"), f"{module_name} occurrence column")
            if occurrence.get("syntaxKind") != "Lean.Parser.Tactic.simp":
                raise RuntimeError("boundary manifest occurrence syntax kind is invalid")
            _string_array(
                occurrence.get("ancestors"), f"{module_name} occurrence ancestors"
            )
            command_kind = occurrence.get("commandKind")
            if command_kind is not None and not isinstance(command_kind, str):
                raise RuntimeError("boundary manifest occurrence commandKind is invalid")
            _optional_int(
                occurrence.get("commandStartByte"),
                f"{module_name} occurrence commandStartByte",
            )
            _optional_int(
                occurrence.get("commandEndByte"),
                f"{module_name} occurrence commandEndByte",
            )
            scope_paths = occurrence.get("scopePaths")
            if not isinstance(scope_paths, list) or not scope_paths:
                raise RuntimeError("boundary manifest occurrence scopePaths is invalid")
            for index, path in enumerate(scope_paths):
                _validate_scope_path(
                    path, f"{module_name} occurrence scopePaths[{index}]"
                )
            declarations = occurrence.get("declarations")
            if not isinstance(declarations, list):
                raise RuntimeError("boundary manifest occurrence declarations is invalid")
            for index, declaration in enumerate(declarations):
                _validate_declaration(
                    declaration, f"{module_name} occurrence declarations[{index}]"
                )
            _string(occurrence.get("reason"), f"{module_name} occurrence reason")
            if "executionEvidence" in occurrence:
                _validate_execution_evidence(
                    occurrence["executionEvidence"],
                    f"{module_name} occurrence executionEvidence",
                )
            execution_role = occurrence.get("executionRole")
            declaration_kind = occurrence.get("declarationKind")
            action = occurrence.get("action")
            try:
                checked_role, checked_kind, checked_action = (
                    scope.validate_scope_dimensions(
                        execution_role, declaration_kind, action
                    )
                )
            except RuntimeError as error:
                raise RuntimeError(
                    f"invalid boundary manifest scope dimensions: {error}"
                ) from error
            execution_role_counts[checked_role] += 1
            declaration_kind_counts[checked_kind] += 1
            action_counts[checked_action] += 1
            occurrence_count += 1
        nested_occurrence_count += _nested_occurrence_count(occurrences, module_name)

    declared_execution_roles = _declared_count_map(
        manifest.get("countsByExecutionRole"), "countsByExecutionRole", EXECUTION_ROLES
    )
    declared_declaration_kinds = _declared_count_map(
        manifest.get("countsByDeclarationKind"),
        "countsByDeclarationKind",
        DECLARATION_KINDS,
    )
    declared_actions = _declared_count_map(
        manifest.get("countsByAction"), "countsByAction", ACTIONS
    )
    if dict(sorted(execution_role_counts.items())) != dict(
        sorted(declared_execution_roles.items())
    ):
        raise RuntimeError(
            "boundary manifest countsByExecutionRole does not match occurrence records"
        )
    if dict(sorted(declaration_kind_counts.items())) != dict(
        sorted(declared_declaration_kinds.items())
    ):
        raise RuntimeError(
            "boundary manifest countsByDeclarationKind does not match occurrence records"
        )
    if dict(sorted(action_counts.items())) != dict(
        sorted(declared_actions.items())
    ):
        raise RuntimeError(
            "boundary manifest countsByAction does not match occurrence records"
        )
    if manifest["moduleFileCount"] != len(modules):
        raise RuntimeError("boundary manifest moduleFileCount does not match module records")
    if manifest["inventoriedModuleCount"] != inventoried_module_count:
        raise RuntimeError(
            "boundary manifest inventoriedModuleCount does not match module records"
        )
    if manifest["occurrenceCount"] != occurrence_count:
        raise RuntimeError("boundary manifest occurrenceCount does not match occurrence records")
    if manifest["nestedOccurrenceCount"] != nested_occurrence_count:
        raise RuntimeError(
            "boundary manifest nestedOccurrenceCount does not match occurrence records"
        )
    if manifest["duplicateSyntaxRecords"] != duplicate_syntax_count:
        raise RuntimeError(
            "boundary manifest duplicateSyntaxRecords does not match module records"
        )
    if manifest["duplicateScopeSyntaxRecords"] != duplicate_scope_count:
        raise RuntimeError(
            "boundary manifest duplicateScopeSyntaxRecords does not match module records"
        )

    unresolved = action_counts.get("unresolved", 0)
    if unresolved and manifest.get("allowUnresolved") is not True:
        raise RuntimeError(
            f"boundary manifest contains {unresolved} unresolved occurrences"
        )


def publish_manifest(path: Path, manifest: dict[str, Any]) -> None:
    """Replace ``path`` only after the manifest satisfies its declared policy."""
    enforce_manifest_policy(manifest)
    write_manifest(path, manifest)


def build_manifest_command(args: argparse.Namespace) -> None:
    paths = module_paths(args.module_prefix, args.max_modules)
    manifest = build_manifest(
        paths,
        module_prefix=args.module_prefix,
        expected_commit=args.commit or None,
        allow_dirty=args.allow_dirty,
        allow_unresolved=args.allow_unresolved,
        inventory_batch_size=args.inventory_batch_size,
        scope_batch_size=args.scope_batch_size,
        timeout=args.timeout,
        checkpoint_root=Path(args.checkpoint_root) if args.checkpoint_root else None,
    )
    output = Path(args.output)
    publish_manifest(output, manifest)
    print(
        "boundary corpus manifest: "
        f"modules={manifest['moduleFileCount']}, "
        f"occurrences={manifest['occurrenceCount']}, "
        f"actions={manifest['countsByAction']}: ok"
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    manifest = commands.add_parser("manifest")
    manifest.add_argument("--output", required=True)
    manifest.add_argument("--commit", default="")
    manifest.add_argument("--module-prefix", default="Mathlib/")
    manifest.add_argument("--max-modules", type=int)
    manifest.add_argument("--inventory-batch-size", type=int, default=2048)
    manifest.add_argument("--scope-batch-size", type=int, default=128)
    manifest.add_argument("--timeout", type=int, default=3600)
    manifest.add_argument("--allow-dirty", action="store_true")
    manifest.add_argument("--allow-unresolved", action="store_true")
    manifest.add_argument(
        "--checkpoint-root",
        help="opt in to durable inventory/scope batch checkpoints at this path",
    )
    manifest.set_defaults(function=build_manifest_command)
    return result


def main() -> None:
    args = parser().parse_args()
    try:
        args.function(args)
    except Exception as error:
        print(f"boundary corpus manifest failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
