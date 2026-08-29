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
from typing import Any, Sequence

import check_simp_engine_boundary_scope as scope
import check_simp_engine_pin as pin
import simp_engine_inventory as inventory


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = inventory.MATHLIB
REPORT_SCHEMA = 1

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

IMPLEMENTATION_SOURCE_PATTERNS = (
    "ExplicitLean.lean",
    "ExplicitLean/SimpEngine/Inventory.lean",
    "ExplicitLean/SimpEngine/Boundary.lean",
    "ExplicitLean/SimpEngine/Boundary/*.lean",
    "Experiment/SimpEngineInventory.lean",
    "Experiment/SimpEngineBoundary*.lean",
    "Experiment/check_simp_engine_boundary*.py",
    "Experiment/check_simp_engine_pin.py",
    "Experiment/simp_engine_inventory.py",
    "Experiment/simp_engine_boundary_corpus.py",
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


def inventory_batch(
    paths: Sequence[Path], timeout: int
) -> tuple[list[dict[str, Any]], list[str]]:
    command = [
        "lake",
        "env",
        "lean",
        "--run",
        "Experiment/SimpEngineInventory.lean",
        *(str(path.resolve()) for path in paths),
    ]
    completed = subprocess.run(
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
    entries: list[dict[str, Any]] = []
    fallbacks: list[str] = []
    for line in completed.stdout.splitlines():
        if line.startswith("{"):
            entries.append(json.loads(line))
        elif line.startswith("SIMP_ENGINE_INVENTORY_FULL_FALLBACK file="):
            fallbacks.append(line.split("=", 1)[1])
    return entries, fallbacks


def inventory_paths(
    paths: Sequence[Path], batch_size: int, timeout: int
) -> tuple[dict[str, list[dict[str, Any]]], list[str]]:
    if batch_size <= 0:
        raise ValueError("inventory batch size must be positive")
    path_to_module = {path.resolve(): module_path(path) for path in paths}
    if len(path_to_module) != len(paths):
        raise RuntimeError("manifest module list contains duplicate paths")
    by_module: defaultdict[str, list[dict[str, Any]]] = defaultdict(list)
    fallback_modules: set[str] = set()
    for start in range(0, len(paths), batch_size):
        entries, fallbacks = inventory_batch(paths[start : start + batch_size], timeout)
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


def classification_disposition(classification: str) -> str:
    if classification in ELIGIBLE_CLASSIFICATIONS:
        return "eligible"
    if classification in EXCLUDED_CLASSIFICATIONS:
        return "excluded"
    return "unclassified"


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
                    "classification": classified["classification"],
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
        classification = str(classified["classification"])
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
                "classification": classification,
                "reason": str(classified["reason"]),
                "disposition": classification_disposition(classification),
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
    allow_unclassified: bool = False,
    inventory_batch_size: int = 2048,
    scope_batch_size: int = 128,
    timeout: int = 3600,
) -> dict[str, Any]:
    selected = sorted((Path(path).resolve() for path in paths), key=module_path)
    if not selected:
        raise RuntimeError("boundary manifest requires at least one module")
    repository_commit = assert_repository(expected_commit, allow_dirty)
    mathlib_commit, lean = verify_environment()
    initial_implementation_hashes = implementation_hashes()
    sources = {module_path(path): path.read_bytes() for path in selected}
    by_module, fallbacks = inventory_paths(selected, inventory_batch_size, timeout)

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
                specs, batch_size=scope_batch_size
            )
        )
    else:
        scope_occurrences, scope_declarations, scope_fallbacks = {}, {}, []

    modules: list[dict[str, Any]] = []
    classification_counts: Counter[str] = Counter()
    disposition_counts: Counter[str] = Counter()
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
        unclassified = [
            occurrence
            for occurrence in classified
            if occurrence["classification"] == "unclassified"
        ]
        if unclassified:
            unknown_ids = {str(occurrence["id"]) for occurrence in unclassified}
            unknown_entries = [
                entry for entry in entries if str(entry["id"]) in unknown_ids
            ]
            scope.apply_execution_evidence(
                compiled,
                sources[module],
                unclassified,
                entries=unknown_entries,
                timeout=timeout,
            )
        duplicate_scope_records += module_scope_duplicates
        classification_counts.update(
            occurrence["classification"] for occurrence in classified
        )
        disposition_counts.update(
            occurrence["disposition"] for occurrence in classified
        )
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
    final_mathlib_commit, final_lean = verify_environment()
    if final_mathlib_commit != mathlib_commit or final_lean != lean:
        raise RuntimeError("pinned_environment_changed_during_run")

    return {
        "reportSchema": REPORT_SCHEMA,
        "kind": "simp_engine_boundary_manifest",
        "allowDirty": allow_dirty,
        "allowUnclassified": allow_unclassified,
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
        "countsByClassification": dict(sorted(classification_counts.items())),
        "countsByDisposition": dict(sorted(disposition_counts.items())),
        "implementationHashes": initial_implementation_hashes,
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


def _declared_count_map(value: object, label: str) -> dict[str, int]:
    if not isinstance(value, dict):
        raise RuntimeError(f"boundary manifest {label} must be an object")
    result: dict[str, int] = {}
    for key, count in value.items():
        if (
            not isinstance(key, str)
            or not key
            or not isinstance(count, int)
            or isinstance(count, bool)
            or count < 0
        ):
            raise RuntimeError(f"boundary manifest {label} has an invalid count")
        result[key] = count
    return result


def enforce_manifest_policy(manifest: dict[str, Any]) -> None:
    modules = manifest.get("modules")
    if not isinstance(modules, list):
        raise RuntimeError("boundary manifest modules must be an array")
    classification_counts: Counter[str] = Counter()
    disposition_counts: Counter[str] = Counter()
    occurrence_count = 0
    for module in modules:
        if not isinstance(module, dict) or not isinstance(module.get("occurrences"), list):
            raise RuntimeError("boundary manifest has an invalid module record")
        for occurrence in module["occurrences"]:
            if not isinstance(occurrence, dict):
                raise RuntimeError("boundary manifest has an invalid occurrence record")
            classification = occurrence.get("classification")
            disposition = occurrence.get("disposition")
            if not isinstance(classification, str) or not isinstance(disposition, str):
                raise RuntimeError("boundary manifest occurrence has no classification/disposition")
            expected_disposition = classification_disposition(classification)
            if disposition != expected_disposition:
                raise RuntimeError(
                    "boundary manifest occurrence classification/disposition disagree"
                )
            classification_counts[classification] += 1
            disposition_counts[disposition] += 1
            occurrence_count += 1

    declared_classifications = _declared_count_map(
        manifest.get("countsByClassification"), "countsByClassification"
    )
    declared_dispositions = _declared_count_map(
        manifest.get("countsByDisposition"), "countsByDisposition"
    )
    if dict(sorted(classification_counts.items())) != dict(
        sorted(declared_classifications.items())
    ):
        raise RuntimeError(
            "boundary manifest countsByClassification does not match occurrence records"
        )
    if dict(sorted(disposition_counts.items())) != dict(
        sorted(declared_dispositions.items())
    ):
        raise RuntimeError(
            "boundary manifest countsByDisposition does not match occurrence records"
        )
    if manifest.get("moduleFileCount") != len(modules):
        raise RuntimeError("boundary manifest moduleFileCount does not match module records")
    if manifest.get("occurrenceCount") != occurrence_count:
        raise RuntimeError("boundary manifest occurrenceCount does not match occurrence records")

    unclassified = disposition_counts.get("unclassified", 0)
    if unclassified and manifest.get("allowUnclassified") is not True:
        raise RuntimeError(
            f"boundary manifest contains {unclassified} unclassified occurrences"
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
        allow_unclassified=args.allow_unclassified,
        inventory_batch_size=args.inventory_batch_size,
        scope_batch_size=args.scope_batch_size,
        timeout=args.timeout,
    )
    output = Path(args.output)
    publish_manifest(output, manifest)
    print(
        "boundary corpus manifest: "
        f"modules={manifest['moduleFileCount']}, "
        f"occurrences={manifest['occurrenceCount']}, "
        f"dispositions={manifest['countsByDisposition']}: ok"
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
    manifest.add_argument("--allow-unclassified", action="store_true")
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
