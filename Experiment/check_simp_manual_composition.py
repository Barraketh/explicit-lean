#!/usr/bin/env python3
"""Run the manual simp replacements through the ordinary boundary pipeline.

This is an integration checker for the small exceptional replacement table.  It
keeps the pinned Mathlib source as the declaration-oracle stock side, applies
the manual replacements to a disposable source copy, freshly classifies that
copy, and lets the normal boundary materializer process every remaining call.
The checker intentionally publishes evidence separately from campaign shard
reports; it does not claim corpus coverage.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import tempfile
from typing import Any, Iterable

import boundary_materialize_shard as materializer
import check_simp_engine_boundary_scope as scope
import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
import simp_manual_overrides as overrides


ROOT = Path(__file__).resolve().parents[1]
MATHLIB = corpus.MATHLIB
REPORT_KIND = "simp_manual_composition_check"
REPORT_SCHEMA = 1
ROOT_RECEIPT_KIND = "simp_manual_composition_root_verification"
ROOT_RECEIPT_SCHEMA = 1
ROOT_RECEIPT_NAME = "root-verification.json"
DEFAULT_TIMEOUT = 600
EVIDENCE_PARENT = ROOT / ".lake" / "week-2026-08-31" / "manual-composition"

IMPLEMENTATION_PATHS = (
    Path(__file__).resolve(),
    Path(overrides.__file__).resolve(),
    Path(materializer.__file__).resolve(),
    Path(corpus.__file__).resolve(),
    Path(scope.__file__).resolve(),
    Path(inventory.__file__).resolve(),
    ROOT / "Experiment" / "boundary_protocol.py",
    ROOT / "Experiment" / "SimpEngineDeclarationOracle.lean",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _module_source(module: str) -> Path:
    path = (MATHLIB / Path(*module.split("/"))).resolve()
    try:
        path.relative_to(MATHLIB.resolve())
    except ValueError as error:
        raise RuntimeError(f"manual composition source escapes Mathlib: {module}") from error
    if not path.is_file():
        raise RuntimeError(f"manual composition source is missing: {path}")
    return path


def _copy_module(root: Path, module: str, source: bytes) -> Path:
    destination = root / Path(*module.split("/"))
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return destination


def _module_evidence_slugs(modules: Iterable[str]) -> dict[str, str]:
    """Return sanitized module directory names, rejecting lossy collisions."""
    by_slug: dict[str, str] = {}
    for module in modules:
        slug = materializer._sanitize_stem(
            module.removeprefix("Mathlib/").removesuffix(".lean")
        )
        previous = by_slug.get(slug)
        if previous is not None and previous != module:
            raise RuntimeError(
                "manual composition module evidence-directory slug collision: "
                f"{previous!r} and {module!r} both map to {slug!r}"
            )
        by_slug[slug] = module
    return {module: slug for slug, module in by_slug.items()}


def _assert_manual_patch(
    original: bytes, patched: bytes, entries: Iterable[dict[str, Any]], module: str
) -> list[dict[str, Any]]:
    """Check the exact splice and return authenticated rendered entries."""
    checked = list(entries)
    cursor_old = cursor_new = 0
    rendered_entries: list[dict[str, Any]] = []
    for entry in checked:
        start, end = int(entry["startByte"]), int(entry["endByte"])
        if original[start:end].decode("utf-8") != entry["source"]:
            raise RuntimeError(f"manual source bytes changed before composition: {module}:{entry['occurrence']}")
        gap = original[cursor_old:start]
        if patched[cursor_new : cursor_new + len(gap)] != gap:
            raise RuntimeError(f"manual composition changed authored bytes in {module}")
        cursor_new += len(gap)
        rendered = overrides.render(entry, original)
        if b"-- Original simp:\n" not in rendered:
            raise RuntimeError(f"manual composition dropped original simp comments: {entry['occurrence']}")
        if patched[cursor_new : cursor_new + len(rendered)] != rendered:
            raise RuntimeError(f"manual rendering differs from the pinned replacement: {entry['occurrence']}")
        rendered_entries.append(
            {
                "occurrence": str(entry["occurrence"]),
                "canonicalStartByte": start,
                "canonicalEndByte": end,
                "source": str(entry["source"]),
                "renderedSha256": sha256(rendered),
                "renderedLength": len(rendered),
                "effectiveStartByte": cursor_new,
                "effectiveEndByte": cursor_new + len(rendered),
            }
        )
        cursor_new += len(rendered)
        cursor_old = end
    if patched[cursor_new:] != original[cursor_old:]:
        raise RuntimeError(f"manual composition changed trailing authored bytes in {module}")
    return rendered_entries


def _supported_position_multiset(
    records: Iterable[dict[str, Any]],
) -> Counter[tuple[str, str, int, int]]:
    return Counter(
        (
            str(record["kind"]),
            str(record["source"]),
            int(record["startByte"]),
            int(record["endByte"]),
        )
        for record in records
        if record.get("kind") in inventory.SUPPORTED_KINDS
    )


def _expected_patched_positions(
    module: str,
    original: bytes,
    records: list[dict[str, Any]],
    entries: list[dict[str, Any]],
) -> tuple[Counter[tuple[str, str, int, int]], list[dict[str, Any]]]:
    """Authenticate the removed syntax nodes and relocate every untouched node."""
    removed_ranges: set[tuple[int, int]] = set()
    removed: list[dict[str, Any]] = []
    for entry in entries:
        start, end = int(entry["startByte"]), int(entry["endByte"])
        matches = [
            record
            for record in records
            if int(record["startByte"]) == start
            and int(record["endByte"]) == end
            and str(record["source"]) == str(entry["source"])
        ]
        if len(matches) != 1:
            raise RuntimeError(
                f"manual override is not one exact syntax occurrence in {module}: "
                f"{entry['occurrence']}"
            )
        removed_ranges.add((start, end))
        removed.append(
            {
                "occurrence": str(entry["occurrence"]),
                "kind": str(matches[0]["kind"]),
                "source": str(matches[0]["source"]),
                "startByte": start,
                "endByte": end,
            }
        )

    expected: Counter[tuple[str, str, int, int]] = Counter()
    for record in records:
        if record.get("kind") not in inventory.SUPPORTED_KINDS:
            continue
        start, end = int(record["startByte"]), int(record["endByte"])
        if (start, end) in removed_ranges:
            continue
        if any(
            start < int(entry["endByte"]) and int(entry["startByte"]) < end
            for entry in entries
        ):
            raise RuntimeError(
                f"manual override range contains an unaccounted supported occurrence in {module}"
            )
        delta = sum(
            len(overrides.render(entry, original))
            - (int(entry["endByte"]) - int(entry["startByte"]))
            for entry in entries
            if int(entry["endByte"]) <= start
        )
        expected[(str(record["kind"]), str(record["source"]), start + delta, end + delta)] += 1
    return expected, removed


def _fresh_classification(
    module: str,
    source_path: Path,
    source: bytes,
    expected_positions: Counter[tuple[str, str, int, int]],
    timeout: int,
) -> tuple[materializer.SelectedModule, dict[str, Any]]:
    """Inventory and scope-classify one patched temporary module."""
    raw_inventory = inventory.syntax_inventory_file(
        source_path,
        module,
        timeout,
        allow_elaboration_errors=True,
        header_imports=True,
    )
    entries, nested, duplicate_syntax = corpus.validate_module_inventory(
        module, source, raw_inventory
    )
    actual_positions = _supported_position_multiset(entries)
    if actual_positions != expected_positions:
        raise RuntimeError(
            f"manual overrides changed the remaining positioned simp inventory in {module}: "
            f"expected {expected_positions}, found {actual_positions}"
        )
    compiled_module = corpus.compiled_module_name(module)
    specs = [scope.ModuleSpec(compiled_module, source_path, len(entries))]
    scoped, declarations, fallbacks = scope.load_records_with_fallbacks(
        specs, batch_size=1, timeout=timeout
    )
    classified, duplicate_scope = corpus.join_scope_records(
        module,
        entries,
        scoped.get(compiled_module, []),
        declarations.get(compiled_module, []),
    )
    unresolved = [entry for entry in classified if entry["action"] == "unresolved"]
    execution_evidence: dict[str, dict[str, Any]] = {}
    if unresolved:
        unresolved_ids = {str(entry["id"]) for entry in unresolved}
        unresolved_entries = [entry for entry in entries if str(entry["id"]) in unresolved_ids]
        execution_evidence = scope.apply_execution_evidence(
            compiled_module,
            source,
            unresolved,
            entries=unresolved_entries,
            timeout=timeout,
        )
    remaining_unresolved = [entry for entry in classified if entry["action"] == "unresolved"]
    if remaining_unresolved:
        raise RuntimeError(
            f"patched composition left unresolved calls in {module}: "
            f"{[entry['id'] for entry in remaining_unresolved]}"
        )
    materialize = tuple(entry for entry in classified if entry["action"] == "materialize")
    retain = tuple(entry for entry in classified if entry["action"] == "retain")
    if not materialize and not retain:
        raise RuntimeError(f"patched composition inventoried no supported calls in {module}")
    selected = materializer.SelectedModule(
        module=module,
        compiled_module=compiled_module,
        source_path=source_path,
        source=source,
        occurrences=tuple(classified),
        materialize=materialize,
        retain=retain,
    )
    return selected, {
        "inventoryCount": len(entries),
        "nestedCount": nested,
        "duplicateSyntaxRecords": duplicate_syntax,
        "duplicateScopeRecords": duplicate_scope,
        "scopeFrontendFallbacks": sorted(fallbacks),
        "executionEvidence": execution_evidence,
    }


def _retained_records(selected: materializer.SelectedModule) -> list[dict[str, Any]]:
    return [
        {
            "id": str(entry["id"]),
            "kind": str(entry["kind"]),
            "source": str(entry["source"]),
            "startByte": int(entry["startByte"]),
            "endByte": int(entry["endByte"]),
        }
        for entry in selected.retain
    ]


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    try:
        temporary.write_text(
            json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def _evidence_file_hashes(evidence_root: Path) -> dict[str, str]:
    """Hash the completed evidence tree, excluding the receipt itself.

    The receipt is deliberately outside this manifest to avoid a hash cycle.
    Every other filesystem entry must be a regular file or directory with no
    symlink anywhere in the evidence tree.
    """
    root = evidence_root.resolve()
    if not root.is_dir():
        raise RuntimeError(f"manual composition evidence root is not a directory: {root}")
    receipt = root / ROOT_RECEIPT_NAME
    hashes: dict[str, str] = {}
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            raise RuntimeError(f"manual composition evidence contains a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise RuntimeError(f"manual composition evidence contains a non-file: {path}")
        if path == receipt:
            continue
        relative = path.relative_to(root).as_posix()
        if relative in hashes:
            raise RuntimeError(f"manual composition evidence path repeated: {relative}")
        hashes[relative] = sha256(path.read_bytes())
    if "report.json" not in hashes:
        raise RuntimeError("manual composition evidence tree is missing report.json")
    return hashes


def _write_root_receipt(
    evidence_root: Path, report_path: Path, report: dict[str, Any]
) -> Path:
    """Persist a deterministic, non-recursive hash receipt for one run."""
    root = evidence_root.resolve()
    report_path = Path(report_path)
    if report_path.is_symlink():
        raise RuntimeError("manual composition report is not a regular file")
    report_path = report_path.resolve()
    if report_path.parent != root:
        raise RuntimeError("manual composition report is outside its evidence root")
    if not report_path.is_file():
        raise RuntimeError("manual composition report is not a regular file")
    hashes = _evidence_file_hashes(root)
    if hashes["report.json"] != sha256(report_path.read_bytes()):
        raise RuntimeError("manual composition report changed before root receipt")
    canonical_manifest = json.dumps(
        hashes, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    receipt_path = root / ROOT_RECEIPT_NAME
    receipt = {
        "kind": ROOT_RECEIPT_KIND,
        "schema": ROOT_RECEIPT_SCHEMA,
        "status": (
            "verified-full-database"
            if report["runMode"] == "full_database"
            else "verified-focused-diagnostic"
        ),
        "acceptedCampaignCoverage": bool(report["acceptedCampaignCoverage"]),
        "runMode": report["runMode"],
        "evidenceRoot": str(root),
        "report": {
            "path": str(report_path),
            "sha256": hashes["report.json"],
        },
        "evidenceFileCount": len(hashes),
        "evidenceFiles": hashes,
        "evidenceTreeSha256": sha256(canonical_manifest),
        "excludedFromEvidenceFiles": ROOT_RECEIPT_NAME,
    }
    _write_json(receipt_path, receipt)
    if _evidence_file_hashes(root) != hashes:
        receipt_path.unlink(missing_ok=True)
        raise RuntimeError("manual composition evidence changed while writing root receipt")
    return receipt_path


def check_module(
    module: str,
    module_entries: list[dict[str, Any]],
    evidence_root: Path,
    dylib: str,
    timeout: int,
    module_slug: str,
) -> dict[str, Any]:
    source_path = _module_source(module)
    canonical = source_path.read_bytes()
    patched = overrides.apply(module, canonical, module_entries)
    rendered_entries = _assert_manual_patch(canonical, patched, module_entries, module)
    manual_path = _copy_module(evidence_root / "manual", module, patched)
    canonical_path = _copy_module(evidence_root / "canonical", module, canonical)

    raw_canonical_inventory = inventory.syntax_inventory_file(
        canonical_path,
        module,
        timeout,
        allow_elaboration_errors=True,
        header_imports=True,
    )
    canonical_inventory, canonical_nested, canonical_duplicates = corpus.validate_module_inventory(
        module, canonical, raw_canonical_inventory
    )
    expected_positions, removed_occurrences = _expected_patched_positions(
        module, canonical, canonical_inventory, module_entries
    )

    # The fresh inventory is deliberately run on the patched source, before
    # constructing the ordinary SelectedModule materialization input.
    selected, classification = _fresh_classification(
        module, manual_path, patched, expected_positions, timeout
    )
    classification["canonicalInventoryCount"] = len(canonical_inventory)
    classification["canonicalNestedCount"] = canonical_nested
    classification["canonicalDuplicateSyntaxRecords"] = canonical_duplicates
    classification["removedManualOccurrences"] = removed_occurrences
    module_root = evidence_root / module_slug
    boundary = materializer._module_result(
        selected, evidence_root, dylib, timeout, recording_mode="applied"
    )
    final_path = Path(str(boundary["materializedPath"]))
    final_source = final_path.read_bytes()
    entries_by_id = {
        str(entry["occurrence"]): entry for entry in module_entries
    }
    for rendered in rendered_entries:
        entry = entries_by_id[str(rendered["occurrence"])]
        expected = overrides.render(entry, canonical)
        if rendered["renderedSha256"] != sha256(expected):
            raise RuntimeError(f"manual rendered provenance changed in {module}")
        if expected not in final_source:
            raise RuntimeError(f"final composite dropped manual original comments in {module}")

    oracle_root = module_root / "canonical-oracle"
    canonical_oracle = materializer.run_declaration_oracle(
        module,
        canonical_path,
        final_path,
        oracle_root,
        dylib,
        timeout,
    )
    retained = _retained_records(selected)
    if boundary["retainCount"] != len(retained) or boundary["retainIds"] != [item["id"] for item in retained]:
        raise RuntimeError(f"retained occurrence report disagrees in {module}")
    return {
        "module": module,
        "compiledModule": selected.compiled_module,
        "canonicalSource": {
            "path": str(canonical_path.resolve()),
            "sha256": sha256(canonical),
        },
        "manualBase": {
            "path": str(manual_path.resolve()),
            "sha256": sha256(patched),
        },
        "manualOverrides": rendered_entries,
        "manualOverrideIds": [str(entry["occurrence"]) for entry in module_entries],
        "freshClassification": classification,
        "retainedOccurrences": retained,
        "retainedCount": len(retained),
        "boundaryResult": boundary,
        "finalComposite": {
            "path": str(final_path.resolve()),
            "sha256": sha256(final_source),
        },
        "canonicalDeclarationOracle": canonical_oracle,
    }


def run(
    modules: list[str], timeout: int
) -> tuple[dict[str, Any], Path]:
    database = overrides.DEFAULT_PATH.resolve()
    database_bytes = database.read_bytes()
    expected_environment, entries = overrides.load_database(database)
    if not entries:
        raise RuntimeError("manual composition requires at least one override")
    actual_mathlib, actual_lean = corpus.verify_environment()
    actual_environment = {"mathlibCommit": actual_mathlib, "lean": actual_lean}
    if actual_environment != expected_environment:
        raise RuntimeError(
            f"manual override environment mismatch: expected {expected_environment}, found {actual_environment}"
        )
    by_module = overrides.entries_by_module(entries)
    if modules == []:
        modules = sorted(by_module)
    if len(modules) != len(set(modules)):
        raise RuntimeError("manual composition modules must be unique")
    unknown = sorted(set(modules) - set(by_module))
    if unknown:
        raise RuntimeError(f"manual composition module is absent from override database: {unknown}")
    module_slugs = _module_evidence_slugs(modules)
    full_database = set(modules) == set(by_module)

    corpus_implementation_hashes = corpus.implementation_hashes()
    implementation_paths = sorted(
        set(IMPLEMENTATION_PATHS)
        | {ROOT / relative for relative in corpus_implementation_hashes}
    )
    implementation_bytes = {path: path.read_bytes() for path in implementation_paths}
    for relative, expected_hash in corpus_implementation_hashes.items():
        if sha256(implementation_bytes[ROOT / relative]) != expected_hash:
            raise RuntimeError(f"boundary implementation hash changed while loading: {relative}")
    source_paths = {module: _module_source(module) for module in modules}
    source_bytes = {module: path.read_bytes() for module, path in source_paths.items()}
    package_identity = corpus.pinned_package_identity()
    repository_commit = corpus.current_commit()
    parent = EVIDENCE_PARENT
    parent.mkdir(parents=True, exist_ok=True)
    evidence_root = Path(tempfile.mkdtemp(prefix="run-", dir=parent))
    dylib = materializer._query_dynamic_library(timeout, evidence_root / "runtime")
    runtime_path = Path(dylib).resolve()
    runtime_bytes = runtime_path.read_bytes()
    oracle_runtime_path = materializer._oracle_runtime_path()
    oracle_target, _ = materializer.tool_cache.TOOLS["oracle"]
    materializer.tool_cache._build("oracle", oracle_target, oracle_runtime_path)
    oracle_runtime_bytes = oracle_runtime_path.read_bytes()
    results = []
    for module in modules:
        results.append(
            check_module(
                module,
                by_module[module],
                evidence_root / "modules",
                dylib,
                timeout,
                module_slugs[module],
            )
        )

    if database.read_bytes() != database_bytes:
        raise RuntimeError("manual override database changed during composition")
    final_mathlib, final_lean = corpus.verify_environment()
    if {"mathlibCommit": final_mathlib, "lean": final_lean} != actual_environment:
        raise RuntimeError("manual composition environment changed during run")
    if corpus.current_commit() != repository_commit:
        raise RuntimeError("repository commit changed during manual composition")
    if corpus.pinned_package_identity() != package_identity:
        raise RuntimeError("package identity changed during manual composition")
    if corpus.implementation_hashes() != corpus_implementation_hashes:
        raise RuntimeError("boundary implementation source set changed during composition")
    for module, path in source_paths.items():
        if path.read_bytes() != source_bytes[module]:
            raise RuntimeError(f"canonical Mathlib source changed during manual composition: {module}")
    for path, initial in implementation_bytes.items():
        if path.read_bytes() != initial:
            raise RuntimeError(f"implementation changed during manual composition: {path}")
    if runtime_path.read_bytes() != runtime_bytes:
        raise RuntimeError("shared runtime changed during manual composition")
    if oracle_runtime_path.read_bytes() != oracle_runtime_bytes:
        raise RuntimeError("declaration oracle runtime changed during manual composition")

    report_path = evidence_root / "report.json"
    root_receipt_path = evidence_root / ROOT_RECEIPT_NAME
    report = {
        "kind": REPORT_KIND,
        "schema": REPORT_SCHEMA,
        "status": "passed" if full_database else "diagnostic",
        "acceptanceStatus": (
            "full_database_check" if full_database else "provisional"
        ),
        "runMode": "full_database" if full_database else "focused",
        "acceptedCampaignCoverage": False,
        "database": {
            "path": str(database),
            "sha256": sha256(database_bytes),
            "environment": expected_environment,
            "overrideCount": len(entries),
            "moduleCount": len(by_module),
        },
        "environment": actual_environment,
        "repositoryCommit": repository_commit,
        "packageIdentity": package_identity,
        "timeoutSeconds": timeout,
        "selectedModules": modules,
        "moduleEvidenceSlugs": module_slugs,
        "rootVerificationPath": str(root_receipt_path.resolve()),
        "implementationHashes": {
            str(path.relative_to(ROOT)): sha256(data)
            for path, data in implementation_bytes.items()
        },
        "runtime": {"path": str(runtime_path), "sha256": sha256(runtime_bytes)},
        "oracleRuntime": {
            "path": str(oracle_runtime_path),
            "sha256": sha256(oracle_runtime_bytes),
        },
        "modules": results,
        "moduleCount": len(results),
        "manualOverrideCount": sum(len(item["manualOverrideIds"]) for item in results),
        "allDatabaseOverridesChecked": set(modules) == set(by_module),
        "retainedCount": sum(int(item["retainedCount"]) for item in results),
    }
    _write_json(report_path, report)
    _write_root_receipt(evidence_root, report_path, report)
    return report, report_path


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", default=[])
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    try:
        report, path = run(args.module, args.timeout)
    except Exception as error:
        print(f"manual simp composition failed: {error}")
        return 1
    print(
        "manual simp composition: "
        f"modules={report['moduleCount']}, "
        f"overrides={report['manualOverrideCount']}, "
        f"retained={report['retainedCount']}, mode={report['runMode']}, "
        f"status={report['status']}, report={path}, "
        f"rootReceipt={report['rootVerificationPath']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
