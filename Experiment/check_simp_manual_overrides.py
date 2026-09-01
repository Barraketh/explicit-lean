#!/usr/bin/env python3
"""Compile and semantically verify every pinned manual ``simp`` replacement."""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import tempfile
import time

import boundary_materialize_shard as materializer
import simp_engine_boundary_corpus as corpus
import simp_engine_inventory as inventory
import simp_manual_overrides as overrides


ROOT = Path(__file__).resolve().parents[1]
TIMEOUT = 900
IMPLEMENTATION_PATHS = tuple(
    ROOT / "Experiment" / name
    for name in (
        "check_simp_manual_overrides.py",
        "simp_manual_overrides.py",
        "boundary_materialize_shard.py",
        "SimpEngineDeclarationOracle.lean",
        "simp_engine_inventory.py",
        "simp_engine_boundary_corpus.py",
        "boundary_protocol.py",
        "boundary_expr_codec.py",
        "boundary_public_theorem_codec.py",
        "lean_toolchain_cache.py",
        "process_runner.py",
        "check_simp_engine_pin.py",
        "check_simp_engine_boundary_scope.py",
        "check_simp_engine_boundary_source.py",
        "inventory_checkpoint.py",
        "analysis_checkpoint_identity.py",
    )
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def exact_gap_check(
    original: bytes, patched: bytes, entries: list[dict[str, object]]
) -> None:
    old_cursor = new_cursor = 0
    for entry in entries:
        start, end = int(entry["startByte"]), int(entry["endByte"])
        gap = original[old_cursor:start]
        if patched[new_cursor : new_cursor + len(gap)] != gap:
            raise RuntimeError("manual override changed bytes outside its pinned range")
        new_cursor += len(gap)
        rendered = overrides.render(entry, original)
        if patched[new_cursor : new_cursor + len(rendered)] != rendered:
            raise RuntimeError("manual override rendering differs from the pinned replacement")
        if b"-- Original simp:\n" not in rendered:
            raise RuntimeError("manual override did not retain its original as comments")
        new_cursor += len(rendered)
        old_cursor = end
    if patched[new_cursor:] != original[old_cursor:]:
        raise RuntimeError("manual override changed trailing authored bytes")


def supported_multiset(records: list[dict[str, object]]) -> Counter[tuple[str, str]]:
    return Counter(
        (str(record["kind"]), str(record["source"]))
        for record in records
        if record.get("kind") in inventory.SUPPORTED_KINDS
    )


def supported_position_multiset(
    records: list[dict[str, object]],
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


def check_module(
    module: str,
    entries: list[dict[str, object]],
    work: Path,
    dylib: str,
) -> dict[str, object]:
    source_path = (corpus.MATHLIB / Path(*module.split("/"))).resolve()
    try:
        source_path.relative_to(corpus.MATHLIB.resolve())
    except ValueError as error:
        raise RuntimeError(f"manual override source escapes Mathlib: {module}") from error
    original = source_path.read_bytes()
    overrides.validate_against_source(module, original, entries)
    patched = overrides.apply(module, original, entries)
    exact_gap_check(original, patched, entries)

    original_path = materializer._copy_at_module_root(work / "original", module, original)
    patched_path = materializer._copy_at_module_root(work / "patched", module, patched)
    original_inventory = inventory.syntax_inventory_file(
        original_path, module, TIMEOUT, allow_elaboration_errors=True, header_imports=True
    )
    patched_inventory = inventory.syntax_inventory_file(
        patched_path,
        module + ".manual",
        TIMEOUT,
        allow_elaboration_errors=True,
        header_imports=True,
    )
    removed: Counter[tuple[str, str]] = Counter()
    removed_ranges: set[tuple[int, int]] = set()
    for entry in entries:
        matches = [
            record
            for record in original_inventory
            if int(record["startByte"]) == int(entry["startByte"])
            and int(record["endByte"]) == int(entry["endByte"])
            and str(record["source"]) == str(entry["source"])
        ]
        if len(matches) != 1:
            raise RuntimeError(
                f"manual override is not one exact syntax occurrence: {entry['occurrence']}"
            )
        removed[(str(matches[0]["kind"]), str(matches[0]["source"]))] += 1
        removed_ranges.add((int(entry["startByte"]), int(entry["endByte"])))

    expected_positions: Counter[tuple[str, str, int, int]] = Counter()
    for record in original_inventory:
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
        expected_positions[
            (str(record["kind"]), str(record["source"]), start + delta, end + delta)
        ] += 1
    actual_positions = supported_position_multiset(patched_inventory)
    if actual_positions != expected_positions:
        raise RuntimeError(
            f"manual override changed the remaining positioned simp inventory in {module}: "
            f"expected {expected_positions}, found {actual_positions}"
        )
    actual = supported_multiset(patched_inventory)

    started = time.monotonic()
    code, output, elapsed = materializer._compile_copy(patched_path, dylib, TIMEOUT)
    log = work / "patched-compiler.log"
    log.write_text(output, encoding="utf-8")
    if code != 0:
        raise RuntimeError(f"manual override did not compile in {module}; see {log}")
    materializer.reject_compiler_sorry_warning(output, f"manual override compile for {module}")
    oracle = materializer.run_declaration_oracle(
        module, original_path, patched_path, work / "oracle", dylib, TIMEOUT
    )
    return {
        "module": module,
        "compiledModule": corpus.compiled_module_name(module),
        "sourcePath": str(source_path.resolve()),
        "sourceSha256": sha256(original),
        "patchedPath": str(patched_path.resolve()),
        "patchedSha256": sha256(patched),
        "overrideIds": [str(entry["occurrence"]) for entry in entries],
        "originalSupportedCount": sum(supported_multiset(original_inventory).values()),
        "patchedSupportedCount": sum(actual.values()),
        "removedSupportedCount": sum(removed.values()),
        "compileSuccess": True,
        "compileSeconds": elapsed,
        "compilerLog": {"path": str(log.resolve()), "sha256": sha256(log.read_bytes())},
        "declarationOracle": oracle,
        "wallSeconds": time.monotonic() - started,
    }


def negative_controls(database: Path, work: Path) -> None:
    value = json.loads(database.read_bytes())
    duplicate = json.loads(json.dumps(value))
    duplicate["overrides"].append(json.loads(json.dumps(duplicate["overrides"][0])))
    path = work / "duplicate.json"
    path.write_text(json.dumps(duplicate), encoding="utf-8")
    try:
        overrides.load(path)
    except RuntimeError as error:
        if "duplicate manual override occurrence" not in str(error):
            raise
    else:
        raise RuntimeError("manual override database accepted a duplicate occurrence")

    traversal = json.loads(json.dumps(value))
    traversal["overrides"][0]["module"] = "Mathlib/../../../../tmp/escape.lean"
    path = work / "traversal.json"
    path.write_text(json.dumps(traversal), encoding="utf-8")
    try:
        overrides.load(path)
    except RuntimeError as error:
        if "invalid Mathlib module path" not in str(error):
            raise
    else:
        raise RuntimeError("manual override database accepted path traversal")

    for token in ("simpa", "aesop", "exact?", "first | rfl", "try rfl", "repeat rfl"):
        searched = json.loads(json.dumps(value))
        searched["overrides"][0]["replacement"] = token
        label = token.replace("?", "q").replace(" ", "-").replace("|", "or")
        path = work / f"search-{label}.json"
        path.write_text(json.dumps(searched), encoding="utf-8")
        try:
            overrides.load(path)
        except RuntimeError as error:
            if "is not an explicit replacement" not in str(error):
                raise
        else:
            raise RuntimeError(f"manual override database accepted search tactic {token}")

    entries = overrides.load(database)
    first = entries[0]
    module = str(first["module"])
    source = (corpus.MATHLIB / Path(*module.split("/"))).read_bytes()
    changed = [dict(entry) for entry in entries]
    changed[0]["moduleSourceSha256"] = "0" * 64
    try:
        overrides.validate_against_source(module, source, changed)
    except RuntimeError as error:
        if "module source hash changed" not in str(error):
            raise
    else:
        raise RuntimeError("manual override accepted a changed source identity")


def main() -> None:
    database = overrides.DEFAULT_PATH
    database_bytes = database.read_bytes()
    expected_environment, entries = overrides.load_database(database)
    if database.read_bytes() != database_bytes:
        raise RuntimeError("manual override database changed while loading")
    if not entries:
        raise RuntimeError("manual override checker requires at least one entry")
    corpus_implementation_hashes = corpus.implementation_hashes()
    implementation_paths = sorted(
        set(IMPLEMENTATION_PATHS)
        | {ROOT / relative for relative in corpus_implementation_hashes}
    )
    implementation_bytes = {path: path.read_bytes() for path in implementation_paths}
    for relative, expected_hash in corpus_implementation_hashes.items():
        if sha256(implementation_bytes[ROOT / relative]) != expected_hash:
            raise RuntimeError(f"boundary implementation hash changed while loading: {relative}")
    actual_mathlib, actual_lean = corpus.verify_environment()
    actual_environment = {"mathlibCommit": actual_mathlib, "lean": actual_lean}
    if actual_environment != expected_environment:
        raise RuntimeError(
            f"manual override environment mismatch: expected {expected_environment}, "
            f"found {actual_environment}"
        )
    repository_commit = corpus.current_commit()
    package_identity = corpus.pinned_package_identity()
    parent = ROOT / ".lake" / "week-2026-08-31" / "manual-overrides"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="check-", dir=parent))
    print(f"manual override evidence: {work}", flush=True)
    negative_controls(database, work)
    dylib = materializer._query_dynamic_library(TIMEOUT, work / "runtime")
    runtime_path = Path(dylib).resolve()
    runtime_bytes = runtime_path.read_bytes()
    oracle_runtime_path = materializer._oracle_runtime_path()
    oracle_target, _ = materializer.tool_cache.TOOLS["oracle"]
    materializer.tool_cache._build("oracle", oracle_target, oracle_runtime_path)
    oracle_runtime_bytes = oracle_runtime_path.read_bytes()
    modules = []
    for module, module_entries in overrides.entries_by_module(entries).items():
        modules.append(check_module(module, module_entries, work / module.replace("/", "-"), dylib))
    final_mathlib, final_lean = corpus.verify_environment()
    if {"mathlibCommit": final_mathlib, "lean": final_lean} != actual_environment:
        raise RuntimeError("manual override environment changed during verification")
    if corpus.current_commit() != repository_commit:
        raise RuntimeError("repository commit changed during manual override verification")
    if corpus.pinned_package_identity() != package_identity:
        raise RuntimeError("package identity changed during manual override verification")
    if corpus.implementation_hashes() != corpus_implementation_hashes:
        raise RuntimeError("boundary implementation source set changed during verification")
    if database.read_bytes() != database_bytes:
        raise RuntimeError("manual override database changed during verification")
    for path, initial in implementation_bytes.items():
        if path.read_bytes() != initial:
            raise RuntimeError(f"manual override implementation changed during verification: {path}")
    if runtime_path.read_bytes() != runtime_bytes:
        raise RuntimeError("shared runtime changed during manual override verification")
    if oracle_runtime_path.read_bytes() != oracle_runtime_bytes:
        raise RuntimeError("declaration oracle runtime changed during verification")
    report = {
        "kind": "simp_manual_override_check",
        "schema": 1,
        "database": str(database.resolve()),
        "databaseSha256": sha256(database_bytes),
        "runtime": str(runtime_path),
        "runtimeSha256": sha256(runtime_bytes),
        "oracleRuntime": str(oracle_runtime_path),
        "oracleRuntimeSha256": sha256(oracle_runtime_bytes),
        "repositoryCommit": repository_commit,
        "environment": actual_environment,
        "packageIdentity": package_identity,
        "implementationHashes": {
            str(path.relative_to(ROOT)): sha256(data)
            for path, data in implementation_bytes.items()
        },
        "overrideCount": len(entries),
        "moduleCount": len(modules),
        "modules": modules,
        "compileSuccess": True,
    }
    report_path = work / "report.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"manual simp overrides: passed: {report_path}", flush=True)


if __name__ == "__main__":
    main()
