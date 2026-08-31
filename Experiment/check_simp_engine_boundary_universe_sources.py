#!/usr/bin/env python3
"""Run a bounded source-level universe-reference diagnostic.

The two modules are deliberately diagnostic samples.  A declaration-oracle
name drift is reported as partial evidence and never as campaign acceptance.
The report hashes source copies, logs, implementation inputs, and an archived
runtime library for reproducibility.  Runtime identity never changes the
acceptance classification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tempfile

import boundary_materialize_shard as shard


ROOT = Path(__file__).resolve().parents[1]
CASES = (
    ("Mathlib/RingTheory/OreLocalization/Basic.lean", "3598744e59efa9e1"),
    ("Mathlib/AlgebraicTopology/ExtraDegeneracy.lean", "192d6d77b59c20dd"),
)
LEAN = Path("/Users/ptsier/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def file_record(path: Path) -> dict[str, str]:
    return {"path": str(path), "sha256": digest(path)}


def immutable_inputs(manifest_path: Path, manifest: dict[str, object],
                     work: Path, dylib: str) -> dict[str, object]:
    """Capture provenance without allowing it to turn into acceptance evidence."""
    if not LEAN.is_file():
        raise RuntimeError(f"pinned Lean binary is missing: {LEAN}")
    toolchain = ROOT / "lean-toolchain"
    if not toolchain.is_file():
        raise RuntimeError(f"toolchain file is missing: {toolchain}")
    runtime = Path(dylib)
    if not runtime.is_file():
        raise RuntimeError(f"queried runtime library is missing: {runtime}")
    archived = work / "runtime.dylib"
    shutil.copy2(runtime, archived)
    implementation = manifest.get("implementationHashes")
    if not isinstance(implementation, dict):
        raise RuntimeError("manifest implementationHashes must be an object")
    observed: dict[str, str] = {}
    missing: list[str] = []
    changed: list[str] = []
    for raw_path, expected in sorted(implementation.items()):
        path = ROOT / raw_path
        if not path.is_file():
            missing.append(str(raw_path))
            continue
        actual = digest(path)
        observed[str(raw_path)] = actual
        if actual != expected:
            changed.append(str(raw_path))
    version_code, version_output, _ = shard._run_command([str(LEAN), "--version"], 10)
    if version_code != 0:
        raise RuntimeError(f"pinned Lean version query failed (exit {version_code})")
    version = version_output.strip()
    return {
        "acceptanceUsesRuntimeIdentity": False,
        "manifest": file_record(manifest_path),
        "manifestImplementationHashes": implementation,
        "observedImplementationHashes": observed,
        "implementationMissing": missing,
        "implementationChanged": changed,
        "toolchain": file_record(toolchain),
        "leanBinary": file_record(LEAN),
        "leanVersion": version,
        "runtimeArchive": file_record(archived),
        "runtimeOriginal": file_record(runtime),
    }


def write_report(path: Path, status: str, manifest_path: Path,
                 records: list[dict[str, object]], provenance: dict[str, object]) -> None:
    for name in ["manifest", "toolchain", "leanBinary", "runtimeArchive", "runtimeOriginal"]:
        entry = provenance[name]
        if digest(Path(entry["path"])) != entry["sha256"]:
            raise RuntimeError(f"source diagnostic input changed during run: {name}")
    for relative, expected in provenance["observedImplementationHashes"].items():
        if digest(ROOT / relative) != expected:
            raise RuntimeError(f"source diagnostic implementation changed during run: {relative}")
    path.write_text(json.dumps({
        "status": status,
        "acceptedCampaignCoverage": False,
        "classification": "bounded_source_diagnostic",
        "manifest": str(manifest_path),
        "cases": records,
        "runtimeProvenance": provenance,
    }, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--allow-known-ore-name-drift", action="store_true",
                        help="permit only the historical Ore helper-name mismatch as partial evidence")
    parser.add_argument(
        "--output-dir", type=Path,
        help="parent for disposable diagnostic output (default: .lake/level-reference-diagnostics)",
    )
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    output_parent = args.output_dir or ROOT / ".lake" / "level-reference-diagnostics"
    output_parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="source-regression-", dir=output_parent))
    dylib = shard._query_dynamic_library(600, work)
    provenance = immutable_inputs(args.manifest, manifest, work, dylib)
    provenance["knownOreNameDriftAllowed"] = args.allow_known_ore_name_drift
    dylib = provenance["runtimeArchive"]["path"]
    report_path = work / "report.json"
    records: list[dict[str, object]] = []
    for module, occurrence in CASES:
        row = next(item for item in manifest["modules"] if item["module"] == module)
        source = (ROOT / ".lake" / "packages" / "mathlib" / module).read_bytes()
        source_hash = hashlib.sha256(source).hexdigest()
        if source_hash != row["sourceHash"]:
            raise RuntimeError(
                f"manifest/source hash mismatch for {module}: "
                f"{row['sourceHash']} != {source_hash}"
            )
        entry = next(item for item in row["occurrences"] if item["id"] == occurrence)
        case_root = work / occurrence
        case_root.mkdir()
        original = shard._copy_at_module_root(case_root / "original", module, source)
        instrumented = shard._copy_at_module_root(
            case_root / "instrumented", module, shard.instrumented_source(source, [entry])
        )
        env, recording_nonce = shard.recording_subprocess_environment()
        recording_code, recording_output, _ = shard._compile_copy(
            instrumented, dylib, 300, env=env
        )
        recording_log = case_root / "instrumented.log"
        recording_log.write_text(recording_output)
        shard.check_recording_abort_markers(
            recording_output,
            expected_nonce=recording_nonce,
            expected_module=shard.corpus.compiled_module_name(module),
        )
        if recording_code != 0:
            raise RuntimeError(f"recording failed for {module}; see {recording_log}")
        reports = shard.parse_framed_json_lines(
            recording_output,
            marker=shard.ARTIFACT_MARKER,
            expected_nonce=recording_nonce,
            label=module,
        )
        reports_path = case_root / "artifact-reports.jsonl"
        shard._write_jsonl(reports_path, reports)
        variants = shard.group_report_variants(
            reports,
            [occurrence],
            expected_module=shard.corpus.compiled_module_name(module),
            unobserved_ids=set(),
        )
        rewritten = shard.replace_all_occurrences(source, [entry], variants)
        materialized = shard._copy_at_module_root(
            case_root / "materialized", module,
            shard._inject_import(rewritten, "ExplicitLean.SimpEngine.Boundary.Tactic"),
        )
        shard._assert_context_gaps(
            source, materialized.read_bytes(), [entry],
            imported="ExplicitLean.SimpEngine.Boundary.Tactic",
            label=module, expected_without_import=rewritten,
        )
        env, replay_nonce = shard.replay_subprocess_environment()
        applied_code, applied_output, _ = shard._compile_copy(
            materialized, dylib, 300, env=env
        )
        applied_log = case_root / "materialized.log"
        applied_log.write_text(applied_output)
        replay_guard = shard.replay_guard_evidence(
            applied_output, replay_nonce, applied_log,
            shard.corpus.compiled_module_name(module),
        )
        if applied_code != 0:
            raise RuntimeError(f"materialization failed for {module}; see {applied_log}")
        fatal_error: RuntimeError | None = None
        try:
            oracle = shard.run_declaration_oracle(
                module, original, materialized, case_root, dylib, 600
            )
        except RuntimeError as error:
            detail = str(error)
            oracle_log = case_root / "declaration-oracle.log"
            oracle = {
                "status": "failed",
                "classification": "known_name_drift" if (
                    args.allow_known_ore_name_drift and module == CASES[0][0]
                    and "declaration_set_mismatch" in detail
                    and "stockOnly=[OreLocalization.instDistribMulActionOfIsScalarTower._proof_3]" in detail
                    and "appliedOnly=[OreLocalization.instDistribMulActionOfIsScalarTower._proof_2]" in detail
                ) else "oracle_failure",
                "detail": detail,
                "path": str(oracle_log),
                "sha256": digest(oracle_log) if oracle_log.is_file() else None,
            }
            if oracle["classification"] == "oracle_failure":
                fatal_error = RuntimeError(
                    f"unexpected declaration oracle failure for {module}; see {oracle_log}"
                )
        else:
            oracle["classification"] = "oracle_success"
        files = [original, instrumented, materialized, recording_log, applied_log, reports_path]
        records.append({
            "module": module,
            "occurrence": occurrence,
            "sourceHash": source_hash,
            "manifestModuleHash": row["moduleHash"],
            "executionCount": len(reports),
            "variantCount": len(variants[occurrence]),
            "sourceOccurrencesReplaced": 1,
            "recordingNonce": recording_nonce,
            "replayGuard": replay_guard,
            "oracle": oracle,
            "files": [file_record(path) for path in files],
        })
        if fatal_error is not None:
            write_report(report_path, "diagnostic_failed", args.manifest, records, provenance)
            raise fatal_error
    status = "diagnostic_passed" if all(
        item["oracle"]["classification"] == "oracle_success" for item in records
    ) else "diagnostic_partial"
    write_report(report_path, status, args.manifest, records, provenance)
    print(f"universe reference source diagnostic: {status}")
    print(f"report={report_path}")


if __name__ == "__main__":
    main()
