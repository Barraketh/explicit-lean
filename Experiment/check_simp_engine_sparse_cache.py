#!/usr/bin/env python3
"""Run paired local/async sparse-cases cache controls.

The old side is an archived schema8-frontier report; the current side is run
fresh against an explicitly supplied coherent shared library.  This fixture
checks only the boundary's cache-state guard.  It does not validate the
standalone sparse-case codec or prove general matcher equivalence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
import subprocess
from typing import Any

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_source as source


ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.SparseCacheFixture"
DEFAULT_RUNTIME = ROOT / ".lake/build/lib/libexplicitLean_ExplicitLean.dylib"
DEFAULT_OUTPUT = ROOT / ".lake/sparse-probe/promoted-controls"

BASE = """module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
public meta import Lean.Meta.Constructions.SparseCasesOn
meta import all Lean.Meta.Constructions.SparseCasesOn
open Lean Meta Elab Tactic
namespace sparse_fixture
private meta def key : SparseCasesOnKey := { indName := ``List, ctors := #[``List.nil], isPrivate := true }
private meta def existingHelper : MetaM Name := do
  let env ← getEnv
  let names := env.constants.foldStage2 (s := #[]) fun names name _ =>
    match getSparseCasesOnInfoCore env name with
    | some info => if info.indName == ``List && info.insterestingCtors == #[``List.nil] then names.push name else names
    | none => names
  unless names.size == 1 do throwError "fixture expected one helper"
  pure names[0]!
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| withExporting (isExporting := false) <| mkSparseCasesOn ``List #[``List.nil]
  __BEFORE__
private theorem asyncAnchor : True := True.intro
run_cmd Lean.Elab.Command.liftCoreM <| enableRealizationsForConst ``asyncAnchor
private meta def realizeCache : MetaM Unit := do
  let helper ← existingHelper
  let name := (``asyncAnchor).getPrefix |>.str "target" |>.str "cacheSnapshot"
  let before := (sparseCasesOnCacheExt.getState (← getEnv)).find? key
  realizeConst ``asyncAnchor name do
    addDecl (.thmDecl { name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [name] })
    modifyEnv fun env => sparseCasesOnCacheExt.modifyState env fun cache => cache.insert key helper
  let env ← getEnv
  unless (sparseCasesOnCacheExt.getState env).find? key == before do throwError "caller cache changed"
  unless (sparseCasesOnCacheExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)).find? key == some helper do
    throwError "async cache missing"
  IO.println "SPARSE_ASYNC callerUnchanged=true snapshotPresent=true"
elab "warm_cache" : tactic => realizeCache
elab "cache_discharge" : tactic => withMainContext do
  __MUTATION__
  evalTactic (← `(tactic| assumption))
private theorem target (p q : Prop) (h : p) (hpq : p → q) : q := by
  __WARM__
  first
  | simp_engine_boundary_record "sparse-__CASE__" (disch := cache_discharge) [hpq]
  | exact hpq h
end sparse_fixture
"""
ERASE = "modifyEnv fun env => sparseCasesOnCacheExt.modifyState env fun cache => cache.erase key"
INSERT = "let helper ← existingHelper\n  modifyEnv fun env => sparseCasesOnCacheExt.modifyState env fun cache => cache.insert key helper"
CASES = ("unchanged", "erase-existing", "insert-existing", "async-fresh", "async-cached")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_old_report(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict) or value.get("status") != "passed":
        raise RuntimeError(f"old sparse cache report is not a passed report: {path}")
    records = value.get("records")
    if not isinstance(records, list) or [r.get("case") for r in records] != list(CASES):
        raise RuntimeError("old sparse cache report has an unexpected case list")
    witnessed = []
    for record in records:
        source_path = Path(record["source"])
        log_path = Path(record["log"])
        runtime = Path(value["runtime"])
        if sha256(source_path) != record["sourceSha256"] or sha256(log_path) != record["logSha256"]:
            raise RuntimeError(f"old sparse cache evidence hash changed: {record['case']}")
        if not runtime.is_file() or sha256(runtime) != value["runtimeSha256"]:
            raise RuntimeError("old sparse cache runtime hash changed")
        log_text = log_path.read_text(encoding="utf-8")
        protocol.check_recording_abort_markers(
            log_text, expected_nonce=record["nonce"], expected_module=MODULE)
        artifacts = protocol.parse_framed_json_lines(
            log_text, marker=materializer.ARTIFACT_MARKER,
            expected_nonce=record["nonce"], label=f"old-{record['case']}")
        aborts = protocol.parse_framed_json_lines(
            log_text, marker=protocol.RECORDING_ABORT_MARKER,
            expected_nonce=record["nonce"], label=f"old-{record['case']}")
        if len(artifacts) != 1 or artifacts[0].get("status") != "success" or aborts:
            raise RuntimeError(f"old control lacks a successful artifact witness: {record['case']}")
        witnessed.append([record["case"], artifacts[0]])
    # Validate the historical wire contract with its own frozen implementation.
    # Importing it into this process would mix its codec with the current one.
    project = Path(value.get("project", str(path.parents[3]))).resolve()
    program = '''
import hashlib,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path.cwd()/"Experiment"))
import boundary_protocol as protocol
import boundary_expr_codec as codec
for case,artifact in json.load(sys.stdin):
    protocol.validate_report(artifact,"sparse-"+case,"Experiment.SparseCacheFixture")
paths=[Path(protocol.__file__),Path(codec.__file__),Path.cwd()/"ExplicitLean/SimpEngine/Boundary.lean"]
print(json.dumps([{ "path":str(p),"sha256":hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths]))
'''
    checked = subprocess.run([sys.executable, "-c", program], cwd=project,
                             input=json.dumps(witnessed), capture_output=True,
                             text=True, check=True, timeout=30)
    value["protocolInputs"] = json.loads(checked.stdout)
    return value


def _run_current(runtime: Path, output: Path) -> list[dict[str, Any]]:
    output.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, Any]] = []
    for case in CASES:
        before = ERASE if case in ("insert-existing", "async-fresh", "async-cached") else "pure ()"
        mutation = {
            "unchanged": "pure ()",
            "erase-existing": ERASE,
            "insert-existing": INSERT,
            "async-fresh": "realizeCache",
            "async-cached": "realizeCache",
        }[case]
        fixture = BASE.replace("__BEFORE__", before).replace("__MUTATION__", mutation)
        fixture = fixture.replace("__WARM__", "warm_cache" if case == "async-cached" else "skip")
        fixture = fixture.replace("__CASE__", case)
        fixture_path = output / case / "Experiment/SparseCacheFixture.lean"
        fixture_path.parent.mkdir(parents=True, exist_ok=True)
        fixture_path.write_text(fixture, encoding="utf-8")
        result, nonce = source.compile_recording_source(str(runtime), fixture_path)
        log_path = fixture_path.with_suffix(".log")
        log_path.write_text(result, encoding="utf-8")
        artifacts = protocol.parse_framed_json_lines(
            result, marker=materializer.ARTIFACT_MARKER, expected_nonce=nonce, label=case)
        aborts = protocol.parse_framed_json_lines(
            result, marker=protocol.RECORDING_ABORT_MARKER, expected_nonce=nonce, label=case)
        if case.startswith("async-") and "SPARSE_ASYNC callerUnchanged=true snapshotPresent=true" not in result:
            raise RuntimeError(f"{case} did not authenticate its async cache witness")
        positive = case in ("unchanged", "async-cached")
        if positive:
            protocol.check_recording_abort_markers(result, expected_nonce=nonce, expected_module=MODULE)
            if len(artifacts) != 1 or artifacts[0]["status"] != "success" or aborts:
                raise RuntimeError(f"positive sparse cache control failed: {case}")
            protocol.validate_report(artifacts[0], f"sparse-{case}", MODULE)
        else:
            expected = "boundary_comparison_local_sparse_cases_cache:"
            if artifacts or len(aborts) != 1 or expected not in aborts[0]["detail"]:
                raise RuntimeError(f"negative sparse cache control was not rejected: {case}")
        records.append({
            "case": case,
            "accepted": positive,
            "source": str(fixture_path.resolve()),
            "sourceSha256": sha256(fixture_path),
            "log": str(log_path.resolve()),
            "logSha256": sha256(log_path),
            "nonce": nonce,
            "aborts": aborts,
        })
    return records


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--runtime", type=Path, default=DEFAULT_RUNTIME)
    parser.add_argument("--old-report", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    runtime = args.runtime.resolve()
    old_report_path = args.old_report.resolve()
    output_root = args.output.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="controls-", dir=output_root))
    if not runtime.is_file():
        raise RuntimeError(f"current runtime is missing: {runtime}")
    old = _load_old_report(old_report_path)
    old_report_hash = sha256(old_report_path)
    inputs = output / "inputs"
    inputs.mkdir(parents=True, exist_ok=True)
    current_boundary = ROOT / "ExplicitLean/SimpEngine/Boundary.lean"
    driver = Path(__file__).resolve()
    archives = {
        "currentRuntime": (runtime, inputs / runtime.name),
        "currentBoundary": (current_boundary, inputs / "Boundary.lean"),
        "driver": (driver, inputs / driver.name),
        "fixtureTemplate": (None, inputs / "SparseCacheFixture.template"),
    }
    for label, (original, archive) in archives.items():
        if label == "fixtureTemplate":
            archive.write_text(BASE, encoding="utf-8")
        else:
            if not original.is_file():
                raise RuntimeError(f"input is missing: {original}")
            shutil.copy2(original, archive)
    before_hashes = {
        label: (hashlib.sha256(BASE.encode("utf-8")).hexdigest() if label == "fixtureTemplate" else sha256(original))
        for label, (original, _) in archives.items()
    }
    archived_runtime = archives["currentRuntime"][1]
    records = _run_current(archived_runtime, output / "current")
    old_by_case = {record["case"]: record for record in old["records"]}
    for record in records:
        if record["sourceSha256"] != old_by_case[record["case"]]["sourceSha256"]:
            raise RuntimeError(f"paired fixture source changed: {record['case']}")
    after_hashes: dict[str, str] = {}
    archive_hashes: dict[str, str] = {}
    for label, (original, archive) in archives.items():
        after_hashes[label] = hashlib.sha256(BASE.encode("utf-8")).hexdigest() if label == "fixtureTemplate" else sha256(original)
        archive_hashes[label] = sha256(archive)
        if after_hashes[label] != before_hashes[label] or archive_hashes[label] != before_hashes[label]:
            raise RuntimeError(f"input changed during sparse cache controls: {label}")
    old_runtime = Path(old["runtime"]).resolve()
    old_runtime_archive = inputs / "old-runtime.dylib"
    shutil.copy2(old_runtime, old_runtime_archive)
    if sha256(old_runtime_archive) != old["runtimeSha256"]:
        raise RuntimeError("old runtime changed while archiving")
    if sha256(old_report_path) != old_report_hash:
        raise RuntimeError("old report changed during validation")
    for index, item in enumerate(old["protocolInputs"]):
        original = Path(item["path"])
        archived = inputs / f"old-protocol-{index}-{original.name}"
        shutil.copy2(original, archived)
        if sha256(original) != item["sha256"] or sha256(archived) != item["sha256"]:
            raise RuntimeError("old protocol input changed during validation")
        item["archivedPath"] = str(archived)
    evidence = {
        "kind": "sparse_cases_cache_guard_paired_controls",
        "status": "passed",
        "cases": list(CASES),
        "old": {
            "report": str(old_report_path),
            "reportSha256": old_report_hash,
            "runtime": old["runtime"],
            "runtimeSha256": old["runtimeSha256"],
            "records": old["records"],
            "protocolInputs": old["protocolInputs"],
        },
        "current": {
            "runtime": str(runtime),
            "archivedRuntime": str(archived_runtime.resolve()),
            "runtimeSha256": before_hashes["currentRuntime"],
            "records": records,
        },
        "expectation": {
            "oldAccepted": list(CASES),
            "currentAccepted": ["unchanged", "async-cached"],
            "currentRejected": ["erase-existing", "insert-existing", "async-fresh"],
        },
        "inputs": {
            "beforeSha256": before_hashes,
            "afterSha256": after_hashes,
            "archiveSha256": archive_hashes,
            "archives": {label: str(archive.resolve()) for label, (_, archive) in archives.items()},
            "oldRuntimeArchive": str(old_runtime_archive.resolve()),
            "oldRuntimeArchiveSha256": sha256(old_runtime_archive),
        },
        "limitation": "This fixture checks sparse cache state equality only; it does not establish general matcher or codec equivalence or claim MatcherCodec-v2 coherence.",
    }
    report_path = output / "report.json"
    report_path.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "report": str(report_path), "runtimeSha256": evidence["current"]["runtimeSha256"]}, sort_keys=True))


if __name__ == "__main__":
    main()
