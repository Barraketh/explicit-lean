#!/usr/bin/env python3
"""Run the closed-v1 and reachable-universe-reference codec regressions.

This is a local regression driver, not campaign acceptance.  Each Lean case
gets a disposable source and durable log under ``.lake``.  The report records
immutable implementation inputs and source/log hashes; it does not use a
mutable runtime library as acceptance identity.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import tempfile

from boundary_expr_codec import validate_boundary_expr_dag, validate_expr_dag
from process_runner import run_process


ROOT = Path(__file__).resolve().parents[1]
OUT_ROOT = ROOT / ".lake" / "level-reference-diagnostics"
LEAN = Path("/Users/ptsier/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean")


HEADER = """module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary.ExprCodec
public meta import ExplicitLean.SimpEngine.Boundary.Selector
open Lean Meta Elab ExplicitLean.SimpEngine.Boundary
run_meta do
  __NOISE__
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  withLocalDeclD `α (mkSort u) fun _ =>
    withLocalDeclD `β (mkSort v) fun _ => do
      let goal ← mkFreshExprMVar (mkConst ``True)
      let references ← boundaryUniverseReferences [goal.mvarId!] {}
      unless references == #[u.mvarId!, v.mvarId!] do
        throwError "reachable order differs"
      let expression := mkSort (.max u (.succ v))
      __BODY__
"""


def _hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _payload(output: str) -> str:
    for line in output.splitlines():
        if line.startswith("[\"expr_dag_v2\""):
            return line
    raise RuntimeError("codec case did not print an expr_dag_v2 payload")


def _immutable_inputs() -> dict[str, object]:
    source_paths = [
        ROOT / "ExplicitLean/SimpEngine/Boundary/ExprCodec.lean",
        ROOT / "ExplicitLean/SimpEngine/Boundary/Selector.lean",
    ]
    build_paths = [
        ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/ExprCodec.olean",
        ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/ExprCodec.ir",
        ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/Selector.olean",
        ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/Selector.ir",
    ]
    for stem in ("ExprCodec", "Selector"):
        for suffix in (".olean.private", ".olean.server"):
            path = ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary" / (stem + suffix)
            if path.is_file():
                build_paths.append(path)
    toolchain = ROOT / "lean-toolchain"
    paths = source_paths + build_paths + [toolchain, LEAN]
    missing = [str(path) for path in paths if not path.is_file()]
    if missing:
        raise RuntimeError(f"immutable codec inputs missing: {missing}")
    version = run_process(
        [str(LEAN), "--version"], cwd=ROOT, text=True, capture_output=True, timeout=10
    )
    if version.returncode != 0:
        raise RuntimeError(f"pinned Lean version query failed: {version.stderr}")
    return {
        "leanBinary": {"path": str(LEAN), "sha256": _hash(LEAN)},
        "leanVersion": (version.stdout or "").strip(),
        "toolchain": {"path": str(toolchain), "sha256": _hash(toolchain)},
        "sources": [{"path": str(path), "sha256": _hash(path)} for path in source_paths],
        "buildArtifacts": [
            {"path": str(path), "sha256": _hash(path)} for path in build_paths
        ],
    }


def _run_case(work: Path, name: str, body: str, expected: str | None = None,
              noise: str = "pure ()") -> dict[str, object]:
    source = work / f"{name}.lean"
    source.write_text(
        HEADER.replace("__NOISE__", noise).replace("__BODY__", body.replace("\n", "\n      "))
    )
    result = run_process(
        ["lake", "env", "lean", str(source)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=90,
    )
    output = (result.stdout or "") + (result.stderr or "")
    log = source.with_suffix(".log")
    log.write_text(output)
    if expected is None:
        if result.returncode != 0 or "LEVEL_REFERENCE_OK" not in output:
            raise RuntimeError(f"{name} failed; see {log}:\n{output}")
    elif result.returncode == 0 or expected not in output:
        raise RuntimeError(f"{name} had unexpected result; see {log}:\n{output}")
    return {
        "case": name,
        "expected": expected,
        "exitCode": result.returncode,
        "source": str(source),
        "sourceSha256": _hash(source),
        "log": str(log),
        "logSha256": _hash(log),
    }


def main() -> None:
    OUT_ROOT.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="codec-", dir=OUT_ROOT))
    immutable_inputs = _immutable_inputs()
    records: list[dict[str, object]] = []
    roundtrip = """let payload ← encodeBoundaryExprWithUniverses expression references
let before ← getMCtx
let decoded ← decodeBoundaryExprWithUniverses payload references
unless decoded == expression do throwError "roundtrip differs"
let after ← getMCtx
unless before.lAssignment.toList == after.lAssignment.toList &&
    (before.lDecls.toList.map fun (id, d) => (id, d.index, d.depth)) ==
      (after.lDecls.toList.map fun (id, d) => (id, d.index, d.depth)) do
  throwError "decoder changed universe context"
IO.println payload
IO.println "LEVEL_REFERENCE_OK"
"""
    first = _run_case(work, "roundtrip", roundtrip)
    records.append(first)
    noisy = _run_case(
        work, "unreachable-allocation-noise", roundtrip,
        noise="for _ in [:17] do discard <| mkFreshLevelMVar",
    )
    records.append(noisy)
    if _payload(Path(first["log"]).read_text()) != _payload(Path(noisy["log"]).read_text()):
        raise RuntimeError("unreachable level allocation changed the wire payload")

    records.extend([
        _run_case(work, "fresh-unreachable",
                  "let fresh ← mkFreshLevelMVar\ndiscard <| encodeBoundaryExprWithUniverses (mkSort fresh) references",
                  "boundary_expr_unresolved_universe"),
        _run_case(work, "duplicate-table",
                  "discard <| encodeBoundaryExprWithUniverses expression #[u.mvarId!, u.mvarId!]",
                  "boundary_expr_duplicate_reference_universe"),
        _run_case(work, "unknown-table",
                  "discard <| encodeBoundaryExprWithUniverses expression #[⟨`missing⟩]",
                  "boundary_expr_unknown_reference_universe"),
        _run_case(work, "count-mismatch",
                  "let payload ← encodeBoundaryExprWithUniverses expression references\ndiscard <| decodeBoundaryExprWithUniverses payload #[u.mvarId!]",
                  "boundary universe reference count mismatch"),
        _run_case(work, "v1-reader-rejects-v2",
                  "let payload ← encodeBoundaryExprWithUniverses expression references\ndiscard <| decodeBoundaryExpr payload",
                  "invalid expression encoding"),
        _run_case(work, "v1-encoder-rejects-open",
                  "discard <| encodeBoundaryExpr expression",
                  "boundary_expr_unresolved_universe"),
    ])
    raw = _payload(Path(first["log"]).read_text())
    mutation = json.loads(raw)
    mutation[2][0][1] = ["r", 2]
    records.append(_run_case(
        work, "out-of-range-reference",
        "discard <| decodeBoundaryExprWithUniverses "
        + json.dumps(json.dumps(mutation, separators=(",", ":")))
        + " references",
        "unknown boundary universe reference",
    ))
    validate_boundary_expr_dag(raw)
    # Keep these Python-only structural negatives alongside the Lean decoder
    # controls.  They ensure malformed count/reference fields fail before any
    # subprocess or kernel path is involved.
    python_negative_cases = [
        ("count-bool", lambda value: value.__setitem__(1, True)),
        ("count-negative", lambda value: value.__setitem__(1, -1)),
        ("ref-bool", lambda value: value[2][0].__setitem__(1, ["r", True])),
        ("ref-negative", lambda value: value[2][0].__setitem__(1, ["r", -1])),
        ("ref-out-of-range", lambda value: value[2][0].__setitem__(1, ["r", 2])),
    ]
    for name, mutate in python_negative_cases:
        value = json.loads(raw)
        mutate(value)
        try:
            validate_boundary_expr_dag(json.dumps(value, separators=(",", ":")))
        except RuntimeError:
            continue
        raise RuntimeError(f"Python validator accepted malformed v2 case: {name}")
    try:
        validate_expr_dag(raw)
    except RuntimeError:
        pass
    else:
        raise RuntimeError("closed v1 Python validator accepted a v2 payload")
    if _immutable_inputs() != immutable_inputs:
        raise RuntimeError("codec inputs changed during the regression run")
    # Retain the tested bytes when a later project build replaces these files.
    inputs = [immutable_inputs["leanBinary"], immutable_inputs["toolchain"],
              *immutable_inputs["sources"], *immutable_inputs["buildArtifacts"]]
    for index, entry in enumerate(inputs):
        path = Path(entry["path"])
        archived = work / "inputs" / f"{index}-{path.name}"
        archived.parent.mkdir(exist_ok=True)
        shutil.copy2(path, archived)
        if _hash(archived) != entry["sha256"]:
            raise RuntimeError(f"codec input changed while archiving: {path}")
        entry["archivedPath"] = str(archived)
    report = {
        "status": "passed",
        "acceptance": "codec-regression-only",
        "records": records,
        "wireSha256": hashlib.sha256(raw.encode()).hexdigest(),
        "pythonNegativeCases": [name for name, _ in python_negative_cases]
        + ["v1-reader-rejects-v2"],
        "negativeCaseCount": 6,
        "runtimeHashRecorded": False,
        "runtimeHashAffectsAcceptance": False,
        "immutableInputs": immutable_inputs,
    }
    report_path = work / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"universe reference codec: {len(records)} cases passed")
    print(f"report={report_path}")


if __name__ == "__main__":
    main()
