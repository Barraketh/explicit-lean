#!/usr/bin/env python3
"""Fresh-process captured matcher bundle prototype, with no shared-package writes."""
from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from boundary_expr_codec import validate_matcher_payload

ROOT = Path(__file__).resolve().parents[1]
HEADER = """module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary.MatcherCodec
open Lean Meta Elab
open Lean.Meta.Match ExplicitLean.SimpEngine.Boundary
"""
DEFINITIONS = {
    "nat": """public def MatcherFixture.anchor (n : Nat) : Nat :=
  match n with
  | 0 => 7
  | n + 1 => n
""",
    "prop": """public def MatcherFixture.anchor (p q : Prop) (h : p ∨ q) : True :=
  match h with
  | Or.inl _ => True.intro
  | Or.inr _ => True.intro
""",
    "overlap": """public def MatcherFixture.anchor (n m : Nat) : Nat :=
  match n, m with
  | 0, m => m
  | n, 0 => n
  | n + 1, m + 1 => n + m
""",
    "imported": "",
}
COMMON = """
run_meta do
  let anchor := ``MatcherFixture.anchor.match_1
  let before ← getEnv
  let checkedBefore := before.constants.foldStage2
    (fun names name _ => names.insert name) ({} : NameSet)
  let path ← IO.getEnv "MATCHER_PAYLOAD_PATH"
  let some path := path | throwError "missing payload path"
  let splitterName := mkPrivateName before anchor ++ `splitter
  unless !(before.find? splitterName (skipRealize := true)).isSome do
    throwError "fixture splitter already realized"
"""
CAPTURE = """
  let eqns ← Match.getEquationsFor anchor
  let source ← encodeBoundaryMatcher before checkedBefore anchor eqns
  let badInfo := { eqns.splitterMatchInfo with numParams := eqns.splitterMatchInfo.numParams + 1 }
  let rejected ← try
    discard <| encodeBoundaryMatcher before checkedBefore anchor { eqns with splitterMatchInfo := badInfo }
    pure false
  catch error => pure ((← error.toMessageData.toString).contains "foreign_provenance")
  unless rejected do throwError "capture accepted metadata without typed provenance"
  IO.FS.writeFile path source
  let splitter ← getConstInfo eqns.splitterName
  IO.println s!"CAPTURE splitter={eqns.splitterName} equations={eqns.eqnNames.size} prop={← isProp splitter.type}"
  IO.println "MATCHER_CAPTURE_OK"
"""
REPLAY = """
  let source ← IO.FS.readFile path
  executeBoundaryMatcher anchor source
  let env ← getEnv
  let state := matchEqnsExt.getState env (asyncMode := .async .asyncEnv)
    (asyncDecl := splitterName)
  let some eqns := state.map.find? anchor | throwError "missing replay metadata"
  let recaptured ← encodeBoundaryMatcher before checkedBefore anchor eqns
  unless (← ofExcept <| Json.parse recaptured) == (← ofExcept <| Json.parse source) do
    throwError "replayed bundle differs from captured bundle"
  -- The declaration cache does not preserve caller-local registrations; reset
  -- the branch and force the executor's cached-result validation path too.
  setEnv before
  executeBoundaryMatcher anchor source
  IO.println "MATCHER_REPLAY_OK"
"""
NAT_COMPUTATION = """
  let some (.defnInfo original) := (← getEnv).find? ``MatcherFixture.anchor (skipRealize := true)
    | throwError "missing fixture definition"
  let function := original.value.replace fun expression =>
    match expression with
    | .const name levels => if name == anchor then some (.const splitterName levels) else none
    | _ => none
  let expression := mkApp function (mkNatLit 5)
  checkWithKernel expression
  let result ← evalExpr Nat (mkConst ``Nat) expression
  unless result == 4 do throwError "compiled captured splitter changed computation"
  IO.println "MATCHER_COMPUTATION_OK"
"""


def compile_source(work: Path, case: str, phase: str, text: str, payload: Path,
                   expected: str | None = None) -> dict:
    phase_root = work / case / phase
    path = phase_root / "Experiment" / "MatcherFixture.lean"
    path.parent.mkdir(parents=True)
    path.write_text(text)
    env = os.environ.copy()
    env["MATCHER_PAYLOAD_PATH"] = str(payload)
    result = subprocess.run(["lake", "env", "lean", "-R", str(phase_root), str(path)],
                            cwd=ROOT, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, timeout=120, check=False)
    log = path.with_suffix(".log")
    log.write_text(result.stdout)
    record = {"case": case, "phase": phase, "exitCode": result.returncode,
              "source": str(path), "sourceSha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "log": str(log), "logSha256": hashlib.sha256(log.read_bytes()).hexdigest(),
              "payload": str(payload),
              "payloadSha256": hashlib.sha256(payload.read_bytes()).hexdigest() if payload.exists() else None}
    if expected is None:
        if result.returncode or f"MATCHER_{phase.upper()}_OK" not in result.stdout:
            raise RuntimeError(f"{case}/{phase} failed:\n{result.stdout}")
    elif result.returncode == 0 or expected not in result.stdout:
        raise RuntimeError(f"{case}/{phase} did not reject with {expected!r}:\n{result.stdout}")
    print(f"matcher codec: {case}/{phase}: ok", flush=True)
    return record


def main() -> None:
    parent = ROOT / ".lake" / "matcher-codec"
    parent.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="fixture-", dir=parent))
    print(f"matcher codec evidence: {work}", flush=True)
    records = []
    payloads = {}
    for case, definition in DEFINITIONS.items():
        payload = work / case / "payload.json"
        common = HEADER + definition + COMMON
        if case == "imported":
            common = common.replace("import Lean\n", "import Lean\nimport Mathlib.Data.Nat.Init\n")
            common = common.replace("``MatcherFixture.anchor.match_1", "``Nat.leRec.match_1")
        records.append(compile_source(work, case, "capture", common + CAPTURE, payload))
        replay = common + REPLAY + (NAT_COMPUTATION if case == "nat" else "")
        records.append(compile_source(work, case, "replay", replay, payload))
        captured = json.loads(payload.read_text())
        validate_matcher_payload(payload.read_text(), captured[1], case)
        payloads[case] = {"path": str(payload),
                          "sha256": hashlib.sha256(payload.read_bytes()).hexdigest()}

    uncompiled = HEADER + "set_option bootstrap.genMatcherCode false\n" + DEFINITIONS["overlap"] + COMMON + CAPTURE
    records.append(compile_source(work, "uncompiled", "capture", uncompiled,
        work / "uncompiled" / "payload.json", "boundary_matcher_uncompiled_splitter_unsupported"))

    original = json.loads((work / "nat" / "payload.json").read_text())

    def negative(label, mutate, detail, *, cached=False, reserved=False):
        data = copy.deepcopy(original)
        mutate(data)
        path = work / "nat" / f"{label}.json"
        path.write_text(json.dumps(data, separators=(",", ":")))
        if label in {"missing-equation", "reordered-equations", "fresh-splitter-info",
                     "fresh-theorem-group", "invalid-discriminants", "duplicate-overlap",
                     "missing-map", "missing-equation-set", "invalid-dag", "unsafe-definition"}:
            try:
                validate_matcher_payload(path.read_text(), original[1], label)
            except RuntimeError:
                pass
            else:
                raise RuntimeError(f"Python accepted invalid matcher payload: {label}")
        body = ""
        if cached:
            original_path = json.dumps(str(work / "nat" / "payload.json"))
            body = f"  let good ← IO.FS.readFile {original_path}\n  executeBoundaryMatcher anchor good\n  setEnv before\n"
        body += "  let source ← IO.FS.readFile path\n"
        if reserved:
            body += """  unless isReservedName (← getEnv) `Nat.add.congr_simp &&
      !(← getEnv).containsOnBranch `Nat.add.congr_simp do
    throwError "reserved negative control is not fresh"
  try
    executeBoundaryMatcher anchor source
  catch error =>
    unless !(← getEnv).containsOnBranch `Nat.add.congr_simp do
      throwError "replay invoked a reserved-name generator"
    throw error
"""
        else:
            body += "  executeBoundaryMatcher anchor source\n"
        records.append(compile_source(work, "nat", label,
            HEADER + DEFINITIONS["nat"] + COMMON + body, path, detail))

    negative("missing-equation", lambda p: p[7].pop(), "boundary_matcher_equation_order")
    negative("fresh-splitter-info", lambda p: p.__setitem__(6, copy.deepcopy(p[3][2])),
             "boundary_matcher_unexpected_splitter_info")
    def non_singleton_theorem(p):
        theorem = json.loads(p[7][0][1])
        theorem[2] = []
        p[7][0][1] = json.dumps(theorem, separators=(",", ":"))
    negative("fresh-theorem-group", non_singleton_theorem, "boundary_matcher_theorem_group")
    negative("reordered-equations", lambda p: p[7].reverse(), "boundary_matcher_equation_order")
    negative("invalid-discriminants", lambda p: p[3][2].__setitem__(1, 99), "discriminant count mismatch")
    negative("duplicate-overlap", lambda p: p[3][2].__setitem__(5, [[0, [1]], [0, [1]]]), "duplicate overlap key")
    negative("missing-map", lambda p: p[9][0].clear(), "boundary_matcher_state_conflict:payload-transition")
    negative("missing-equation-set", lambda p: p[9][1].clear(), "boundary_matcher_state_conflict:payload-transition")

    def bad_proof(p):
        theorem = json.loads(p[7][0][1])
        theorem[5] = theorem[4]
        p[7][0][1] = json.dumps(theorem, separators=(",", ":"))
    negative("invalid-proof", bad_proof, "boundary_theorem_value_type_mismatch")

    def bad_definition(p):
        definition = json.loads(p[4])
        definition[7] = definition[6]
        p[4] = json.dumps(definition, separators=(",", ":"))
    negative("invalid-definition", bad_definition, "boundary_definition_value_type_mismatch")

    def invalid_dag(p):
        definition = json.loads(p[4])
        definition[7] = "[]"
        p[4] = json.dumps(definition, separators=(",", ":"))
    negative("invalid-dag", invalid_dag, "boundary_expr_decode_error")

    def unsafe_definition(p):
        definition = json.loads(p[4])
        definition[5] = "unsafe"
        p[4] = json.dumps(definition, separators=(",", ":"))
    negative("unsafe-definition", unsafe_definition, "invalid safe singleton definition payload")

    def recursive_definition(p):
        definition = json.loads(p[4])
        definition[7] = json.dumps(["expr_dag_v1", [["c", definition[1],
            [["p", level] for level in definition[3]]]], 0], separators=(",", ":"))
        p[4] = json.dumps(definition, separators=(",", ":"))
    negative("cached-recursion", recursive_definition, "boundary_definition_recursive_reference", cached=True)

    def reserved_reference(p):
        definition = json.loads(p[4])
        name = [["s", "Nat"], ["s", "add"], ["s", "congr_simp"]]
        definition[7] = json.dumps(["expr_dag_v1", [["c", name, []]], 0], separators=(",", ":"))
        p[4] = json.dumps(definition, separators=(",", ":"))
    negative("reserved-reference", reserved_reference,
             "expression constant is unavailable without generation: Nat.add.congr_simp", reserved=True)
    negative("uncompiled-inline", lambda p: p.__setitem__(5, None),
             "boundary_matcher_uncompiled_splitter_unsupported")
    negative("cached-tag", lambda p: p[7][0].__setitem__(2, not p[7][0][2]),
             "boundary_matcher_equation_tag_conflict", cached=True)

    def changed_alt_info(p):
        p[3][2][2][0][0] += 1
        for key, value in p[9][0]:
            if key == p[1]:
                value[2][2][0][0] += 1
    negative("cached-alternative-metadata", changed_alt_info,
             "boundary_matcher_state_conflict:realized-member", cached=True)
    negative("cached-async-map", lambda p: p[9][1].append([["s", "foreign"]]),
             "boundary_matcher_state_conflict:payload-transition", cached=True)

    implementation = {}
    for path in [Path(__file__).resolve(), ROOT / "ExplicitLean/SimpEngine/Boundary/MatcherCodec.lean",
                 ROOT / "ExplicitLean/SimpEngine/Boundary/DeclarationCodec.lean"]:
        implementation[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    (work / "report.json").write_text(json.dumps({"kind": "isolated_matcher_codec_prototype",
        "baseCommit": "6287642b0567867cc14ad026da5467badfa9b329", "implementation": implementation,
        "payloads": payloads, "records": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
