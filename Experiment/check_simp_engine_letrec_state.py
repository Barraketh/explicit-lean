#!/usr/bin/env python3
"""Preexisting pending recursion stays exact; new/changed entries fail closed."""
from pathlib import Path
import argparse
import hashlib
import json
import tempfile
import subprocess
import shutil

import boundary_protocol as protocol
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.LetRecStateFixture"
CALL = 'simp_engine_boundary_record "existing-letrec" only [letrec_rule]'
TEMPLATE = r'''module
public import Lean
public meta import ExplicitLean.SimpEngine.Boundary
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

elab "letrec_rule" : term => do
  let entries := (← getThe Term.State).letRecsToLift
  unless entries.length == 1 do throwError "expected one preexisting pending function"
  MUTATION
  Term.elabTerm (mkIdent `hpq) none

elab "inspect_letrec" : tactic => do
  let entries := (← getThe Term.State).letRecsToLift
  unless entries.length == 1 do throwError "missing pending recursion"
  IO.println "LETREC_CONTINUATION onePending=true"

@[expose] public def sample (p q : Prop) (h : p) (hpq : p → q) (n : Nat) : Nat :=
  loop n
where
  loop : Nat → Nat
  | 0 => by
    have : q := by
      first
      | CALL
      | exact hpq h
    inspect_letrec
    exact 0
  | n + 1 => loop n + 1

example : sample True True True.intro (fun h => h) 5 = 5 := rfl
'''

UNIT = r'''module
public import Lean
public meta import ExplicitLean.SimpEngine.Boundary.LetRecState
open Lean Meta Elab ExplicitLean.SimpEngine.Boundary
run_meta do
  let fv : FVarId := ⟨`pending⟩
  let mv : MVarId := ⟨`pendingRoot⟩
  let nat := mkConst ``Nat
  let atom := Syntax.atom .none "same"
  let relocated := Syntax.atom (.synthetic ⟨1⟩ ⟨2⟩ false) "same"
  let lctx := ({} : LocalContext).mkLocalDecl fv `loop nat .default .auxDecl
  let base : Term.LetRecToLift := {
    ref := atom, fvarId := fv, attrs := #[], shortDeclName := `loop,
    declName := `sample.loop, parentName? := some `sample, lctx,
    localInstances := #[{className := `Nat, fvar := mkFVar fv}],
    type := ← mkArrow nat nat, val := .lam `x nat (.bvar 0) .default,
    mvarId := mv, termination := .none }
  let mutations : Array (String × Term.LetRecToLift) := #[
    ("source-info", {base with ref := relocated}),
    ("fvar", {base with fvarId := ⟨`other⟩}),
    ("attributes", {base with attrs := #[{name := `inline}]}),
    ("short-name", {base with shortDeclName := `other}),
    ("decl-name", {base with declName := `sample.other}),
    ("parent", {base with parentName? := none}),
    ("context-hole", {base with lctx := {lctx with decls := lctx.decls.push none}}),
    ("context-map", {base with lctx := {lctx with fvarIdToDecl := {}}}),
    ("context-aux-map", {base with lctx := {lctx with auxDeclToFullName := lctx.auxDeclToFullName.insert fv `foreign}}),
    ("instance-class", {base with localInstances := #[{className := `Bool, fvar := mkFVar fv}]}),
    ("type", {base with type := nat}),
    ("value", {base with val := .lam `x nat (mkNatLit 1) .default}),
    ("binder-name", {base with val := .lam `different nat (.bvar 0) .default}),
    ("binder-annotation", {base with val := .lam `x nat (.bvar 0) .implicit}),
    ("mvar", {base with mvarId := ⟨`different⟩}),
    ("termination-extra", {base with termination := {base.termination with extraParams := 1}}),
    ("termination-ref", {base with termination := {base.termination with ref := atom}}),
    ("termination-syntax", {base with termination := {base.termination with terminationBy?? := some atom}}),
    ("termination-by", {base with termination := {base.termination with terminationBy? := some {
      ref := atom, structural := false, vars := #[], body := ⟨atom⟩}}}),
    ("partial-fixpoint", {base with termination := {base.termination with partialFixpoint? := some {
      ref := atom, term? := none}}}),
    ("decreasing-by", {base with termination := {base.termination with decreasingBy? := some {
      ref := atom, tactic := ⟨atom⟩}}}),
    ("binders", {base with binders := atom}),
    ("docstring", {base with docString? := some (⟨atom⟩, true)})]
  unless boundaryExistingLetRecsEq [base] [base] do throwError "unchanged list rejected"
  for (label, changed) in mutations do
    if boundaryExistingLetRecsEq [base] [changed] then throwError "mutation accepted: {label}"
  if boundaryExistingLetRecsEq [base] [] then throwError "deletion accepted"
  if boundaryExistingLetRecsEq [base] [base,base] then throwError "new entry accepted"
  let other := {base with declName := `sample.other}
  if boundaryExistingLetRecsEq [base,other] [other,base] then throwError "reorder accepted"
  IO.println "LETREC_UNIT 26mutations=true binderAnnotations=true sourceInfo=true instanceClasses=true"
  IO.println "LETREC_CONTINUATION onePending=true"
'''

ROUTING_UNIT = r'''module
public import Lean
public meta import Lean.Elab.RecAppSyntax
public meta import ExplicitLean.SimpEngine.Boundary.Selector
open Lean Meta Elab ExplicitLean.SimpEngine.Boundary
run_meta do
  let nat := mkConst ``Nat
  let fnType ← mkArrow nat nat
  let root ← mkFreshExprMVar (mkConst ``True)
  let fn ← mkFreshExprMVar fnType
  let fv ← mkFreshFVarId
  let lctx := ({} : LocalContext).mkLocalDecl fv `loop fnType .default .auxDecl
  let recCall (offset : Nat) : Expr :=
    mkRecAppWithSyntax (mkApp (mkFVar fv) (.bvar 0))
      (.atom (.synthetic ⟨offset⟩ ⟨offset + 1⟩ false) "loop n")
  let body (left right : Nat) : Expr :=
    .lam `n nat (mkApp2 (mkConst ``Nat.add) (recCall left) (recCall right)) .default
  let base : Term.LetRecToLift := {
    ref := .missing, fvarId := fv, attrs := #[], shortDeclName := `loop,
    declName := `sample.loop, parentName? := some `sample, lctx,
    localInstances := #[{className := `Nat, fvar := mkFVar fv}],
    type := fnType, val := body 10 20, mvarId := fn.mvarId!, termination := .none }
  let observe (entry : Term.LetRecToLift) :=
    boundaryProofStateFingerprintWithTerm [root.mvarId!] {letRecsToLift := [entry]}
  let expected ← observe base
  unless (← observe {base with val := body 100 900}) == expected do
    throwError "monotone source relocation changed routing"
  let mutations : Array (String × Term.LetRecToLift) := #[
    ("source-order", {base with val := body 20 10}),
    ("source-sharing", {base with val := body 10 10}),
    ("body", {base with val := .lam `n nat (mkNatLit 4) .default}),
    ("termination", {base with termination := {base.termination with extraParams := 1}}),
    ("instance-class", {base with localInstances := #[{className := `Bool, fvar := mkFVar fv}]}),
    ("other-metadata", {base with val := mkMData (KVMap.empty.setNat `userSemanticField 7) (body 10 20)})]
  for (label, changed) in mutations do
    if (← observe changed) == expected then throwError "routing mutation ignored: {label}"
  let stx := Syntax.atom (.synthetic ⟨10⟩ ⟨11⟩ false) "loop n"
  let canonical := KVMap.empty.setSyntax `_recApp stx |>.setNat `_recAppPos 10
  let malformed := #[
    canonical.setNat `_recAppPos 11,
    canonical.setString `_recAppPos "10",
    canonical.erase `_recAppPos,
    canonical.erase `_recApp,
    {canonical with entries := canonical.entries ++ [(`_recAppPos, .ofNat 10)]}]
  for data in malformed do
    let rejected ← try
      discard <| observe {base with val := mkMData data (body 10 20)}
      pure false
    catch error =>
      unless (← error.toMessageData.toString).contains "boundary_selector_invalid_rec_app_metadata" do throw error
      pure true
    unless rejected do throwError "malformed recursive-call metadata accepted"
  IO.println "LETREC_ROUTING relocation=true sixMutations=true fiveMalformed=true"
  IO.println "LETREC_CONTINUATION onePending=true"
'''

EMPTY_UNIT = r'''module
public import Lean
public meta import Lean.Elab.RecAppSyntax
public meta import ExplicitLean.SimpEngine.Boundary.Selector
open Lean Meta Elab ExplicitLean.SimpEngine.Boundary
run_meta do
  let goalAt (offset : Nat) := mkFreshExprMVar (mkRecAppWithSyntax (mkConst ``True)
    (.atom (.synthetic ⟨offset⟩ ⟨offset + 1⟩ false) "same"))
  let first ← goalAt 10
  let second ← goalAt 20
  let a ← boundaryProofStateFingerprintWithTerm [] {pendingMVars := [first.mvarId!]}
  let b ← boundaryProofStateFingerprintWithTerm [] {pendingMVars := [second.mvarId!]}
  if a == b then throwError "empty-letrec routing unexpectedly quotiented source offsets"
  IO.println ("EMPTY_LETREC_BYTES " ++ (toJson #[a,b]).compress)
  IO.println "LETREC_CONTINUATION onePending=true"
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-runtime", type=Path)
    args = parser.parse_args()
    diagnostics = ROOT / ".lake/letrec-diagnostics"
    diagnostics.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="controls-", dir=diagnostics))
    print(work, flush=True)
    dylib = source.query_json_string(source.run(["lake", "query", "ExplicitLean:shared", "--json"]), "shared")
    def immutable_inputs():
        paths = [Path(__file__).resolve(), ROOT / "lean-toolchain", Path(dylib).resolve(),
                 ROOT / "ExplicitLean/SimpEngine/Boundary.lean",
                 ROOT / "Experiment/boundary_protocol.py",
                 ROOT / "Experiment/check_simp_engine_boundary_source.py"]
        paths += sorted((ROOT / "ExplicitLean/SimpEngine/Boundary").glob("*.lean"))
        paths += sorted((ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine").rglob("*.olean*"))
        paths += sorted((ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine").rglob("*.ir"))
        if args.baseline_runtime:
            paths.append(args.baseline_runtime.resolve() / ".lake/build/lib/libexplicitLean_ExplicitLean.dylib")
        return [{"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                for path in paths]
    inputs = immutable_inputs()
    archived_inputs = []
    for index, item in enumerate(inputs):
        path = Path(item["path"])
        destination = work / "inputs" / f"{index}-{path.name}"
        destination.parent.mkdir(exist_ok=True)
        shutil.copy2(path, destination)
        assert hashlib.sha256(destination.read_bytes()).hexdigest() == item["sha256"]
        archived_inputs.append({**item, "archivedPath": str(destination)})
    archived_runtime = next(item["archivedPath"] for item in archived_inputs
                            if item["path"] == str(Path(dylib).resolve()))
    records = []
    def compile_case(label, text, *, recording=False, abort=None, runtime=None):
        path = work / label / "Experiment/LetRecStateFixture.lean"
        path.parent.mkdir(parents=True)
        path.write_text(text)
        env, nonce = protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment()
        try:
            if runtime is None:
                output = source.compile_source(archived_runtime, path, env=env)
            else:
                result = subprocess.run(["lake", "env", "lean",
                    f"--load-dynlib={runtime}/.lake/build/lib/libexplicitLean_ExplicitLean.dylib",
                    "-R", str(path.parent.parent), str(path)], cwd=runtime, env=env,
                    capture_output=True, text=True, timeout=120)
                output = result.stdout + result.stderr
                if result.returncode: raise RuntimeError(output)
        except RuntimeError as error:
            path.with_suffix(".log").write_text(str(error))
            raise
        log = path.with_suffix(".log"); log.write_text(output)
        records.append({"label":label, "nonce":nonce, "source":str(path),
            "sourceSha256":hashlib.sha256(path.read_bytes()).hexdigest(), "log":str(log),
            "logSha256":hashlib.sha256(log.read_bytes()).hexdigest(), "compilerExit":0,
            "recording":recording, "expectedAbort":abort,
            "runtime":str(runtime or ROOT)})
        check = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        try:
            check(output, expected_nonce=nonce)
        except RuntimeError as error:
            if abort is None or abort not in str(error): raise
        else:
            if abort: raise RuntimeError("caught pending-recursion mutation was accepted")
        assert "LETREC_CONTINUATION onePending=true" in output
        reports = protocol.parse_framed_json_lines(output, marker=source.ARTIFACT_MARKER,
            expected_nonce=nonce, label="letrec artifact")
        if abort: assert not reports
        print(label + ": passed", flush=True)
        return reports, output
    compile_case("unit", UNIT)
    compile_case("routing-unit", ROUTING_UNIT)
    _, empty_output = compile_case("empty-letrec-current", EMPTY_UNIT)
    if args.baseline_runtime:
        _, baseline_output = compile_case("empty-letrec-baseline", EMPTY_UNIT,
                                         runtime=args.baseline_runtime.resolve())
        def empty_bytes(output):
            return [line for line in output.splitlines() if line.startswith("EMPTY_LETREC_BYTES ")]
        assert len(empty_bytes(empty_output)) == 1
        assert empty_bytes(empty_output) == empty_bytes(baseline_output)
    text = TEMPLATE.replace("MUTATION", "pure ()").replace("CALL", CALL)
    compile_case("original", text.replace(CALL, "simp only [letrec_rule]"))
    reports, _ = compile_case("record", text, recording=True)
    assert len(reports) == 1
    protocol.validate_report(reports[0], "existing-letrec", MODULE)
    replacement = source.preserve_original_call(source.format_report_variants(reports, "          "),
                                               "simp only [letrec_rule]", "          ")
    applied = text.replace("public meta import ExplicitLean.SimpEngine.Boundary\n",
                           "public meta import ExplicitLean.SimpEngine.Boundary.Tactic\n")
    compile_case("replay", applied.replace(CALL, replacement))
    mutations = {
        "delete": "modifyThe Term.State fun s => {s with letRecsToLift := []}",
        "body": "modifyThe Term.State fun s => {s with letRecsToLift := entries.map fun e => {e with val := .lam `n (mkConst ``Nat) (mkNatLit 123) .default}}",
        "duplicate-fresh": "modifyThe Term.State fun s => {s with letRecsToLift := {entries.head! with declName := entries.head!.declName.str \"fresh\"} :: entries}",
    }
    # Pinned simp deliberately restores Term.State after argument elaboration.
    # These are positive isolation checks; they are not observable stock deltas.
    for label, mutation in mutations.items():
        transient, _ = compile_case("transient-" + label,
            TEMPLATE.replace("MUTATION", mutation).replace("CALL", CALL), recording=True)
        assert len(transient) == 1
    consumer = text.replace(CALL, "simp only [letrec_rule]")
    consumer = consumer.replace("  | 0 => by\n", "  | 0 => by\n    have : True := by\n      simp_engine_boundary_comparator_self_test\n      exact True.intro\n")
    _, consumer_output = compile_case("full-comparator-negatives", consumer)
    assert "LETREC_COMPARATOR_CONTROLS deleted=true body=true fresh=true commonPreRequired=true" in consumer_output
    if immutable_inputs() != inputs:
        raise RuntimeError("letRec control inputs changed during validation")
    report = {"kind":"preexisting_letrec_controls", "status":"passed",
              "acceptedCampaignCoverage":False, "records":records,
              "typedFieldMutationCount":26, "routingSemanticMutationCount":6,
              "routingMalformedMutationCount":5, "fullComparatorMutationCount":3,
              "emptyLetRecBaselineCompared":args.baseline_runtime is not None,
              "immutableInputs":archived_inputs}
    (work / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(work / "report.json", flush=True)

if __name__ == "__main__": main()
