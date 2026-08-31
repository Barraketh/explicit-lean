#!/usr/bin/env python3
"""Focused cached-only local realization controls; no builds or package writes.

Fresh local production and nonempty auxiliary-proof member caches intentionally
remain unsupported. This fixture does not certify complete source modules.
"""
from __future__ import annotations
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
from process_runner import run_process
import tempfile

import boundary_protocol as protocol
from boundary_expr_codec import validate_realization_payload
import check_simp_engine_boundary_source as source

ROOT = Path(__file__).resolve().parents[1]

CONTROLS = r'''
meta section
open Lean Meta Elab Command ExplicitLean.SimpEngine.Boundary
private unsafe def changedEnv (env : Environment) (owner key : Name) (mode : String) : IO Environment := do
  let some ctx := env.localRealizationCtxMap.find? owner | throw <| IO.userError "fixture no context"
  if mode == "disabled" then return { env with localRealizationCtxMap := env.localRealizationCtxMap.erase owner }
  if mode == "changed-owner" || mode == "changed-owner-consistent" then
    let checked := env.checked.get
    let some (.defnInfo info) := checked.find? owner | throw <| IO.userError "fixture owner kind"
    let changed := ConstantInfo.defnInfo { info with value := .mdata (KVMap.empty.setNat `changed 1) info.value }
    let checked := { checked with constants := checked.constants.insert owner changed }
    if mode == "changed-owner" then return { env with checked := .pure checked }
    let rewrite := fun branch : AsyncConsts => Id.run do
      let some old := branch.map.find? owner | return branch
      let member := { old with constInfo := AsyncConstantInfo.ofConstantInfo changed }
      return { branch with
        revList := branch.revList.map fun old => if old.constInfo.name == owner then member else old
        map := branch.map.insert owner member
        normalizedTrie := branch.normalizedTrie.insert (privateToUserName owner) member }
    return { env with
      checked := .pure checked
      asyncConstsMap := { «private» := rewrite env.asyncConstsMap.private, «public» := rewrite env.asyncConstsMap.public } }
  let mut changed := ctx
  if mode == "saved-options" then changed := { ctx with opts := ctx.opts.setBool `Elab.async false }
  if mode == "saved-environment" then
    let empty ← mkEmptyEnvironment
    changed := { ctx with env := unsafeCast empty }
  let mut map ← ctx.realizeMapRef.get
  let some raw := map.find? (TypeName.typeName Environment.RealizeConstKey) | throw <| IO.userError "fixture no map"
  let entries := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
  let cacheKey : Environment.RealizeConstKey := { constName := key }
  let some task := entries.find? cacheKey | throw <| IO.userError "fixture no task"
  let some result := task.get.get? Environment.RealizeConstResult | throw <| IO.userError "fixture wrong result"
  let entries ← if mode == "missing" then pure (entries.erase cacheKey)
    else if mode == "wrong-type" then pure (entries.insert cacheKey (.pure (.mk (default : AsyncConsts))))
    else if mode == "pending" then do
      let promise ← IO.Promise.new
      map := map.insert `holdPendingFixture (unsafeCast promise)
      pure (entries.insert cacheKey promise.result!)
    else if mode == "signature" || mode == "nested-map" || mode == "nested-body" || mode == "nested-cardinality" then do
      let [member] := result.newConsts.private | throw <| IO.userError "fixture root count"
      let member ← if mode == "signature" then pure { member with
          constInfo := { member.constInfo with sig := .pure { member.constInfo.sig.get with type := mkConst ``True } } }
        else do
          let some nested := member.aconstsImpl.get.get? AsyncConsts | throw <| IO.userError "fixture children type"
          let nested ← if mode == "nested-cardinality" then pure { nested with size := nested.size + 1 }
            else do
              let some child := nested.revList.head? | throw <| IO.userError "fixture no child"
              let changedChild := { child with isRealized := !child.isRealized }
              if mode == "nested-map" then pure { nested with map := nested.map.insert child.constInfo.name changedChild }
              else
                let .defnInfo info := child.constInfo.constInfo.get | throw <| IO.userError "fixture child kind"
                let ci := ConstantInfo.defnInfo { info with value := .mdata (KVMap.empty.setNat `changed 1) info.value }
                let changedChild := { child with constInfo := AsyncConstantInfo.ofConstantInfo ci }
                pure { nested with
                  revList := changedChild :: nested.revList.tail
                  map := nested.map.insert child.constInfo.name changedChild,
                  normalizedTrie := nested.normalizedTrie.insert (privateToUserName child.constInfo.name) changedChild }
          pure { member with aconstsImpl := .pure (.mk nested) }
      pure (entries.insert cacheKey (.pure (.mk { result with newConsts.private := [member] })))
    else pure entries
  let ref ← IO.mkRef (map.insert (TypeName.typeName Environment.RealizeConstKey) (unsafeCast entries))
  changed := { changed with realizeMapRef := ref }
  return { env with localRealizationCtxMap := env.localRealizationCtxMap.insert owner changed }
@[implemented_by changedEnv]
private opaque changedEnvSafe (env : Environment) (owner key : Name) (mode : String) : IO Environment

private def controls : MetaM Unit := do
  let mode := (← IO.getEnv "LOCAL_CASE").getD "cached"
  let expected := (← IO.getEnv "LOCAL_EXPECT").getD ""
  let before ← getEnv
  let owner := `Cubic.toPoly
  let key := `Cubic.toPoly.eq_1
  unless !before.containsOnBranch key && (before.checked.get.find? key).isSome do
    throwError "fixture not cached-only"
  let checkedBefore := before.checked.get.constants.foldStage2 (fun acc n _ => acc.insert n) ({} : NameSet)
  let callbacks ← IO.mkRef (0 : Nat)
  realizeConst owner key do
    callbacks.modify (· + 1)
    throwError "FIXTURE_CALLBACK_INVOKED"
  unless (← callbacks.get) == 0 do throwError "fixture callback count"
  let stock ← getEnv
  let some (_, payload) ← encodeBoundaryRealizationBatch? before stock checkedBefore #[] #[]
    | throwError "fixture missing capture"
  if let some path ← IO.getEnv "LOCAL_PAYLOAD" then IO.FS.writeFile path payload
  let modeEnv ← changedEnvSafe before owner key mode
  setEnv modeEnv
  let mut rejected := false
  try
    if mode == "fresh-mode" then
      discard <| encodeBoundaryRealizationBatch? before stock {} #[] #[]
    else if mode == "foreign" then executeBoundaryRealizationBatch `Foreign.eq_1 payload
    else executeBoundaryRealizationBatch key payload
  catch ex =>
    let error ← ex.toMessageData.toString
    if expected.isEmpty || (error.splitOn expected).length <= 1 then throwError "fixture wrong rejection: {error}"
    rejected := true
    IO.println s!"EXPECTED_REJECTION {error}"
  unless rejected == !expected.isEmpty do throwError "fixture missing rejection"
  unless (← callbacks.get) == 0 do throwError "fixture callback count after"
  IO.println s!"LOCAL_CONTROL_OK {mode} callbacks=0"
run_cmd liftTermElabM controls
'''

FRESH = r'''
module
import Mathlib.Init
meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all Lean.Environment
open Lean Meta Elab Command ExplicitLean.SimpEngine.Boundary
@[expose] public section
namespace LocalCachedFresh
def owner (n : Nat) : Nat := n + 1
end LocalCachedFresh
meta section
private def freshControl : MetaM Unit := do
  let before ← getEnv
  let owner := `LocalCachedFresh.owner
  let key := `LocalCachedFresh.owner.eq_1
  let checkedBefore := before.checked.get.constants.foldStage2 (fun acc n _ => acc.insert n) ({} : NameSet)
  unless !(checkedBefore.contains key) && !(← lookupCacheTask before owner key).isSome do
    throwError "fixture unexpectedly warm"
  try
    discard <| localCachedDescriptor before owner key
    throwError "fixture expected absent"
  catch ex =>
    let message ← ex.toMessageData.toString
    unless (message.splitOn "activation_cache_absent").length > 1 do throw ex
  let some equations ← Lean.Meta.getEqnsFor? owner | throwError "fixture no equations"
  unless equations == #[key] do throwError "fixture unexpected equations"
  let stock ← getEnv
  try
    discard <| encodeBoundaryRealizationBatch? before stock checkedBefore #[] #[]
    throwError "fixture expected fresh rejection"
  catch ex =>
    let message ← ex.toMessageData.toString
    unless (message.splitOn "boundary_local_cached_only").length > 1 do throw ex
  IO.println "FRESH_LOCAL_REJECTED beforeCacheAbsent=true beforeCheckedAbsent=true"
run_cmd liftTermElabM freshControl
'''

CONSTANTS = r'''
module
import Mathlib.Init
meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
open Lean Meta Elab Command ExplicitLean.SimpEngine.Boundary
meta section
private def constantsControl : MetaM Unit := do
  let base : ConstantVal := { name := `fixture, levelParams := [`u], type := .forallE `x (mkConst ``Nat) (mkConst ``Nat) .default }
  let body := Expr.lam `x (mkConst ``Nat) (.bvar 0) .default
  let axiomInfo := ConstantInfo.axiomInfo { toConstantVal := base, isUnsafe := false }
  let defn := ConstantInfo.defnInfo { toConstantVal := base, value := body, hints := .regular 3, safety := .safe }
  let thm := ConstantInfo.thmInfo { toConstantVal := base, value := body }
  let opaqueInfo := ConstantInfo.opaqueInfo { toConstantVal := base, value := body, isUnsafe := false }
  let quot := ConstantInfo.quotInfo { toConstantVal := base, kind := .lift }
  let ind := ConstantInfo.inductInfo { toConstantVal := base, numParams := 1, numIndices := 2,     all := [`fixture], ctors := [`fixture.mk], numNested := 0, isRec := true, isUnsafe := false, isReflexive := false }
  let ctor := ConstantInfo.ctorInfo { toConstantVal := base, induct := `fixture, cidx := 0, numParams := 1, numFields := 2, isUnsafe := false }
  let recInfo := ConstantInfo.recInfo { toConstantVal := base, all := [`fixture], numParams := 1,     numIndices := 2, numMotives := 1, numMinors := 1, rules := [{ ctor := `fixture.mk, nfields := 2, rhs := body }], k := false, isUnsafe := false }
  let variants := #[axiomInfo, defn, thm, opaqueInfo, quot, ind, ctor, recInfo]
  for value in variants do
    let original ← localConstantJson value
    let .arr parts := original | throwError "fixture json"
    unless parts.size > 4 do throwError "fixture incomplete constant"
  let mutations : Array (String × ConstantInfo × ConstantInfo) := #[
    ("axiom-safety", axiomInfo, .axiomInfo { toConstantVal := base, isUnsafe := true }),
    ("definition-value", defn, .defnInfo { toConstantVal := base, value := .mdata (KVMap.empty.setNat `note 7) body, hints := .regular 3, safety := .safe }),
    ("definition-hints", defn, .defnInfo { toConstantVal := base, value := body, hints := .abbrev, safety := .safe }),
    ("definition-safety", defn, .defnInfo { toConstantVal := base, value := body, hints := .regular 3, safety := .unsafe }),
    ("theorem-proof", thm, .thmInfo { toConstantVal := base, value := .lam `y (mkConst ``Nat) (.bvar 0) .default }),
    ("opaque-safety", opaqueInfo, .opaqueInfo { toConstantVal := base, value := body, isUnsafe := true }),
    ("quotient-kind", quot, .quotInfo { toConstantVal := base, kind := .ind }),
    ("inductive-flag", ind, .inductInfo { toConstantVal := base, numParams := 1, numIndices := 2,       all := [`fixture], ctors := [`fixture.mk], numNested := 0, isRec := true, isUnsafe := false, isReflexive := true }),
    ("constructor-field", ctor, .ctorInfo { toConstantVal := base, induct := `fixture, cidx := 0, numParams := 1, numFields := 3, isUnsafe := false }),
    ("recursor-rhs", recInfo, .recInfo { toConstantVal := base, all := [`fixture], numParams := 1,       numIndices := 2, numMotives := 1, numMinors := 1, rules := [{ ctor := `fixture.mk, nfields := 2,       rhs := .lam `x (mkConst ``Nat) (.bvar 0) .implicit }], k := false, isUnsafe := false }),
    ("recursor-rule-count", recInfo, .recInfo { toConstantVal := base, all := [`fixture], numParams := 1,       numIndices := 2, numMotives := 1, numMinors := 1, rules := [], k := false, isUnsafe := false }),
    ("binder-annotation", axiomInfo, .axiomInfo { toConstantVal := { base with       type := .forallE `x (mkConst ``Nat) (mkConst ``Nat) .implicit }, isUnsafe := false }),
    ("binder-name", axiomInfo, .axiomInfo { toConstantVal := { base with       type := .forallE `y (mkConst ``Nat) (mkConst ``Nat) .default }, isUnsafe := false })]
  for (label, a, b) in mutations do
    unless (← localConstantJson a) != (← localConstantJson b) do throwError "fixture missed {label}"
    IO.println s!"CONSTANT_MUTATION_OK {label}"
  IO.println s!"CONSTANT_KINDS_OK {variants.size} mutations={mutations.size}"
run_cmd liftTermElabM constantsControl
'''


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parent = ROOT / ".lake/local-cached-owner-check"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="controls-", dir=parent))
    print(work, flush=True)
    records = []
    sources = [ROOT / "ExplicitLean/SimpEngine/Boundary/RealizationCodec.lean",
               ROOT / "Experiment/boundary_expr_codec.py", ROOT / "Experiment/boundary_protocol.py",
               Path(__file__), ROOT / ".lake/build/lib/libexplicitLean_ExplicitLean.dylib"]
    for stem in ["Boundary/RealizationCodec", "Boundary"]:
        sources += list((ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine").glob(stem + ".*"))
    cubic_path = ROOT / ".lake/packages/mathlib/Mathlib/Algebra/CubicDiscriminant.lean"
    extra_path = ROOT / ".lake/packages/mathlib/Mathlib/AlgebraicTopology/ExtraDegeneracy.lean"
    sources += [cubic_path, extra_path]
    before = {str(p): sha(p) for p in sources}
    (work / "inputs-before.json").write_text(json.dumps(before, indent=2))
    cubic = cubic_path.read_text().split("@[simp]\ntheorem coeff_eq_zero", 1)[0]
    cubic += "end Coeff\nend Basic\nend Cubic\nend\n"
    imports = "meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec\nmeta import all Lean.Environment\n"
    controls = cubic.replace("module\n", "module\n" + imports, 1) + CONTROLS

    def compile_case(label, module, text, *, mode=None, expected="", recording=False,
                     expected_abort=None, success_marker=None):
        relative = Path(*module.split(".")).with_suffix(".lean")
        path = work / label / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        env, nonce = protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment()
        if mode is not None:
            env.update(LOCAL_CASE=mode, LOCAL_EXPECT=expected, LOCAL_PAYLOAD=str(work / f"{label}.payload.json"))
        command = ["lake", "env", "lean", f"--load-dynlib={sources[4]}", "-R", str(work / label), str(path)]
        run = run_process(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=180)
        log = work / f"{label}.log"
        log.write_text(run.stdout)
        records.append(dict(label=label, module=module, source=str(path), sourceSha256=sha(path),
                            command=command, nonce=nonce, exit=run.returncode, log=str(log),
                            logSha256=sha(log), expected=expected, expectedAbort=expected_abort))
        (work / "progress.json").write_text(json.dumps(records, indent=2))
        if expected_abort is None:
            assert run.returncode == 0, run.stdout[-5000:]
        else:
            assert run.returncode != 0, "expected fail-closed compiler rejection"
        checker = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        try:
            checker(run.stdout, expected_nonce=nonce)
        except RuntimeError as error:
            assert expected_abort and expected_abort in str(error), str(error)
        else:
            assert expected_abort is None, "required authenticated abort missing"
        if success_marker:
            assert success_marker in run.stdout, run.stdout[-5000:]
        print(label + ": passed", flush=True)
        return protocol.parse_framed_json_lines(run.stdout, marker="SIMP_ENGINE_BOUNDARY_ARTIFACT ",
                   expected_nonce=nonce, label=label) if recording and expected_abort is None else []

    cases = [("cached", ""), ("saved-options", ""), ("saved-environment", ""),
             ("missing", "activation_cache_absent"), ("pending", "activation_cache_pending"),
             ("wrong-type", "activation_cache_type"), ("disabled", "boundary_local_cached_owner_context"),
             ("changed-owner", "boundary_local_cached_owner_checked"),
             ("changed-owner-consistent", "boundary_local_cached_owner_conflict"),
             ("signature", "boundary_local_cached_async_signature"),
             ("nested-map", "boundary_local_cached_graph_lookup_conflict"),
             ("nested-cardinality", "boundary_local_cached_graph_cardinality"),
             ("nested-body", "boundary_local_cached_descriptor_conflict"),
             ("fresh-mode", "boundary_local_cached_only"), ("foreign", "boundary_local_cached_identity")]
    for mode, expected in cases:
        compile_case(mode, "Mathlib.Algebra.CubicDiscriminant", controls, mode=mode, expected=expected,
                     success_marker=f"LOCAL_CONTROL_OK {mode} callbacks=0")
        payload = (work / f"{mode}.payload.json").read_text()
        validate_realization_payload(payload, json.loads(payload)[10][1])
    compile_case("genuinely-cold", "Experiment.LocalCachedFresh", FRESH,
                 success_marker="FRESH_LOCAL_REJECTED beforeCacheAbsent=true beforeCheckedAbsent=true")
    compile_case("constant-fields", "Experiment.LocalCachedConstants", CONSTANTS,
                 success_marker="CONSTANT_KINDS_OK 8 mutations=13")

    oldcall = "simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,\n    Polynomial.coeff_C_mul_X_pow]"
    record = cubic.replace("module\n", "module\npublic meta import ExplicitLean.SimpEngine.Boundary\n", 1)
    record = record.replace(oldcall, oldcall.replace("simp", 'simp_engine_boundary_record "local-cubic"', 1))
    reports = compile_case("cubic-record", "Mathlib.Algebra.CubicDiscriminant", record, recording=True)
    assert reports
    for report in reports:
        protocol.validate_report(report, "local-cubic", "Mathlib.Algebra.CubicDiscriminant")
    actions = [a for r in reports for a in r["environmentActions"] if a["kind"] == "realize_groups"]
    assert len(actions) == 1 and json.loads(actions[0]["declaration"])[0] == "boundary_local_cached_v1"
    replacement = source.preserve_original_call(source.format_report_variants(reports, "  "), oldcall, "  ")
    applied = record.replace(oldcall.replace("simp", 'simp_engine_boundary_record "local-cubic"', 1), replacement)
    compile_case("cubic-replay", "Mathlib.Algebra.CubicDiscriminant", applied)

    extra = extra_path.read_text().split("@[reassoc (attr := simp)]\ntheorem ExtraDegeneracy.s_comp_base", 1)[0]
    extra += "end AugmentedCechNerve\nend Arrow\nend CategoryTheory\n"
    extra = extra.replace("module\n", "module\npublic meta import ExplicitLean.SimpEngine.Boundary\n", 1)
    offset = extra.rindex("simp [ExtraDegeneracy.s]")
    extra = extra[:offset] + extra[offset:].replace("simp", 'simp_engine_boundary_record "local-extra"', 1)
    compile_case("extra-unsupported-aux", "Mathlib.AlgebraicTopology.ExtraDegeneracy", extra,
                 recording=True, expected_abort="activation_nonempty_aux_cache")

    payload = json.loads((work / "cached.payload.json").read_text())
    mutations = [
        ("missing-field", lambda p: p.pop()),
        ("fresh-mode", lambda p: p.__setitem__(1, False)),
        ("duplicate-member", lambda p: p[2].append(copy.deepcopy(p[2][0]))),
        ("foreign-owner", lambda p: p[10].__setitem__(0, [["s", "Foreign"]])),
        ("wrong-owner-safety", lambda p: p[10][2].__setitem__(6, "unsafe")),
        ("owner-safety-type", lambda p: p[10][2].__setitem__(6, [])),
        ("node-kind", lambda p: p[10][3][3][0][0].__setitem__(0, "unknown")),
        ("graph-root", lambda p: p[10][3].__setitem__(4, 99999)),
        ("graph-root-bool", lambda p: p[10][3].__setitem__(4, True)),
        ("graph-cycle", lambda p: p[10][3][3][0][3].append(0)),
        ("duplicate-node", lambda p: p[10][3][3].append(copy.deepcopy(p[10][3][3][0]))),
        ("duplicate-child", lambda p: p[10][3][3][-1][3].append(p[10][3][3][-1][3][0])),
        ("public-safety", lambda p: p[10][3][3][p[10][3][5]][0].__setitem__(4, True)),
        ("persistent-bytes", lambda p: p[10][3][3][p[10][3][4]][2][3][0].__setitem__(1, "x")),
        ("metadata-shape", lambda p: p[10][3][3][p[10][3][4]].__setitem__(2, [])),
    ]
    wire = []
    for label, mutate in mutations:
        value = copy.deepcopy(payload)
        mutate(value)
        try:
            validate_realization_payload(json.dumps(value), payload[10][1])
        except RuntimeError as error:
            wire.append(dict(label=label, error=str(error)))
        else:
            raise AssertionError(f"accepted malformed local wire: {label}")
    after = {str(p): sha(p) for p in sources}
    assert before == after, "tool/source changed during controls"
    files = [p for p in work.rglob("*") if p.is_file()]
    report = dict(kind="local_cached_realization_controls", schema=1, records=records,
                  constantKinds=8, constantMutations=13, wireRejections=wire, inputsBefore=before,
                  inputsAfter=after, hashes={str(p): sha(p) for p in files},
                  limitations=["fresh local production unsupported", "ExtraDegeneracy auxiliary member cache unsupported",
                               "not whole-module coverage", "not general export-hook purity"])
    (work / "report.json").write_text(json.dumps(report, indent=2))
    print(f"passed {len(records)} processes, {len(wire)} wire rejections; {work / 'report.json'}", flush=True)


if __name__ == "__main__":
    main()
