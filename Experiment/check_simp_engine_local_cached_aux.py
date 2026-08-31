#!/usr/bin/env python3
"""Exact local auxiliary-cache witness controls. Uses prebuilt tools only."""
from __future__ import annotations
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import boundary_protocol as protocol
from boundary_expr_codec import validate_realization_payload
import check_simp_engine_boundary_source as source
from process_runner import run_process
ROOT = Path(__file__).resolve().parents[1]

CONTROLS = r'''
meta section
open Lean Meta Elab Command ExplicitLean.SimpEngine.Boundary
private unsafe def mutateAuxEnv (env : Environment) (owner key : Name) (mode : String) : IO Environment := do
  let some ctx := env.localRealizationCtxMap.find? owner | throw <| IO.userError "fixture context"
  let map ← ctx.realizeMapRef.get
  let some raw := map.find? (TypeName.typeName Environment.RealizeConstKey) | throw <| IO.userError "fixture cache map"
  let entries := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
  let cacheKey : Environment.RealizeConstKey := { constName := key }
  let some task := entries.find? cacheKey | throw <| IO.userError "fixture cache key"
  let some result := task.get.get? Environment.RealizeConstResult | throw <| IO.userError "fixture result"
  if mode == "missing-cache" then
    let ref ← IO.mkRef (map.insert (TypeName.typeName Environment.RealizeConstKey) (unsafeCast (entries.erase cacheKey)))
    return { env with localRealizationCtxMap := env.localRealizationCtxMap.insert owner { ctx with realizeMapRef := ref } }
  let [member] := result.newConsts.private | throw <| IO.userError "fixture member"
  let view ← memberEnvironment env member
  let cache := (auxLemmasExt.getState view).lemmas
  let some (auxKey, name, levels) := cache.toArray.find? (fun (k,n,_) => isPrivateName n && !k.defeq && !defeqAttr.hasTag view n)
    | throw <| IO.userError "fixture private untagged proof"
  let checked := env.checked.get
  if mode == "proof" || mode == "owner" then
    let target := if mode == "proof" then name else owner
    let some original := checked.find? target | throw <| IO.userError "fixture checked declaration"
    let modified ← match original with
      | .thmInfo v => pure <| ConstantInfo.thmInfo { v with value := .mdata (KVMap.empty.setNat `mutation 1) v.value }
      | .defnInfo v => pure <| ConstantInfo.defnInfo { v with value := .mdata (KVMap.empty.setNat `mutation 1) v.value }
      | _ => throw <| IO.userError "fixture unexpected checked declaration"
    let checked := { checked with constants := checked.constants.insert target modified }
    let rewrite := fun branch : AsyncConsts => Id.run do
      let some old := branch.map.find? target | return branch
      let replacement := { old with constInfo := AsyncConstantInfo.ofConstantInfo modified }
      return { branch with
        revList := branch.revList.map fun old => if old.constInfo.name == target then replacement else old
        map := branch.map.insert target replacement
        normalizedTrie := branch.normalizedTrie.insert (privateToUserName target) replacement }
    return { env with
      checked := .pure checked
      asyncConstsMap := { «private» := rewrite env.asyncConstsMap.private, «public» := rewrite env.asyncConstsMap.public } }
  let changedKey := if mode == "type" then { auxKey with type := .mdata (KVMap.empty.setNat `mutation 1) auxKey.type }
    else if mode == "open-key" then { auxKey with type := .bvar 0 }
    else if mode == "privacy" then { auxKey with isPrivate := false }
    else if mode == "defeq" then { auxKey with defeq := true }
    else auxKey
  let changedName := if mode == "name" then `Missing.aux else name
  let changedLevels := if mode == "levels" then levels ++ [`extra] else levels
  let updated := if mode == "clear" then {} else (cache.erase auxKey).insert changedKey (changedName, changedLevels)
  let changedView := auxLemmasExt.setState view { lemmas := updated }
  let member := { member with exts? := some (.pure changedView.base.private.extensions) }
  let result := { result with newConsts.private := [member] }
  let ref ← IO.mkRef (map.insert (TypeName.typeName Environment.RealizeConstKey)
    (unsafeCast (entries.insert cacheKey (.pure (.mk result)))))
  return { env with localRealizationCtxMap := env.localRealizationCtxMap.insert owner { ctx with realizeMapRef := ref } }
@[implemented_by mutateAuxEnv]
private opaque mutateAuxEnvSafe (env : Environment) (owner key : Name) (mode : String) : IO Environment

private def auxControls : MetaM Unit := do
  let before ← getEnv
  let owner := `CategoryTheory.Arrow.AugmentedCechNerve.ExtraDegeneracy.s
  let key := owner ++ `eq_1
  let mode := (← IO.getEnv "AUX_CASE").getD "cached"
  let expected := (← IO.getEnv "AUX_EXPECT").getD ""
  unless !before.containsOnBranch key && (before.checked.get.find? key).isSome do throwError "fixture cached shape"
  let checkedBefore := before.checked.get.constants.foldStage2 (fun acc n _ => acc.insert n) ({} : NameSet)
  let callbacks ← IO.mkRef (0 : Nat)
  realizeConst owner key do
    callbacks.modify (· + 1)
    throwError "FIXTURE_UNEXPECTED_CALLBACK"
  unless (← callbacks.get) == 0 do throwError "fixture callback"
  let stock ← getEnv
  let some (_, payload) ← encodeBoundaryRealizationBatch? before stock checkedBefore #[] #[]
    | throwError "fixture capture missing"
  let .arr data ← ofExcept (Json.parse payload) | throwError "fixture payload"
  unless data[0]? == some (.str "boundary_local_cached_aux_v1") do throwError "fixture wrong new tag"
  if let some path ← IO.getEnv "AUX_PAYLOAD" then IO.FS.writeFile path payload
  setEnv (← mutateAuxEnvSafe before owner key mode)
  let mut rejected := false
  try
    if mode == "legacy-v1" then discard <| localCachedDescriptor (← getEnv) owner key
    else executeBoundaryRealizationBatch key payload
  catch ex =>
    let error ← ex.toMessageData.toString
    if expected.isEmpty || (error.splitOn expected).length <= 1 then throwError "fixture wrong rejection {error}"
    rejected := true
    IO.println s!"EXPECTED_REJECTION {error}"
  unless rejected == !expected.isEmpty do throwError "fixture missing rejection"
  unless (← callbacks.get) == 0 do throwError "fixture callback after"
  IO.println s!"LOCAL_AUX_CONTROL_OK {mode} callbacks=0"
run_cmd liftTermElabM auxControls
'''

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def expand_descriptor(value):
    result = copy.deepcopy(value)
    assert len(result) == 7 and result[0] == "completed_local_cached_aux_v1"
    proofs = result.pop()
    for node in result[3]:
        if node[2] is not None:
            for entry in node[2][4]:
                entry[5] = copy.deepcopy(proofs[entry[5]])
    return result

def main():
    parent = ROOT / ".lake/local-cached-aux-check"
    parent.mkdir(exist_ok=True, parents=True)
    work = Path(tempfile.mkdtemp(prefix="controls-", dir=parent)); print(work,flush=True)
    records=[]
    dylib=ROOT/".lake/build/lib/libexplicitLean_ExplicitLean.dylib"
    owned=[ROOT/"ExplicitLean/SimpEngine/Boundary/RealizationCodec.lean",ROOT/"Experiment/boundary_expr_codec.py",
           ROOT/"Experiment/boundary_protocol.py",Path(__file__),dylib]
    extra_path=ROOT/".lake/packages/mathlib/Mathlib/AlgebraicTopology/ExtraDegeneracy.lean"
    cubic_path=ROOT/".lake/packages/mathlib/Mathlib/Algebra/CubicDiscriminant.lean"
    owned += [extra_path,cubic_path]
    before={str(p):sha(p) for p in owned};(work/"inputs-before.json").write_text(json.dumps(before,indent=2))
    extra=extra_path.read_text().split("@[reassoc (attr := simp)]\ntheorem ExtraDegeneracy.s_comp_base",1)[0]
    extra += "end AugmentedCechNerve\nend Arrow\nend CategoryTheory\n"
    controls=extra.replace("module\n","module\nmeta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec\nmeta import all Lean.Environment\n",1)+CONTROLS
    def compile(label,module,text,*,mode=None,expected="",recording=False):
        path=work/label/Path(*module.split('.')).with_suffix('.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        env,nonce=protocol.recording_subprocess_environment() if recording else protocol.replay_subprocess_environment()
        if mode is not None:env.update(AUX_CASE=mode,AUX_EXPECT=expected,AUX_PAYLOAD=str(work/f"{label}.payload.json"))
        command=['lake','env','lean',f'--load-dynlib={dylib}','-R',str(work/label),str(path)]
        run=run_process(command,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
        log=work/f'{label}.log';log.write_text(run.stdout)
        records.append(dict(label=label,source=str(path),command=command,nonce=nonce,exit=run.returncode,
                            log=str(log),expected=expected,recording=recording,module=module))
        (work/'progress.json').write_text(json.dumps(records,indent=2))
        assert run.returncode==0,run.stdout[-6000:]
        (protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers)(run.stdout,expected_nonce=nonce)
        if mode is not None:
            assert f"LOCAL_AUX_CONTROL_OK {mode} callbacks=0" in run.stdout
            payload=(work/f'{label}.payload.json').read_text();v=json.loads(payload);validate_realization_payload(payload,v[10][1])
        print(label+': passed',flush=True)
        return protocol.parse_framed_json_lines(run.stdout,marker='SIMP_ENGINE_BOUNDARY_ARTIFACT ',expected_nonce=nonce,label=label) if recording else []
    for mode,expected in [('cached',''),('type','boundary_local_aux_type_conflict'),('name','boundary_local_aux_missing_checked_proof'),
        ('levels','boundary_local_aux_levels_conflict'),('privacy','boundary_local_aux_privacy_conflict'),('defeq','boundary_local_aux_defeq_conflict'),
        ('proof','boundary_local_cached_descriptor_conflict'),('owner','boundary_local_cached_owner_conflict'),
        ('open-key','boundary_local_aux_open_key'),('clear','boundary_local_cached_descriptor_conflict'),
        ('missing-cache','activation_cache_absent'),('legacy-v1','activation_nonempty_aux_cache')]:
        compile(mode,'Mathlib.AlgebraicTopology.ExtraDegeneracy',controls,mode=mode,expected=expected)
    cubic=cubic_path.read_text().split('@[simp]\ntheorem coeff_eq_zero',1)[0]+'end Coeff\nend Basic\nend Cubic\nend\n'
    for module,raw,call,label,tag in [
      ('Mathlib.AlgebraicTopology.ExtraDegeneracy',extra,'simp [ExtraDegeneracy.s]','extra','boundary_local_cached_aux_v1'),
      ('Mathlib.Algebra.CubicDiscriminant',cubic,'simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,\n    Polynomial.coeff_C_mul_X_pow]','cubic','boundary_local_cached_v1')]:
        raw=raw.replace('module\n','module\npublic meta import ExplicitLean.SimpEngine.Boundary\n',1)
        at=raw.rindex(call);instrumented_call=call.replace('simp',f'simp_engine_boundary_record "{label}"',1)
        recorded=raw[:at]+instrumented_call+raw[at+len(call):]
        reports=compile(label+'-record',module,recorded,recording=True);assert reports
        for report in reports:protocol.validate_report(report,label,module)
        actions=[a for r in reports for a in r['environmentActions'] if a['kind']=='realize_groups']
        assert len(actions)==1 and json.loads(actions[0]['declaration'])[0]==tag
        replacement=source.preserve_original_call(source.format_report_variants(reports,'  '),call,'  ')
        compile(label+'-replay',module,raw[:at]+replacement+raw[at+len(call):])
    payload=json.loads((work/'cached.payload.json').read_text())
    def table(p):return p[10][3][6]
    def entry(p):return next(n[2][4][0] for n in p[10][3][3] if n[2] is not None and n[2][4])
    bad=[('missing-table',lambda p:p[10][3].pop()),('duplicate-proof',lambda p:table(p).append(copy.deepcopy(table(p)[0]))),
      ('proof-not-theorem',lambda p:table(p)[0].__setitem__(0,'definition')),
      ('reference-bounds',lambda p:entry(p).__setitem__(5,len(table(p)))),('reference-bool',lambda p:entry(p).__setitem__(5,True)),
      ('entry-type',lambda p:entry(p).__setitem__(0,'bad')),('entry-name',lambda p:entry(p).__setitem__(3,[["s","Foreign"]])),
      ('entry-levels',lambda p:entry(p).__setitem__(4,[[["s","extra"]]])),('entry-privacy-type',lambda p:entry(p).__setitem__(1,'false')),
      ('entry-defeq-type',lambda p:entry(p).__setitem__(2,0)),('proof-body-dag',lambda p:table(p)[0].__setitem__(4,'bad')),
      ('duplicate-key',lambda p:next(n[2][4] for n in p[10][3][3] if n[2] is not None and n[2][4]).append(copy.deepcopy(entry(p))))]
    wire=[]
    for label,mutate in bad:
        value=copy.deepcopy(payload);mutate(value)
        try:validate_realization_payload(json.dumps(value),payload[10][1])
        except RuntimeError as error:wire.append(dict(label=label,error=str(error)))
        else:raise AssertionError('malformed wire accepted '+label)
    after={str(p):sha(p) for p in owned};assert before==after
    files=[p for p in work.rglob('*') if p.is_file()]
    report=dict(kind='local_aux_cached_controls',schema=1,records=records,wireRejections=wire,inputsBefore=before,inputsAfter=after,
                hashes={str(p):sha(p) for p in files},acceptedCampaignCoverage=False)
    (work/'report.json').write_text(json.dumps(report,indent=2));print('COMPLETE '+str(work/'report.json'),flush=True)
if __name__=='__main__':main()
