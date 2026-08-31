#!/usr/bin/env python3
"""Fresh-process codec/guard controls, including compiler-success caught aborts."""
from pathlib import Path
import hashlib,json,tempfile
import boundary_materialize_shard as m
import boundary_protocol as p
import check_simp_engine_recursive_realizations as runtime
from boundary_expr_codec import validate_reference_expr_dag,validate_expr_dag,validate_boundary_expr_dag
ROOT=Path(__file__).resolve().parents[1]
HEADER='''module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary.Tactic
import all ExplicitLean.SimpEngine.Boundary.Tactic
import all ExplicitLean.SimpEngine.Boundary.ExpressionReferences
import all ExplicitLean.SimpEngine.Boundary.ModuleDataObservation
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary
meta section
elab "reference_fixture" : tactic => do
  let saved ← Tactic.saveState
  let core ← getThe Core.State
  try
    withReplayAbort "reference-fixture" "apply" <| withMainContext do
      let hole ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
      let target ← mkEq hole hole
      let goal := (← mkFreshExprSyntheticOpaqueMVar target).mvarId!
      let refs ← boundaryExpressionReferenceContext [goal] {}
      unless refs.mvars == #[goal, hole.mvarId!] do throwError "fixture reference order"
      let payload ← encodeBoundaryExprWithReferences hole refs
      let use ← protectBoundaryReferences refs #[hole]
      __BODY__
      let nonce := (← IO.getEnv boundaryRunNonceEnv).getD "missing"
      IO.println s!"\\nEXPRESSION_REFERENCE_OK {nonce}"
  finally
    saved.restore
    modifyThe Core.State fun _ => core
end
example : True := by
  try reference_fixture
  exact True.intro
'''
CASES=[
('roundtrip','''let decoded ← decodeBoundaryExprWithReferences payload refs
unless decoded.equal hole do throwError "not exact original reference"
use.checkAt goal #[decoded]
use.checkUnchanged''',None),
('legacy_closed','''let original := mkConst ``True
unless (← decodeBoundaryExpr (← encodeBoundaryExpr original)).equal original do throwError "legacy v1"
unless (← decodeBoundaryExprWithUniverses (← encodeBoundaryExprWithUniverses original refs.universes) refs.universes).equal original do throwError "legacy v2"''',None),
('legacy_rejects_reference','discard <| encodeBoundaryExpr hole','boundary_expr_unresolved_metavariable'),
('structural_rejects_reference','discard <| encodeBoundaryStructExpr hole','boundary_struct_expr_not_closed'),
('fresh_reference','''let fresh ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
discard <| encodeBoundaryExprWithReferences fresh refs''','boundary_reference_not_preexisting'),
('visible_reference','discard <| encodeBoundaryExprWithReferences (mkMVar goal) refs','boundary_reference_ineligible'),
('out_of_range','''let raw := Json.arr #[.str "expr_dag_v3", toJson refs.universes.size, toJson refs.mvars.size, .arr #[.arr #[.str "v", toJson refs.mvars.size]], toJson (0 : Nat)]
discard <| decodeBoundaryExprWithReferences raw.compress refs''','boundary_reference_index'),
('wrong_count','''let raw := Json.arr #[.str "expr_dag_v3", toJson refs.universes.size, toJson (refs.mvars.size + 1), .arr #[.arr #[.str "v", toJson (1 : Nat)]], toJson (0 : Nat)]
discard <| decodeBoundaryExprWithReferences raw.compress refs''','boundary expression reference count mismatch'),
('assigned_reference','''hole.mvarId!.assign (mkConst ``True.intro)
discard <| decodeBoundaryExprWithReferences payload refs''','boundary_reference_state_changed'),
('delayed_reference','''assignDelayedMVar hole.mvarId! #[] goal
discard <| decodeBoundaryExprWithReferences payload refs''','boundary_reference_state_changed'),
('self_assignment','use.checkAt hole.mvarId! #[hole]','boundary_reference_occurs'),
('protected_assignment','''hole.mvarId!.assign (mkConst ``True.intro)
use.checkAt goal #[hole]''','boundary_reference_dependency_changed'),
('no_inferred_assignment','''let value ← mkFreshExprSyntheticOpaqueMVar (mkConst ``Nat)
let goal := (← mkFreshExprSyntheticOpaqueMVar (← mkEq value value)).mvarId!
let refs ← boundaryExpressionReferenceContext [goal] {}
let use ← protectBoundaryReferences refs #[value]
let solved ← withBoundaryReferenceValidation use <| withAssignableSyntheticOpaque <| isDefEq value (mkNatLit 0)
if solved then throwError "inferred protected assignment"
use.checkUnchanged''',None),
('no_pending_synthesis','''let instType := mkApp (mkConst ``Inhabited [.succ .zero]) (mkConst ``Nat)
let inst ← mkFreshExprMVar instType .synthetic
let candidate := mkApp2 (mkConst ``Inhabited.default [.succ .zero]) (mkConst ``Nat) inst
let coreBefore ← getThe Core.State
let metaBefore ← getThe Meta.State
let ordinary ← withNewMCtxDepth do
  let success ← isDefEq candidate (mkNatLit 0)
  return success && (← inst.mvarId!.isAssigned)
modifyThe Core.State fun _ => coreBefore
modifyThe Meta.State fun _ => metaBefore
unless ordinary do throwError "fixture did not demonstrate ordinary synthesis"
let guarded ← withBoundaryReferenceValidation use do
  let success ← isDefEq candidate (mkNatLit 0)
  if ← inst.mvarId!.isAssigned then throwError "pending synthesis ran under guard"
  return success
if guarded then throwError "guard inferred a class instance"''',None),
('type_cycle','''let ctx ← getMCtx
let some d := ctx.decls.find? hole.mvarId! | throwError "fixture missing hole"
let ctx := {ctx with decls := ctx.decls.insert hole.mvarId! {d with type := mkMVar goal}}
setMCtx ctx
discard <| protectBoundaryReferences {refs with before := ctx} #[hole]''','boundary_reference_dependency_cycle'),
('two_hop_type_cycle','''let bridge ← mkFreshExprMVar (mkMVar goal)
let ctx ← getMCtx
let some d := ctx.decls.find? hole.mvarId! | throwError "fixture missing hole"
let ctx := {ctx with decls := ctx.decls.insert hole.mvarId! {d with type := bridge}}
setMCtx ctx
discard <| protectBoundaryReferences {refs with before := ctx} #[hole]''','boundary_reference_dependency_cycle'),
('indirect_assignment_cycle','''let bridge ← mkFreshExprMVar (mkSort .zero)
bridge.mvarId!.assign (mkMVar goal)
let ctx ← getMCtx
let some d := ctx.decls.find? hole.mvarId! | throwError "fixture missing hole"
let ctx := {ctx with decls := ctx.decls.insert hole.mvarId! {d with type := bridge}}
setMCtx ctx
discard <| protectBoundaryReferences {refs with before := ctx} #[hole]''','boundary_reference_dependency_cycle'),
('delayed_fvar_cycle','''let pending ← mkFreshExprMVar (mkSort .zero)
let bridge ← mkFreshExprMVar (mkSort .zero)
assignDelayedMVar bridge.mvarId! #[mkMVar goal] pending.mvarId!
let ctx ← getMCtx
let some d := ctx.decls.find? hole.mvarId! | throwError "fixture missing hole"
let ctx := {ctx with decls := ctx.decls.insert hole.mvarId! {d with type := bridge}}
setMCtx ctx
discard <| protectBoundaryReferences {refs with before := ctx} #[hole]''','boundary_reference_dependency_cycle'),

('local_instance_cycle','''let ctx ← getMCtx
let some d := ctx.decls.find? hole.mvarId! | throwError "fixture missing hole"
let d := {d with localInstances := #[{className := ``True, fvar := mkMVar goal}]}
let ctx := {ctx with decls := ctx.decls.insert hole.mvarId! d}
setMCtx ctx
discard <| protectBoundaryReferences {refs with before := ctx} #[hole]''','boundary_reference_dependency_cycle'),
('scope_missing_local','''let hidden ← withLocalDeclD `hidden (mkConst ``True) fun _ => mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
let ctx ← getMCtx
let refs := {refs with mvars := refs.mvars.push hidden.mvarId!, before := ctx}
let use ← protectBoundaryReferences refs #[hidden]
use.checkAt goal #[hidden]''','boundary_reference_scope_subprefix'),
('cross_context_same_fvar_cycle','''withLocalDeclD `x (mkConst ``True) fun x => do
  let h ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq h h)).mvarId!
  let r ← boundaryExpressionReferenceContext [g] {}
  let ctx ← getMCtx
  let some hd := ctx.decls.find? h.mvarId! | throwError "fixture missing h"
  let some gd := ctx.decls.find? g | throwError "fixture missing g"
  let hiddenType := mkLet `unused (mkConst ``True) (mkMVar g) (mkConst ``True)
  let hd := {hd with lctx := hd.lctx.setType x.fvarId! hiddenType}
  let gd := {gd with type := mkConst ``True}
  let ctx := {ctx with decls := (ctx.decls.insert h.mvarId! hd).insert g gd}
  setMCtx ctx
  let use ← protectBoundaryReferences {r with before := ctx} #[h]
  use.checkAt g #[x, h]''','boundary_reference_occurs'),
('local_let_value_cycle','''withLetDecl `x (mkConst ``True) (mkConst ``True.intro) fun x => do
  let h ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq h h)).mvarId!
  let r ← boundaryExpressionReferenceContext [g] {}
  let ctx ← getMCtx
  let some hd := ctx.decls.find? h.mvarId! | throwError "fixture missing h"
  let some gd := ctx.decls.find? g | throwError "fixture missing g"
  let lctx := hd.lctx.modifyLocalDecl x.fvarId! fun d => match d with
    | .ldecl i id n t _ nd k => .ldecl i id n t (mkMVar g) nd k
    | other => other
  let ctx := {ctx with decls := (ctx.decls.insert h.mvarId! {hd with lctx}).insert g {gd with type := mkConst ``True}}
  setMCtx ctx
  let use ← protectBoundaryReferences {r with before := ctx} #[h]
  use.checkAt g #[x, h]''','boundary_reference_occurs'),
('scope_changed_type','''withLocalDeclD `x (mkConst ``True) fun x => do
  let h ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq h h)).mvarId!
  let r ← boundaryExpressionReferenceContext [g] {}
  let ctx ← getMCtx
  let some hd := ctx.decls.find? h.mvarId! | throwError "fixture missing h"
  let hd := {hd with lctx := hd.lctx.setType x.fvarId! (mkConst ``Nat)}
  let ctx := {ctx with decls := ctx.decls.insert h.mvarId! hd}
  setMCtx ctx
  let use ← protectBoundaryReferences {r with before := ctx} #[h]
  use.checkAt g #[h]''','boundary_reference_scope_type_or_value'),

]

# These controls reach production encoded entrypoints with CLOSED v3 evidence
# and a naturally synthesizable instance hole only in the current goal. A
# barrier conditional on nonempty expression references would fail these.
CLOSED_SYNTH = '''let instType := mkApp (mkConst ``Inhabited [.succ .zero]) (mkConst ``Nat)
let inst ← mkFreshExprMVar instType .synthetic
let candidate := mkApp2 (mkConst ``Inhabited.default [.succ .zero]) (mkConst ``Nat) inst
let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq candidate (mkNatLit 0))).mvarId!
setGoals [g]
let r ← boundaryExpressionReferenceContext [g] (← getThe Term.State)
let input ← encodeBoundaryExprWithReferences (← mkEq (mkNatLit 0) (mkNatLit 0)) r
let literal := Syntax.mkStrLit input
__INVOKE__'''
CASES += [
('encoded_target_no_pending_synthesis', CLOSED_SYNTH.replace('__INVOKE__',
    'let evidence ← `(boundaryEncodedEvidence| ($literal:str ==> $literal:str))\nrunExplicitEncodedApply #[] evidence'), 'boundary_target_input_mismatch'),
('encoded_location_no_pending_synthesis', CLOSED_SYNTH.replace('__INVOKE__',
    'let target ← `(boundaryEncodedTargetEvidence| ⊢ ($literal:str ==> $literal:str))\nrunExplicitEncodedLocationApply #[] #[] (some target)'), 'boundary_target_input_mismatch'),
('encoded_visible_reference', '''setGoals [goal]
let bad := Syntax.mkStrLit <| (Json.arr #[.str "expr_dag_v3", toJson refs.universes.size, toJson refs.mvars.size, .arr #[.arr #[.str "v", toJson (0 : Nat)]], toJson (0 : Nat)]).compress
let evidence ← `(boundaryEncodedEvidence| ($bad:str ==> $bad:str))
runExplicitEncodedApply #[] evidence''', 'boundary_reference_ineligible'),
('observational_reference_table', '''let first ← mkFreshExprMVar (mkSort .zero)
let second ← mkFreshExprMVar (mkSort .zero)
first.mvarId!.assign second
second.mvarId!.assign (mkConst ``True)
let h ← mkFreshExprSyntheticOpaqueMVar first
let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq h h)).mvarId!
let before ← getMCtx
discard <| boundaryExpressionReferenceContext [g] {}
let after ← getMCtx
unless sameExprOption (before.eAssignment.find? first.mvarId!) (after.eAssignment.find? first.mvarId!) do
  throwError "reference table observation changed raw assignment"''',None),
]

SCOPE = '''withLocalDeclD `x (mkConst ``True) fun x => do
  let h ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq h h)).mvarId!
  let r ← boundaryExpressionReferenceContext [g] {}
  let ctx ← getMCtx
  let some hd := ctx.decls.find? h.mvarId! | throwError "fixture missing h"
  __CHANGE__
  let ctx := {ctx with decls := ctx.decls.insert h.mvarId! hd}
  setMCtx ctx
  let use ← protectBoundaryReferences {r with before := ctx} #[h]
  use.checkAt g #[h]'''
CASES += [
('scope_binder_shape', SCOPE.replace('__CHANGE__', 'let hd := {hd with lctx := hd.lctx.modifyLocalDecl x.fvarId! fun d => d.setBinderInfo .implicit}'), 'boundary_reference_scope_shape'),
('scope_local_kind', SCOPE.replace('__CHANGE__', 'let hd := {hd with lctx := hd.lctx.modifyLocalDecl x.fvarId! fun d => d.setKind .implDetail}'), 'boundary_reference_scope_shape'),
('scope_local_instances', SCOPE.replace('__CHANGE__', 'let hd := {hd with localInstances := #[{className := ``True, fvar := x}]}'), 'boundary_reference_scope_instances'),
('scope_let_nondep', SCOPE.replace('withLocalDeclD `x (mkConst ``True)', 'withLetDecl `x (mkConst ``True) (mkConst ``True.intro)').replace('__CHANGE__', 'let lctx := hd.lctx.modifyLocalDecl x.fvarId! fun d => match d with\n    | .ldecl i id n t v nd k => .ldecl i id n t v (!nd) k\n    | other => other\n  let hd := {hd with lctx}'), 'boundary_reference_scope_nondep'),
]

# A nondependent let hides its value from LocalDecl.value?'s default API.
# Both graph traversal and the exact saved-context witness must still see it.
let_cycle = next(body for label,body,_ in CASES if label == 'local_let_value_cycle')
CASES.append(('nondep_hidden_value_cycle', let_cycle.replace('t (mkMVar g) nd k', 't (mkMVar g) true k'), 'boundary_reference_occurs'))
CASES.append(('nondep_hidden_value_snapshot', '''withLetDecl `x (mkConst ``Nat) (mkNatLit 0) fun x => do
  let h ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq h h)).mvarId!
  let r ← boundaryExpressionReferenceContext [g] {}
  let ctx ← getMCtx
  let some hd := ctx.decls.find? h.mvarId! | throwError "fixture missing h"
  let lctx := hd.lctx.modifyLocalDecl x.fvarId! fun d => match d with
    | .ldecl i id n t v _ k => .ldecl i id n t v true k
    | other => other
  let hd := {hd with lctx}
  let ctx := {ctx with decls := ctx.decls.insert h.mvarId! hd}
  setMCtx ctx
  let use ← protectBoundaryReferences {r with before := ctx} #[h]
  let lctx := hd.lctx.modifyLocalDecl x.fvarId! fun d => match d with
    | .ldecl i id n t _ nd k => .ldecl i id n t (mkNatLit 1) nd k
    | other => other
  setMCtx {ctx with decls := ctx.decls.insert h.mvarId! {hd with lctx}}
  use.checkUnchanged''', 'boundary_reference_dependency_changed'))

CASES.append(('delayed_dependency_owning_context', '''let (pending, x) ← withLocalDeclD `x (mkConst ``Nat) fun x => do
  let pending ← mkFreshExprSyntheticOpaqueMVar (mkSort .zero)
  return (pending, x)
let bridge ← mkFreshExprMVar (← mkArrow (mkConst ``Nat) (mkSort .zero))
assignDelayedMVar bridge.mvarId! #[x] pending.mvarId!
let h ← mkFreshExprSyntheticOpaqueMVar (mkApp bridge (mkNatLit 0))
let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq h h)).mvarId!
let r ← boundaryExpressionReferenceContext [g] {}
let use ← protectBoundaryReferences r #[h]
use.checkAt g #[h]
use.checkUnchanged''', None))

CALLBACK = '''let inst ← mkFreshExprMVar (mkApp (mkConst ``Inhabited [.succ .zero]) (mkConst ``Nat)) .synthetic
let candidate := mkApp2 (mkConst ``Inhabited.default [.succ .zero]) (mkConst ``Nat) inst
let triggered ← isDefEq candidate (mkNatLit 0)
pure (triggered || (← inst.mvarId!.isAssigned))'''
for guarded in [False, True]:
    label='guarded_realization_callback' if guarded else 'outer_guard_reader_reset'
    call='realizeBoundaryConst' if guarded else 'realizeConst'
    body=f'''withoutBoundaryPendingSynthesis <| {call} ``Nat `Nat.expressionReferenceCallback do
  let observed ← do
    {CALLBACK.replace(chr(10),chr(10)+'    ')}
  unless observed == {str(not guarded).lower()} do throwError "unexpected callback synthesis"
  addDecl (.thmDecl {{name := `Nat.expressionReferenceCallback, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro}})'''
    CASES.append((label,body,None))
CASES.append(('observer_fresh_meta_guard', '''let observed ← runExportMeta (← getEnv) do
  '''+CALLBACK.replace('\n','\n  ')+'''
if observed then throwError "observer callback synthesized a class hole"''',None))
CASES.append(('nested_realization_callback', '''realizeBoundaryConst ``Nat `Nat.expressionReferenceOuter do
  realizeBoundaryConst ``Nat `Nat.expressionReferenceInner do
    let observed ← do
      '''+CALLBACK.replace('\n','\n      ')+'''
    if observed then throwError "nested callback synthesized a class hole"
    addDecl (.thmDecl {name := `Nat.expressionReferenceInner, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro})
  addDecl (.thmDecl {name := `Nat.expressionReferenceOuter, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro})''',None))

CASES.append(('level_dependency_index_changed', '''let u ← mkFreshLevelMVar
let h ← mkFreshExprSyntheticOpaqueMVar (mkSort u)
let g := (← mkFreshExprSyntheticOpaqueMVar (← mkEq h h)).mvarId!
let r ← boundaryExpressionReferenceContext [g] {}
let use ← protectBoundaryReferences r #[h]
let ctx ← getMCtx
let some d := ctx.lDecls.find? u.mvarId! | throwError "fixture missing level"
setMCtx {ctx with lDecls := ctx.lDecls.insert u.mvarId! {d with index := d.index + 1}}
use.checkUnchanged''', 'boundary_reference_level_changed'))

def main():
    parent=ROOT/'.lake/expression-reference';parent.mkdir(exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='controls-',dir=parent));print(work,flush=True)
    before=runtime.input_hashes();runs=[]
    try:
        for label,body,expected in CASES:
            source=work/(label+'.lean');source.write_text(HEADER.replace('__BODY__',body.replace('\n','\n      ')))
            env,nonce=p.replay_subprocess_environment()
            code,output,seconds=m._compile_copy(source,str(ROOT/'.lake/build/lib/libexplicitLean_ExplicitLean.dylib'),120,env=env)
            log=source.with_suffix('.log');log.write_text(output)
            failure=None
            try:p.check_replay_abort_markers(output,expected_nonce=nonce)
            except RuntimeError as error:failure=str(error)
            runs.append({'label':label,'source':str(source),'log':str(log),'nonce':nonce,'exit':code,'expectedAbort':expected,'seconds':seconds})
            assert code==0,(label,output[-3000:])
            if expected:
                assert failure and expected in failure,(label,failure,output[-3000:])
            else:
                assert failure is None and f'EXPRESSION_REFERENCE_OK {nonce}' in output,(label,failure,output[-3000:])
            print(label+': passed',flush=True)
    finally:
        after=runtime.input_hashes()
        (work/'report.json').write_text(json.dumps({'runs':runs,'inputsBefore':before,'inputsAfter':after,'acceptedCoverage':False},indent=2)+'\n')
        assert before==after,'runtime/source drift'
    good=['expr_dag_v3',0,2,[['v',1]],0]
    validate_reference_expr_dag(json.dumps(good))
    for value in [ ['expr_dag_v3',0,2,[['v',2]],0], ['expr_dag_v3',0,True,[['v',0]],0], ['expr_dag_v3',0,2,[['v',1,0]],0], ['expr_dag_v3',0,2,[['v',-1]],0] ]:
        try:validate_reference_expr_dag(json.dumps(value))
        except RuntimeError:pass
        else:raise AssertionError(value)
    for validator in [validate_expr_dag,validate_boundary_expr_dag]:
        try:validator(json.dumps(good))
        except RuntimeError:pass
        else:raise AssertionError('legacy accepted v3')
    # Renderer inputs must be encoded data, never the legacy handwritten term
    # API or a term elaboration program. The variant grammar itself exposes
    # only apply_encoded/apply_encoded_with_actions (and recorded failure).
    for legacy in ['by exact True.intro', 'simp_engine_boundary_apply (True ==> True)']:
        try:p.validate_rendered_term(legacy, 'legacy generated evidence')
        except RuntimeError:pass
        else:raise AssertionError('legacy term source accepted as generated evidence')
    report=json.loads((work/'report.json').read_text())
    report.update(status='passed',artifactSchema=p.ARTIFACT_SCHEMA,reportSchema=m.REPORT_SCHEMA,wireNegatives=8)
    (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'passed {len(runs)} Lean controls and 8 wire negatives; {work}/report.json',flush=True)

if __name__=='__main__':main()
