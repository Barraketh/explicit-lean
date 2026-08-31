import ExplicitLean.SimpEngine.Boundary.ExprCodec
import Lean.Elab.Tactic
import Lean.Meta.Check

set_option linter.unusedVariables false

open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

elab "codec_roundtrip " value:term : tactic => withMainContext do
  let expr ← elabTerm value none
  runTermElab Term.synthesizeSyntheticMVarsNoPostponing
  let expr ← instantiateMVars expr
  let source ← encodeBoundaryExpr expr
  let saved ← getTraceState
  modifyTraceState fun state => { state with traces := {} }
  let decoded ← withOptions (·.setBool `trace.Meta.synthInstance true) do
    let decoded ← decodeBoundaryExpr source
    check decoded
    pure decoded
  let traces := (← getTraceState).traces.toArray
  modifyTraceState fun _ => saved
  unless traces.isEmpty do throwError "decoder triggered instance search"
  unless ← isDefEq expr decoded do throwError "roundtrip changed expression"
  unless (← encodeBoundaryExpr decoded) == source do throwError "unstable expression encoding: {source} != {← encodeBoundaryExpr decoded}"

example (α : Type u) (x : α) : True := by
  codec_roundtrip (fun (y : α) => (x, y))
  codec_roundtrip (∀ (y : α), y = x)
  codec_roundtrip (let y := x; (y, y))
  codec_roundtrip (37 : Nat)
  codec_roundtrip "hello"
  exact True.intro

example [inst : Inhabited α] : True := by
  codec_roundtrip (@Inhabited.default α inst)
  exact True.intro

run_meta do
  for source in ["[\"expr_dag_v1\",[[\"a\",0,0]],0]",
      "[\"expr_dag_v1\",[[\"f\",999999]],0]",
      "[\"expr_dag_v1\",[[\"tactic\",\"simp\"]],0]",
      "[\"expr_dag_v1\",[[\"c\",[[\"s\",\"sorryAx\"]],[]]],0]",
      "[\"expr_dag_v1\",[[\"s\",[\"mvar\",0]]],0]"] do
    let rejected ← try
      discard <| decodeBoundaryExpr source
      pure false
    catch _ => pure true
    unless rejected do throwError "malformed expression was accepted"
  let expr ← mkFreshExprMVar none
  let rejected ← try
    discard <| encodeBoundaryExpr expr
    pure false
  catch _ => pure true
  unless rejected do throwError "unresolved metavariable was encoded"
  let expr := mkSort (← mkFreshLevelMVar)
  let rejected ← try
    discard <| encodeBoundaryExpr expr
    pure false
  catch _ => pure true
  unless rejected do throwError "unresolved universe was encoded"

  -- Name components distinguish numeric fields from textual digits.
  let name := Name.num (.str (.str .anonymous "a.b") "1") 2
  let .ok decodedName := decodeBoundaryName (encodeBoundaryName name)
    | throwError "name roundtrip failed"
  unless name == decodedName do throwError "name components changed"
  let expr := mkConst name []
  let rejected ← try
    discard <| decodeBoundaryExpr (← encodeBoundaryExpr expr)
    pure false
  catch _ => pure true
  unless rejected do throwError "unavailable constant was accepted"
  let projection := mkProj ``Prod 0 (mkBVar 0)
  let decoded ← decodeBoundaryExpr (← encodeBoundaryExpr projection)
  unless projection == decoded do throwError "projection changed"
