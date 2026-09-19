import Lean

open Lean Elab Term Meta

elab "runStockMetaSimp" : term <= ty => do
  let ty ← instantiateMVars ty
  let g ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ty
  let ctx ← Lean.Meta.Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← Lean.Meta.simpGoal g.mvarId! ctx
  if result.isNone then
    return (← instantiateMVars g)
  throwError "direct Meta simp unexpectedly left a goal"

example (n : Nat) : n + 0 = n := by
  exact runStockMetaSimp
