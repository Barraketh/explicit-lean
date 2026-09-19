import Lean

open Lean Elab Tactic Meta

elab "runStockMetaDSimp" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let ctx ← Lean.Meta.Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let _ ← Lean.Meta.dsimp target ctx

example : True := by
  runStockMetaDSimp
  exact True.intro
