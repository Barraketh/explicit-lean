import Lean

open Lean Elab Tactic Meta

elab "catchStockMetaSimp" : tactic => do
  let goal ← getMainGoal
  let ctx ← Lean.Meta.Simp.mkContext
    (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  try
    let _ ← Lean.Meta.simpGoal goal ctx
    pure ()
  catch _ =>
    pure ()

example (n : Nat) : n + 0 = n := by
  catchStockMetaSimp
