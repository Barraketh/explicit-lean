-- The same attack via `Tactic.run` + `evalTactic simp`.
import ExplicitLean.ExplicitRw
import Mathlib.Logic.Basic
open Lean Elab Term Meta
elab "SmuggleRun" : term <= ty => do
  let ty ← instantiateMVars ty
  let g ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ty
  _ ← Lean.Elab.Tactic.run g.mvarId! (Lean.Elab.Tactic.evalTactic (← `(tactic| simp)))
  return (← instantiateMVars g)
example (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then exact SmuggleRun
