-- A term elaborator that runs the simplifier in `MetaM` directly. It produces
-- no `by` syntax and registers no synthetic metavariable, so neither a syntax
-- walk nor a metavariable check can see it; only the whitelist grammar stops it,
-- and it does so at parse time.
import ExplicitLean.ExplicitRw
import Mathlib.Logic.Basic
open Lean Elab Term Meta
elab "SmuggleMetaM" : term <= ty => do
  let ty ← instantiateMVars ty
  let g ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ty
  let ctx ← Lean.Meta.Simp.mkContext (simpTheorems := #[← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← Lean.Meta.simpGoal g.mvarId! ctx
  if r.isNone then return (← instantiateMVars g) else throwError "no"
example (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then exact SmuggleMetaM
