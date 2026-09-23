import ExplicitLean.SimpTrace
import ExplicitLean.ExplicitRw
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

open Lean Lean.Meta

namespace ExplicitLean.SimpTrace.T77NeZeroSourceEvidence

/-- An irrelevant explicit argument must remain visible to the validator. -/
private theorem neZeroWithUnusedArgument (_ignored : Nat) {n : Nat} [NeZero n] : n ≠ 0 :=
  NeZero.ne n

example {n : ℕ} [NeZero n] : ¬ n < 1 := by
  simp_trace [NeZero.ne _] =>trace "T77_NEZERO_SOURCE_TRACE_PATH"

example (n : ℕ) : 0 ≤ n := by
  simp_trace only [Nat.zero_le _] =>trace "T77_PROP_TRUE_SOURCE_TRACE_PATH"

/- A different proposition cannot be accepted just because the source value
   has already been converted to an equality ending in `False`. -/
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let zero := mkNatLit 0
    let before ← mkEq zero zero
    let reason ← checkRwStep (.decl ``Nat.succ_ne_zero true false) #[] false
      (some false) before (mkConst ``False) {} false ""
      (some (mkConst ``Nat.succ_ne_zero))
    unless reason.any (String.startsWith · "unreplayable_rw:") do
      throwError "a mismatched source proposition was accepted"

/- The source value still cannot invent an unrelated non-class explicit
   argument, even when its proposition matches the selected redex. -/
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let zero := mkNatLit 0
    let before ← mkEq zero zero
    let reason ← checkRwStep (.decl ``neZeroWithUnusedArgument true false) #[]
      false (some false) before (mkConst ``False) {} false ""
      (some (mkConst ``neZeroWithUnusedArgument))
    unless reason.any (String.startsWith · "unassigned_explicit_argument:") do
      throwError "expected a missing explicit argument to fail closed, got {reason}"

end ExplicitLean.SimpTrace.T77NeZeroSourceEvidence
