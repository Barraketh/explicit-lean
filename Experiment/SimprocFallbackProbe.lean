import ExplicitLean.SimpExplicit
import Mathlib.Tactic.Push

/- `pushFun` is a registered simp simproc.  The report is checked by the
   harness for a generated fallback with the `simproc` reason; the resulting
   suggestion is then materialized and compiled by the same harness. -/
example : (fun x : Nat => x) = (id : Nat → Nat) := by
  set_option explicitLean.simpExplicit.report true in
  simp_explicit? [↓pushFun]
