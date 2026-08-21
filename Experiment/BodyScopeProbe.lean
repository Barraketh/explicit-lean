import Mathlib
import ExplicitLean.SimpExplicit

/- Each source occurrence is given an explicit stable id so the checker can
   verify that dynamic executions are grouped by occurrence, not by report
   line order.  These are intentionally source-level probes for the internal
   body-scope wrapper; F2 will consume the per-execution certificates. -/

example (n : Nat) : n + 0 = n ∧ n + 0 = n := by
  simp_explicit_body_scope "f1-shared-body" in
    constructor <;>
      set_option explicitLean.simpExplicit.passive true in
        set_option explicitLean.simpExplicit.occurrenceId "f1-shared" in
          simp_explicit?

example (n : Nat) : n + 0 = n ∧ n + 0 = n := by
  simp_explicit_body_scope "f1-all-goals-body" in
    constructor
    all_goals
      set_option explicitLean.simpExplicit.passive true in
        set_option explicitLean.simpExplicit.occurrenceId "f1-all-goals" in
          simp_explicit?

example (n : Nat) : (n + 0 = n) ∧ ((n + 0 = n) ∧ (n + 0 = n)) := by
  simp_explicit_body_scope "f1-repeat-body" in
    constructor <;>
      repeat
        set_option explicitLean.simpExplicit.passive true in
          set_option explicitLean.simpExplicit.occurrenceId "f1-repeat" in
            simp_explicit?

axiom f1ProbeP : Prop

example (h : f1ProbeP) (n : Nat) : n + 0 = n ∧ f1ProbeP := by
  simp_explicit_body_scope "f1-first-body" in
    first
    | (set_option explicitLean.simpExplicit.passive true in
        set_option explicitLean.simpExplicit.occurrenceId "f1-first" in
          simp_explicit? only [Nat.add_zero]; fail)
    | set_option explicitLean.simpExplicit.passive true in
        set_option explicitLean.simpExplicit.occurrenceId "f1-first" in
          simp_explicit? [h]
