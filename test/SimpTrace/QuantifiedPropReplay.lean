import ExplicitLean.SimpTrace
import ExplicitLean.ExplicitRw

namespace ExplicitLean.SimpTrace.QuantifiedPropReplay

inductive FixturePredicate (n : Nat) : Prop where
  | witness : FixturePredicate n

theorem fixtureGlobal (n : Nat) : FixturePredicate n := .witness

example (n : Nat) : FixturePredicate n := by
  simp_trace [fixtureGlobal] =>trace "QUANTIFIED_PROP_GLOBAL_TRACE_PATH"

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  simp_trace [h] =>trace "QUANTIFIED_PROP_LOCAL_TRACE_PATH"

example (P : Nat → Prop) (h : ∀ n, ¬ P n) : P 0 = False := by
  simp_trace [h] =>trace "QUANTIFIED_PROP_FALSE_TRACE_PATH"

end ExplicitLean.SimpTrace.QuantifiedPropReplay
