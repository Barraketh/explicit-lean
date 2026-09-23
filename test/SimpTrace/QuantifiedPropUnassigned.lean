import ExplicitLean.SimpTrace

namespace ExplicitLean.SimpTrace.QuantifiedPropUnassigned

inductive FixturePredicate (n : Nat) : Prop where
  | witness : FixturePredicate n

theorem fixtureNeedsValue (n : Nat) (_k : Nat) : FixturePredicate n := .witness

example (n : Nat) : FixturePredicate n := by
  simp_trace [fixtureNeedsValue] =>trace "QUANTIFIED_PROP_UNASSIGNED_TRACE_PATH"

end ExplicitLean.SimpTrace.QuantifiedPropUnassigned
