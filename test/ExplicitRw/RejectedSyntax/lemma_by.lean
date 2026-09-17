-- A `by` block in a lemma term.
import ExplicitLean.ExplicitRw
example (a : Nat) : a + 0 = a := by
  explicit_rw [(by simp : a + 0 = a) at []]
