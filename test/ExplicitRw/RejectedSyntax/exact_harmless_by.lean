-- Even a harmless `by` is refused: the rule is about tactics in terms, not
-- about which tactic it happens to be.
import ExplicitLean.ExplicitRw
example (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then exact (id (by rfl))
