import ExplicitLean.ExplicitRw
example (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then simp
