import ExplicitLean.ExplicitRw

open ExplicitLean.ExplicitRw

theorem t1 (a b : Nat) (h : a = b) : a + 0 = b + 0 := by
  explicit_rw [h at [0, 1]]
  rfl

#print axioms t1
