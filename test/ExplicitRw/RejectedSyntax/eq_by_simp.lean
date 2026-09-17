import ExplicitLean.ExplicitRw
example : (2 + 3) + 1 = 6 := by
  explicit_rw [eq (2 + 3 = 5) by simp at [0, 1, 0, 1]]
