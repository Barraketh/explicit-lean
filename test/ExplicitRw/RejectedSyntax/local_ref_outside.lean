import ExplicitLean.ExplicitRw

-- `local_ref` belongs only to the closed `explicit_rw` grammar, not to Lean's
-- ordinary term grammar; there is no public option that can enable it here.
example (a : Nat) : a = a := by
  exact local_ref 1
