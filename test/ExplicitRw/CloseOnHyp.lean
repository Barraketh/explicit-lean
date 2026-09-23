import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.CloseOnHyp

/-- A hypothesis rewrite is an ordinary `explicit_rw at h` followed by the
recorded goal closer.  The close runs once, after `h` has become `False`. -/
theorem rewrite_hypothesis_then_close {P : Prop}
    (h : P) (hFalse : P = False) : False := by
  explicit_rw [hFalse at [] ] at h; exact h.elim

end ExplicitRwTest.CloseOnHyp
