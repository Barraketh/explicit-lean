import ExplicitLean.SimpExplicit

/-! Focused O6e projection-function replay and recorder fixtures. -/

structure O6eProjectionRecord where
  value : Nat

structure O6eOtherProjection where
  value : Nat

example (n : Nat) : O6eProjectionRecord.value { value := n } = n := by
  simp_explicit [reduce projection_fn O6eProjectionRecord.value]

set_option explicitLean.simpExplicit.report true in
example (n : Nat) : O6eProjectionRecord.value { value := n } = n := by
  simp_explicit?

example (n : Nat) : O6eProjectionRecord.value { value := n } = n := by
  fail_if_success simp_explicit []
  exact rfl

example (n : Nat) : O6eProjectionRecord.value { value := n } = n := by
  fail_if_success simp_explicit [reduce projection_fn O6eOtherProjection.value]
  exact rfl
