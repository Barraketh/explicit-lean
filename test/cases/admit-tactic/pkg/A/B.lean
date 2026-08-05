-- A tactic proof. Its completed value is indistinguishable from a term proof,
-- so this can only be rejected from the source syntax.
set_option autoImplicit false

theorem viaTactic : 1 = 1 := by rfl
