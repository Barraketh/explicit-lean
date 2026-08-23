import ExplicitLean.SimpExplicit

structure O6iDefault where
  value : Nat

instance : Inhabited O6iDefault := ⟨⟨7⟩⟩

/- The named class projection is its own unfolding authorization.  Deletion,
   substitution, and reordering must still fail closed. -/
example : (default : O6iDefault) = ⟨7⟩ := by
  fail_if_success simp_explicit [eq_self]
  fail_if_success
    simp_explicit [reduce projection_fn O6iDefault.value, eq_self]
  fail_if_success
    simp_explicit [eq_self, reduce projection_fn Inhabited.default]
  simp_explicit [reduce projection_fn Inhabited.default, eq_self]
