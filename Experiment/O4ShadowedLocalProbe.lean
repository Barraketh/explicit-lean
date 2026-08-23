import ExplicitLean.SimpExplicit

opaque shadowedLocalNat : Nat := 0
axiom shadowedLocalRule (h : ∀ k : Nat, k = k → False) :
  shadowedLocalNat + 0 = shadowedLocalNat

/- The premise discharger selects the older proposition-valued `h`, not the
   newer let declaration with the same source name. The certificate must keep
   that identity without relying on name resolution. -/
set_option explicitLean.simpExplicit.report true in
example (h : ∀ k : Nat, k = k → False) :
    shadowedLocalNat + 0 = shadowedLocalNat := by
  let h : Nat := 37
  simp_explicit? only [shadowedLocalRule, eq_self]
