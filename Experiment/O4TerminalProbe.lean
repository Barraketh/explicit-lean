import ExplicitLean.SimpExplicit

opaque localTerminalNat : Nat := 0
axiom localTerminalRule (h : ∀ k : Nat, k = k → False) :
  localTerminalNat + 0 = localTerminalNat

set_option explicitLean.simpExplicit.report true in
example (h : ∀ k : Nat, k = k → False) :
    localTerminalNat + 0 = localTerminalNat := by
  simp_explicit? only [localTerminalRule, eq_self]

opaque equationTerminalNat : Nat := 0
axiom equationTerminalRule (h : ∀ k : Nat, Nat.succ k = 0 → False) :
  equationTerminalNat + 0 = equationTerminalNat

set_option explicitLean.simpExplicit.report true in
example : equationTerminalNat + 0 = equationTerminalNat := by
  simp_explicit? only [equationTerminalRule, eq_self]

opaque rflTerminalNat : Nat := 0
axiom rflTerminalRule {f : Nat → Nat} (h : ∀ x : Nat, 0 = f x) :
  rflTerminalNat + 0 = rflTerminalNat

set_option explicitLean.simpExplicit.report true in
example : rflTerminalNat + 0 = rflTerminalNat := by
  simp_explicit? only [rflTerminalRule, eq_self]

/- The fixed terminal primitive is not a general reflexivity search.  A
   closed residual with the wrong terminal selector must be rejected, while
   the recorded dischargeRfl primitive reconstructs its fixed proof. -/
example : ∀ _x : Nat, (0 : Nat) = 0 := by
  fail_if_success simp_explicit_premise equationHypothesis
  simp_explicit_premise dischargeRfl

/- Provider order and premise consumption remain part of replay. -/
example : rflTerminalNat + 0 = rflTerminalNat := by
  fail_if_success simp_explicit [rflTerminalRule using [], eq_self]
  simp_explicit [rflTerminalRule using
    [show ∀ _x : Nat, (0 : Nat) = 0 from by intro _x; rfl], eq_self]
