-- Term-style proofs: theorems whose values are proof terms rather than tactic
-- blocks, including a use of an imported proof.
set_option autoImplicit false

def n : Nat := 2

theorem nEqTwo : n = 2 := rfl

theorem symmNEqTwo : 2 = n := Eq.symm nEqTwo

theorem transTrivial : n = n := Eq.trans nEqTwo (Eq.symm nEqTwo)
