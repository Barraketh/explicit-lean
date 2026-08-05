-- Nonrecursive `let`, projections, and a type ascription: completed term forms
-- v0 accepts. Within this accepted set stock Lean produces no same-module
-- generated auxiliaries, so `declarations` counts only the source declarations.
set_option autoImplicit false

def withLet (n : Nat) : Nat :=
  let doubled := n + n
  doubled + 1

def usesLet : Nat := withLet 3

def ascribed : Nat := (2 : Nat)

def projected (p : Nat × Nat) : Nat := p.fst
