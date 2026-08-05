-- A pattern-matching lambda. Ordinary `fun x => e` is accepted; only the
-- alternatives form is rejected.
set_option autoImplicit false

def classify : Nat → Nat := fun
  | 0 => 0
  | _ => 1
