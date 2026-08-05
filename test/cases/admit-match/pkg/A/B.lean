-- `match` requires G11 canonical-match syntax and generates a same-module
-- matcher auxiliary, neither of which v0 supports.
set_option autoImplicit false

def classify (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | _ => 1
