-- A `let rec` binding.
set_option autoImplicit false

def usesLetRec : Nat :=
  let rec helper : Nat := 1
  helper
