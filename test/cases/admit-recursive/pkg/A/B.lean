-- A recursive definition. v0 accepts only nonrecursive, nonmutual declarations.
set_option autoImplicit false

def countdown : Nat → Nat
  | 0 => 0
  | (n + 1) => countdown n
