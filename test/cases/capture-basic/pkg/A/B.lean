-- Simple nonrecursive definitions and a dependency between them.
set_option autoImplicit false

def one : Nat := 1

def two : Nat := Nat.succ one

abbrev alsoTwo : Nat := two

opaque hidden : Nat
