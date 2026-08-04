-- A single command that introduces many constants at once. v0 rejects
-- `structure` at admission, but capture must still inventory the complete
-- environment delta, and this is what pins the canonical name ordering: the
-- underlying map's traversal order is not a stable identity.
set_option autoImplicit false

structure Point where
  x : Nat
  y : Nat
