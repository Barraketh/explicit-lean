-- A deriving clause.
set_option autoImplicit false

inductive Flag where
  | on
  | off
  deriving Repr
