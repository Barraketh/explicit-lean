-- A multi-line elaboration error, checking that a forwarded Lean message keeps
-- one diagnostic on one unindented line.
set_option autoImplicit false

def bad : Nat := "not a nat"
