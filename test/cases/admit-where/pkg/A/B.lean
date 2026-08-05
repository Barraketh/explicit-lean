-- A `where` clause, which introduces an auxiliary declaration v0 cannot
-- correlate.
set_option autoImplicit false

def usesWhere : Nat := helper
where
  helper : Nat := 1
