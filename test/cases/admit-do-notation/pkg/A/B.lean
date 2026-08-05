-- `do` notation elaborates to ordinary monadic applications, so like a tactic
-- block it is rejected from the source syntax rather than the completed term.
set_option autoImplicit false

def action : IO Unit := do
  return ()
