-- Recursion written without equation syntax. The syntax-level checks do not
-- fire here, so this is what pins the self-reference check on the completed
-- value. The constant reported is an auxiliary Lean generates while compiling
-- the recursion, not one this source wrote.
set_option autoImplicit false

def countdown (n : Nat) : Nat :=
  if n = 0 then 0 else countdown (n - 1)
termination_by n
