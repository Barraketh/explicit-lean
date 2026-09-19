import ExplicitLean.Grind.Metadata

-- This definition has equations, so rejection must come from the command's
-- exact-name guard rather than the generic equation lookup.
def unrelatedDefinition (n : Nat) : Nat := n + 1

explicit_grind_def unrelatedDefinition
