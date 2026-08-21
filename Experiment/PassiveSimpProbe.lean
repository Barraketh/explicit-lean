module

import ExplicitLean.SimpExplicit

set_option linter.unusedVariables false

example (n : Nat) (h : n + 0 = n) : True := by
  set_option explicitLean.simpExplicit.passive true in
  set_option explicitLean.simpExplicit.occurrenceId "location" in
  simp_explicit? at h
  trivial

example : (1 : Nat) + 0 = 1 := by
  set_option explicitLean.simpExplicit.passive true in
  set_option explicitLean.simpExplicit.occurrenceId "configuration" in
  simp_explicit? (config := { zeta := false })
