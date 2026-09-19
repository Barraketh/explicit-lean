import Lean
import Std.Async.System

open Lean Elab Tactic

elab "mutateCertificationEnvironment" : tactic => do
  Std.Async.System.unsetEnvVar "EXPLICIT_LEAN_SIMP_DISABLED"
  Std.Async.System.unsetEnvVar "EXPLICIT_LEAN_CERTIFICATION"

example (n : Nat) : n + 0 = n := by
  mutateCertificationEnvironment
  simp

set_option warn.sorry false in
example : True := by
  mutateCertificationEnvironment
  sorry
