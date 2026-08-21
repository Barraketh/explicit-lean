module

import Mathlib

/- The `simp` body is nested in a structure field and follows another tactic.
   Passive whole-body instrumentation must preserve its relative indentation
   when it inserts the body-scope and option wrappers. -/

structure BodyIndentationProbe where
  value : Nat
  property : (fun _ : Unit => value + 0) = fun _ => value

def bodyIndentationProbe (n : Nat) : BodyIndentationProbe :=
  { value := n
    property := by
      funext _
      simp }
