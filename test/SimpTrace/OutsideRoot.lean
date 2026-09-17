/-
Negative fixture: `with_trace` must refuse a path outside the package root.

Compiling this file must FAIL with the containment error and must not create
`/tmp/simp_trace_escape_check.json`.  `Experiment/check_simp_trace.py` asserts
both.  A tactic that writes files must not be able to write anywhere.
-/
import ExplicitLean.SimpTrace
import Mathlib.Algebra.Order.Group.Nat

example (a : Nat) : a + 0 = a := by
  simp_trace with_trace "/tmp/simp_trace_escape_check.json"
