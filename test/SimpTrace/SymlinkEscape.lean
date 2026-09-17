/-
Negative fixture: a symlink under the package root must not defeat containment.

`Experiment/check_simp_trace.py` creates `test/SimpTrace/linkescape -> /tmp`,
compiles this file, and requires it to FAIL with the containment error and to
leave `/tmp/simp_trace_symlink_check.json` uncreated. Textual `..` collapsing
does not see through a symlink, so containment compares resolved paths.
-/
import ExplicitLean.SimpTrace
import Mathlib.Algebra.Order.Group.Nat

example (a : Nat) : a + 0 = a := by
  simp_trace =>trace "test/SimpTrace/linkescape/simp_trace_symlink_check.json"
