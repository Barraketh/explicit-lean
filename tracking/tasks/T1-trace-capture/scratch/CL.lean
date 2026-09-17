import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
set_option linter.unusedVariables false
namespace CL
example (a : Nat) (h : a ≠ a) : False := by
  simp_trace (out := "tracking/tasks/T1-trace-capture/scratch/false_hyp.json") at h
end CL
