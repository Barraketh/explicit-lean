/-
`simp_trace`: record stock simp's step trace in the `simp-trace-v1` format.

Recorder machinery only; never imported by translated Mathlib source.
-/
module

public meta import ExplicitLean.SimpTrace.Types
public meta import ExplicitLean.SimpTrace.Traversal
public meta import ExplicitLean.SimpTrace.Recorder
public meta import ExplicitLean.SimpTrace.Position
public meta import ExplicitLean.SimpTrace.Tactic
