-- The general term form is delimited, then checked before term elaboration.
-- Even a theorem proof that would close this goal must not run inside a trace.
import ExplicitLean.ExplicitRw

example (p : Prop) : p := by
  explicit_rw [lean_term((by simp)) at []]
