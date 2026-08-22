import ExplicitLean.SimpExplicit

/- A small source-level gate for a theorem local introduced by implication
   traversal.  Slot 1 is the binder hypothesis in the callback context. -/
example (P : Prop) : P → P := by
  simp_explicit [local_rule 1, implies_true]
