import ExplicitLean.SimpOperations.Recording

open Lean Elab Tactic

namespace ExplicitLean.SimpTrace.T79OperationalRecording

/- The observer does not replace the goal.  It records the exact `Nat.add_zero`
operation separately, then the ordinary proof below closes the unchanged goal. -/
example (n : Nat) : n + 0 = n := by
  simp_operations_observe only [Nat.add_zero]
  exact Nat.add_zero n

/- The database retry path labels a trace with the exact source-site ordinal.
   The label is a log prefix, not part of the serialized operation record. -/
example (n : Nat) : n + 0 = n := by
  simp_operations_observe_at 17 only [Nat.add_zero]
  exact Nat.add_zero n

/- A nested occurrence exercises the raw application-child position recorder. -/
example (n : Nat) : (n + 0, n) = (n, n) := by
  simp_operations_observe only [Nat.add_zero]
  exact congrArg (fun value => (value, n)) (Nat.add_zero n)

/- Definitional engine operations use the same position channel. -/
example (n : Nat) : (fun x : Nat => x) n = n := by
  simp_operations_observe only
  rfl

/- A contextual local rewrite records only the context index needed by
`local_ref`; it is not a source-syntax rule argument. -/
example (p : Prop) : p → p := by
  simp_operations_observe (config := { contextual := true }) only
  intro h
  exact h

/- Metadata is a real expression child and therefore contributes child `0` to
the exact raw position. -/
elab "wrap_operations_mdata" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let wrapped := Expr.mdata
    (KVMap.empty.insert `explicitRwV2Test (DataValue.ofBool true)) target
  replaceMainGoal [← goal.replaceTargetDefEq wrapped]

example (n : Nat) : n + 0 = n := by
  wrap_operations_mdata
  simp_operations_observe only [Nat.add_zero]
  exact Nat.add_zero n

/- A nontrivial simp argument is retained as parser syntax. The operation
stream does not serialize the elaborated proof application. -/
example (n : Nat) : n + 0 = n := by
  simp_operations_observe only [Nat.add_zero n]
  exact Nat.add_zero n

example (n : Nat) : n + 1 = Nat.succ n := by
  simp_operations_observe only [← Nat.succ_eq_add_one n]
  exact (Nat.succ_eq_add_one n).symm

private def nestedPremiseProp (n : Nat) : Prop := n + 0 = n

private theorem nestedPremiseRule (n : Nat) (h : n + 0 = n) : nestedPremiseProp n := h

example (n : Nat) : nestedPremiseProp n := by
  simp_operations_observe only [nestedPremiseRule, Nat.add_zero]
  exact Nat.add_zero n

/- `Meta.simpHaveTelescope` invokes simplification through `MonadSimp`; the
recorder must retain the exact raw child path of the have value and body. -/
example (n : Nat) : (have x := n + 0; x) = n := by
  simp_operations_observe (config := { zeta := false, zetaUnused := false }) only [Nat.add_zero]
  exact Nat.add_zero n

end ExplicitLean.SimpTrace.T79OperationalRecording
