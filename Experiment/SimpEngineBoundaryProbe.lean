import ExplicitLean.SimpEngine.Boundary

set_option autoImplicit false

open Lean Meta Elab Tactic

/-- An intentionally reducible wrapper for the definitional-transport case. -/
def boundaryAlias (n : Nat) : Nat := n

/-- A proposition not definitionally equal to `True`, used to force a custom
    discharger through a conditional simplification theorem. -/
inductive BoundaryConditionalBox : Prop where
  | intro

theorem boundaryConditionalBox_eq (_ : True) : BoundaryConditionalBox ↔ True :=
  ⟨fun _ => True.intro, fun _ => .intro⟩

class BoundaryPendingClass : Prop where
  intro : True

instance : BoundaryPendingClass := ⟨True.intro⟩

def boundaryPersistentTagTarget : Nat := 0

syntax "boundary_insert_assignment_goal" : tactic
syntax "boundary_assign_preexisting_mvars" : tactic
syntax "boundary_pending_typeclass_probe" : tactic
syntax "boundary_postponed_constraint_probe" : tactic
syntax "boundary_mutate_persistent_extension" : tactic

elab_rules : tactic
  | `(tactic| boundary_insert_assignment_goal) => withMainContext do
      let goals ← getGoals
      let level ← mkFreshLevelMVar
      let typeMVar ← mkFreshExprMVar (some (mkSort level))
      withLocalDeclD `boundaryAssignmentCarrier typeMVar fun _ => do
        let continuation ← mkFreshExprMVar (some typeMVar) .syntheticOpaque
        let auxiliary ← mkFreshExprMVar (some (mkConst ``BoundaryConditionalBox))
          .syntheticOpaque
        setGoals (auxiliary.mvarId! :: continuation.mvarId! :: goals)
  | `(tactic| boundary_assign_preexisting_mvars) => withMainContext do
      let some carrier := (← getLCtx).findFromUserName? `boundaryAssignmentCarrier
        | throwError "missing pre-existing assignment carrier"
      let typeMVarId := carrier.type.mvarId!
      let typeDecl ← typeMVarId.getDecl
      let levelMVarId := typeDecl.type.sortLevel!.mvarId!
      assignLevelMVar levelMVarId .zero
      typeMVarId.assign (mkConst ``True)
      let goal ← getMainGoal
      goal.assign (mkConst ``True.intro)
      replaceMainGoal []
  | `(tactic| boundary_pending_typeclass_probe) => withMainContext do
      let synthetic ← mkFreshExprMVar (some (mkConst ``BoundaryPendingClass))
        .syntheticOpaque
      Term.registerSyntheticMVarWithCurrRef synthetic.mvarId! (.typeClass none)
      unless (← getThe Term.State).pendingMVars.contains synthetic.mvarId! do
        throwError "pending synthetic metavariable was not registered"
      evalTactic (← `(tactic| simp_engine_boundary_probe only [Nat.add_zero]))
      unless (← getThe Term.State).pendingMVars.contains synthetic.mvarId! do
        throwError "boundary apply consumed a stock-preserved pending metavariable"
      if ← synthetic.mvarId!.isAssigned then
        throwError "boundary apply assigned a stock-preserved pending metavariable"
  | `(tactic| boundary_postponed_constraint_probe) => withMainContext do
      let saved ← getPostponed
      let ref ← getRef
      modifyPostponed fun postponed => postponed.push {
        ref
        lhs := .zero
        rhs := .zero
        ctx? := none
      }
      evalTactic (← `(tactic| simp_engine_boundary_probe only [Nat.add_zero]))
      unless (← getPostponed).size == saved.size + 1 do
        throwError "boundary apply changed a stock-preserved postponed constraint"
      setPostponed saved
  | `(tactic| boundary_mutate_persistent_extension) => withMainContext do
      Lean.addDocStringCore ``boundaryPersistentTagTarget
        "boundary-only persistent-extension mutation"

-- Equality-proof transport followed by an unchanged continuation.
example (P : Nat → Prop) (n : Nat) (h : P n) : P (n + 0) := by
  simp_engine_boundary_probe only [Nat.add_zero]
  exact h

example : True := by
  simp_engine_boundary_comparator_self_test
  exact True.intro

-- Target closure after simplification proves the target equal to `True`.
example (n : Nat) : n + 0 = n := by
  simp_engine_boundary_probe only [Nat.add_zero]

-- A successful no-op must preserve the original goal metavariable.
example (P : Prop) (h : P) : P := by
  simp_engine_boundary_probe (failIfUnchanged := false) only
  exact h

-- A changed but definitionally equal result exercises proof-free transport.
example (P : Nat → Prop) (n : Nat) (h : P n) : P (boundaryAlias n) := by
  simp_engine_boundary_probe only [boundaryAlias]
  exact h

-- Local declaration ordering and let declarations remain observable.
example (P : Nat → Prop) (n : Nat) (h : P n) :
    let k := n
    P (k + 0) := by
  simp_engine_boundary_probe only [Nat.add_zero]
  exact h

-- The probe changes only the active goal and preserves the ordered goal tail.
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · simp_engine_boundary_probe (failIfUnchanged := false) only
    exact hp
  · exact hq

-- Full scoped options are part of the compared boundary snapshot.
set_option pp.universes true in
example (P : Prop) (h : P) : P := by
  simp_engine_boundary_probe (failIfUnchanged := false) only
  exact h

-- Proof-bearing hypothesis transport leaves a usable hypothesis for the
-- continuation.
example (P : Nat → Prop) (n : Nat) (h : P (n + 0)) : P n := by
  simp_engine_boundary_probe only [Nat.add_zero] at h
  exact h

-- Definitional (proof-free) hypothesis transport keeps the original fvar.
example (P : Nat → Prop) (n : Nat) (h : P (boundaryAlias n)) : P n := by
  simp_engine_boundary_probe only [boundaryAlias] at h
  exact h

-- A combined hypothesis-and-target location preserves both transports.
example (P : Nat → Prop) (n : Nat) (h : P (n + 0)) : P (n + 0) := by
  simp_engine_boundary_probe only [Nat.add_zero] at h ⊢
  exact h

-- Explicitly selected hypotheses are transported in their source order.
example (P Q : Nat → Prop) (n : Nat) (hP : P (n + 0)) (hQ : Q (n + 0)) :
    P n ∧ Q n := by
  simp_engine_boundary_probe only [Nat.add_zero] at hP hQ
  constructor
  · exact hP
  · exact hQ

-- Wildcard location simplifies nondependent propositional hypotheses and the
-- target together.
example (P Q : Nat → Prop) (n : Nat) (hP : P (n + 0)) (hQ : Q (n + 0)) :
    P (n + 0) ∧ Q (n + 0) := by
  simp_engine_boundary_probe only [Nat.add_zero] at *
  constructor <;> assumption

-- A local hypothesis simplified to False closes the goal.
example (h : (0 : Nat) = 1) : True := by
  simp_engine_boundary_probe only [Nat.zero_ne_one] at h

-- Target closure occurs before deferred proof-bearing hypotheses are installed.
example (n : Nat) (h : n + 0 = n) : n + 0 = n := by
  simp_engine_boundary_probe only [Nat.add_zero] at h ⊢

-- A later declaration may depend on the authored hypothesis proof itself.
example (n : Nat) (h : n + 0 = n) (K : h = h → Prop) (k : K rfl) : K rfl := by
  simp_engine_boundary_probe only [Nat.add_zero] at h
  exact k

-- A custom discharger runs only while recording; apply consumes its checked
-- proof as ordinary boundary evidence.
example (p q : Prop) (h : p) (hpq : p → q) : q := by
  simp_engine_boundary_probe (disch := assumption) [hpq]

-- The proof produced by this custom discharger assigns both a pre-existing
-- expression metavariable and its universe. The following original goal is the
-- unchanged continuation after the auxiliary target closes.
example : True := by
  boundary_insert_assignment_goal
  simp_engine_boundary_probe (disch := boundary_assign_preexisting_mvars) only
    [boundaryConditionalBox_eq]
  exact boundaryAssignmentCarrier
  exact True.intro

-- Elaborating the original simp theorem list processes an already-pending
-- synthetic typeclass metavariable before applying the boundary transform.
example (P : Nat → Prop) (n : Nat) (h : P n) : P (n + 0) := by
  boundary_pending_typeclass_probe
  exact h

-- Pre-existing postponed universe constraints are compared canonically and
-- remain untouched when stock simp leaves them untouched.
example (P : Nat → Prop) (n : Nat) (h : P n) : P (n + 0) := by
  boundary_postponed_constraint_probe
  exact h

-- Persistent extension changes made by the stock discharger are not replayed
-- by a materialized artifact, so the immediate-boundary comparator must reject
-- this call instead of treating it as an unobserved occurrence.
example (p q : Prop) (h : p) (hpq : p → q) : q := by
  fail_if_success simp_engine_boundary_probe
    (disch := boundary_mutate_persistent_extension <;> assumption) [hpq]
  exact hpq h
