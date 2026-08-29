module

import Mathlib
public meta import Lean.Elab.Tactic.Basic

public section

set_option autoImplicit false

open Lean Meta Elab Tactic

/-- A source fixture that forces a custom discharger to assign pre-existing
    expression and universe metavariables. -/
inductive BoundarySourceConditionalBox : Prop where
  | intro

theorem boundarySourceConditionalBox_eq (_ : True) :
    BoundarySourceConditionalBox ↔ True :=
  ⟨fun _ => True.intro, fun _ => .intro⟩

syntax "boundary_source_insert_assignment_goal" : tactic
syntax "boundary_source_assign_preexisting_mvars" : tactic

elab_rules : tactic
  | `(tactic| boundary_source_insert_assignment_goal) => withMainContext do
      let goals ← getGoals
      let level ← mkFreshLevelMVar
      let typeMVar ← mkFreshExprMVar (some (mkSort level))
      withLocalDeclD `boundarySourceAssignmentCarrier typeMVar fun _ => do
        let continuation ← mkFreshExprMVar (some typeMVar) .syntheticOpaque
        let auxiliary ← mkFreshExprMVar
          (some (mkConst ``BoundarySourceConditionalBox)) .syntheticOpaque
        setGoals (auxiliary.mvarId! :: continuation.mvarId! :: goals)
  | `(tactic| boundary_source_assign_preexisting_mvars) => withMainContext do
      let some carrier :=
          (← getLCtx).findFromUserName? `boundarySourceAssignmentCarrier
        | throwError "missing pre-existing assignment carrier"
      let typeMVarId := carrier.type.mvarId!
      let typeDecl ← typeMVarId.getDecl
      assignLevelMVar typeDecl.type.sortLevel!.mvarId! .zero
      typeMVarId.assign (mkConst ``True)
      let goal ← getMainGoal
      goal.assign (mkConst ``True.intro)
      replaceMainGoal []

theorem boundarySourceFixture
    (P : Nat → Prop) (n : Nat) (h : P n) : P (n + 0) := by
  simp only [Nat.add_zero]
  exact h

theorem boundarySourceClosed (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]

def boundarySourceAlias (n : Nat) : Nat := n

theorem boundarySourceDefEq
    (P : Nat → Prop) (n : Nat) (h : P n) : P (boundarySourceAlias n) := by
  simp only [boundarySourceAlias]
  exact h

theorem boundarySourceUnchanged (P : Prop) (h : P) : P := by
  simp (config := { failIfUnchanged := false }) only
  exact h

theorem boundarySourceHypothesis
    (P : Nat → Prop) (n : Nat) (h : P (n + 0)) : P n := by
  simp only [Nat.add_zero] at h
  exact h

theorem boundarySourceCombined
    (P : Nat → Prop) (n : Nat) (h : P (n + 0)) : P (n + 0) := by
  simp only [Nat.add_zero] at h ⊢
  exact h

theorem boundarySourceFalseHypothesis (h : (0 : Nat) = 1) : True := by
  simp only [Nat.zero_ne_one] at h

theorem boundarySourceOrderedHypotheses
    (P Q : Nat → Prop) (n : Nat) (hP : P (n + 0)) (hQ : Q (n + 0)) :
    P n ∧ Q n := by
  simp only [Nat.add_zero] at hP hQ
  constructor
  · exact hP
  · exact hQ

-- The replacement must refer to a binder that has no authored source name
-- without requiring the enclosing theorem body to be restructured.
theorem boundarySourceInaccessible : ∀ n : Nat, n + 0 = n :=
  fun _ => by
    simp only [Nat.add_zero]

-- An inline occurrence exercises generated-term indentation relative to the
-- tactic token rather than only the enclosing declaration margin.
theorem boundarySourceInline (n : Nat) : n + 0 = n := by simp only [Nat.add_zero]

def boundarySourceAcceptEq {n : Nat} (_ : n + 0 = n) : Prop := True

-- Two nested occurrences on one line ensure that expanding the first artifact
-- establishes the actual source column used to indent the second artifact.
theorem boundarySourceTwoNested (n : Nat) :
    boundarySourceAcceptEq (n := n) (by simp only [Nat.add_zero]) = boundarySourceAcceptEq (n := n) (by simp only [Nat.add_zero]) :=
  rfl

-- The discharger is recording-only provenance; materialized source contains
-- only the resulting checked transformation and proof.
theorem boundarySourceDischarger (p q : Prop) (h : p) (hpq : p → q) : q := by
  simp (disch := assumption) [hpq]

-- A failed whole tactic is externally visible to tactic control flow. The
-- materialized failure must leave the state untouched so the same branch wins.
theorem boundarySourceFailureAlternative (P : Prop) (h : P) : P := by
  first
  | simp (config := { failIfUnchanged := true }) only
  | exact h

-- Serialized evidence must reproduce assignments needed by the unchanged
-- continuation even though the generated apply tactic does not run the
-- discharger.
theorem boundarySourcePreexistingAssignments : True := by
  boundary_source_insert_assignment_goal
  simp (disch := boundary_source_assign_preexisting_mvars) only
    [boundarySourceConditionalBox_eq]
  exact boundarySourceAssignmentCarrier
  exact True.intro

-- One quoted source occurrence executes in two callers with different states
-- and outcomes. The generated selector must choose the successful artifact in
-- the first theorem and propagate the recorded failure to the unchanged
-- alternative in the second.
macro "boundary_source_reusable_simp" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := true }) only [Nat.add_zero])

theorem boundarySourceReusableSuccess (n : Nat) : n + 0 = n := by
  boundary_source_reusable_simp

theorem boundarySourceReusableFailure (P : Prop) (h : P) : P := by
  first
  | boundary_source_reusable_simp
  | exact h

-- This reusable syntax is intentionally not invoked by the frozen fixture.
-- Materialization must still replace it with an explicit fail-closed tactic.
macro "boundary_source_unobserved_simp" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false, zetaDelta := false }) only)
