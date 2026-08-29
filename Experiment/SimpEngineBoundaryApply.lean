import ExplicitLean.SimpEngine.Boundary.Tactic
import Lean.Meta.Tactic.Rename

open Lean Meta Elab Tactic

namespace ExplicitLean.SimpEngine.Boundary.GuardProbe

private def mkGuardSyntax (state : BoundaryStateFingerprint) (options caller : String) :
    Syntax :=
  mkNode ``Lean.Parser.Tactic.simpEngineBoundaryGuard #[
    mkAtom "simp_engine_boundary_guard",
    Syntax.mkStrLit state.targetFingerprint,
    Syntax.mkStrLit state.localContextFingerprint,
    Syntax.mkStrLit state.metavariableContextFingerprint,
    Syntax.mkNatLit state.goalCount,
    Syntax.mkStrLit options,
    Syntax.mkStrLit caller]

private def currentCaller : TacticM String :=
  return boundaryCallerIdentity? (← Term.getDeclName?)

private def accepted (state : BoundaryStateFingerprint) (options caller : String) :
    TacticM Bool := do
  try
    evalTactic (mkGuardSyntax state options caller)
    pure true
  catch _ =>
    pure false

elab "check_boundary_guard" : tactic => withMainContext do
  let before ← boundaryProofStateFingerprint (← getGoals)
  let options := boundaryOptionsFingerprint (← getOptions)
  let caller ← currentCaller
  unless ← accepted before options caller do
    throwError "boundary guard rejected its own dynamically computed selector"
  let mutations : Array BoundaryStateFingerprint := #[
    { before with targetFingerprint := before.targetFingerprint ++ ":mutated" },
    { before with localContextFingerprint := before.localContextFingerprint ++ ":mutated" },
    { before with metavariableContextFingerprint :=
        before.metavariableContextFingerprint ++ ":mutated" },
    { before with goalCount := before.goalCount + 1 }]
  let mutationOptions := options ++ ":mutated"
  let mutationCaller := caller ++ ":mutated"
  for mutation in mutations do
    if ← accepted mutation options caller then
      throwError "boundary guard accepted a mutated selector"
  if ← accepted before mutationOptions caller then
    throwError "boundary guard accepted a mutated options selector"
  if ← accepted before options mutationCaller then
    throwError "boundary guard accepted a mutated caller selector"
  let after ← boundaryProofStateFingerprint (← getGoals)
  unless after == before do
    throwError "boundary guard mutation checks changed the proof state"

elab "check_boundary_alpha_invariant" id:ident : tactic => withMainContext do
  let before ← boundaryProofStateFingerprint (← getGoals)
  let options := boundaryOptionsFingerprint (← getOptions)
  let caller ← currentCaller
  let goal ← getMainGoal
  let some decl := (← getLCtx).findFromUserName? id.getId
    | throwErrorAt id "unknown local '{id.getId}'"
  let renamed ← goal.rename decl.fvarId `alphaRenamedParameter
  replaceMainGoal [renamed]
  let after ← boundaryProofStateFingerprint (← getGoals)
  unless after == before do
    throwError "boundary selector changed under theorem-parameter alpha-renaming"
  unless ← accepted before options caller do
    throwError "boundary guard rejected an alpha-renamed equivalent state"

end ExplicitLean.SimpEngine.Boundary.GuardProbe

set_option autoImplicit false

def materializedBoundaryAlias (n : Nat) : Nat := n

theorem materializedBoundaryTransport
    (P : Nat → Prop) (n : Nat) (h : P n) : P (n + 0) := by
  simp_engine_boundary_apply (P (n + 0) ==> P n using
    congrArg P (Nat.add_zero n))
  exact h

theorem materializedBoundaryDefEq
    (P : Nat → Prop) (n : Nat) (h : P n) : P (materializedBoundaryAlias n) := by
  simp_engine_boundary_apply (P (materializedBoundaryAlias n) ==> P n)
  exact h

theorem materializedBoundaryUnchanged (P : Prop) (h : P) : P := by
  simp_engine_boundary_apply (P ==> P)
  exact h

theorem materializedBoundaryGuard (P : Prop) (h : P) : P := by
  check_boundary_guard
  exact h

theorem materializedBoundaryRejectsInvalid (P : Prop) (h : P) : P := by
  fail_if_success simp_engine_boundary_apply (True ==> True)
  fail_if_success simp_engine_boundary_variant_missing
  fail_if_success simp_engine_boundary_occurrence_unobserved
  exact h

theorem materializedBoundaryAlphaInvariant (P : Prop) (h : P) : P := by
  check_boundary_alpha_invariant h
  assumption

theorem materializedBoundaryClosed (n : Nat) : n + 0 = n := by
  simp_engine_boundary_apply (n + 0 = n ==> True using
    propext ⟨fun _ => True.intro, fun _ => Nat.add_zero n⟩)

theorem materializedBoundaryHypothesis
    (P : Nat → Prop) (n : Nat) (h : P (n + 0)) : P n := by
  simp_engine_boundary_apply
    at h (P (n + 0) ==> P n using congrArg P (Nat.add_zero n))
  exact h

theorem materializedBoundaryLocation
    (P : Nat → Prop) (n : Nat) (h : P (n + 0)) : P (n + 0) := by
  simp_engine_boundary_apply
    at h (P (n + 0) ==> P n using congrArg P (Nat.add_zero n))
    ⊢ (P (n + 0) ==> P n using congrArg P (Nat.add_zero n))
  exact h

theorem materializedBoundaryFalseHypothesis (h : (0 : Nat) = 1) : True := by
  simp_engine_boundary_apply
    at h ((0 : Nat) = 1 ==> False using
      propext ⟨Nat.zero_ne_one, fun false => False.elim false⟩)

#eval IO.println "SIMP_ENGINE_BOUNDARY_APPLY_ONLY ok"
