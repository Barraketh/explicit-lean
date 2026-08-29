module
prelude

public import Init.Prelude
public meta import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Tactic.Util

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/-- A closed transformation for one target or local subject. It contains the
    result of stock simplification, not a program for running simplification. -/
structure TargetArtifact where
  input : Expr
  result : Expr
  proof? : Option Expr

structure LocalArtifact where
  fvarId : FVarId
  transformation : TargetArtifact

structure GoalArtifact where
  locals : Array LocalArtifact := #[]
  target? : Option TargetArtifact := none

inductive TargetTerminal where
  | transported
  | closedTrue
  deriving BEq, Repr

inductive GoalTerminal where
  | open
  | closedFromLocalFalse
  | closedFromTargetTrue
  deriving BEq, Repr

/-- Apply a captured target transformation.  This function is intentionally in
    a module whose import closure contains no simplifier implementation,
    theorem registry, simproc registry, or tactic-context construction. -/
def applyTargetArtifact (goal : MVarId) (tail : List MVarId)
    (artifact : TargetArtifact) : MetaM (List MVarId × TargetTerminal) :=
  goal.withContext do
    goal.checkNotAssigned `simp_engine_boundary_apply
    let target ← instantiateMVars (← goal.getType)
    unless ← isDefEq target artifact.input do
      throwError "boundary_target_input_mismatch"
    if artifact.result.isTrue then
      match artifact.proof? with
      | some proof => goal.assign (← mkOfEqTrue proof)
      | none => goal.assign (mkConst ``True.intro)
      return (tail, .closedTrue)
    let next ← match artifact.proof? with
      | some proof => goal.replaceTargetEq artifact.result proof
      | none =>
          if target != artifact.result then
            goal.replaceTargetDefEq artifact.result
          else
            pure goal
    return (next :: tail, .transported)

private def equalityTransport (input result proof value : Expr) : MetaM Expr := do
  let level ← getLevel input
  return mkApp4 (mkConst ``Eq.mp [level]) input result proof value

/-- Apply all captured location subjects in stock externally visible order:
    proof-free local changes happen immediately, proof-bearing local
    changes are asserted after the optional target transformation, and the old
    proof-bearing declarations are then cleared. -/
def applyGoalArtifact (goal : MVarId) (tail : List MVarId)
    (artifact : GoalArtifact) : MetaM (List MVarId × GoalTerminal) := do
  let mut current := goal
  let mut pending : Array Hypothesis := #[]
  let mut toClear : Array FVarId := #[]
  for entry in artifact.locals do
    let transformation := entry.transformation
    let (outcome, pending?) ← current.withContext do
      current.checkNotAssigned `simp_engine_boundary_apply
      let decl ← entry.fvarId.getDecl
      let input ← instantiateMVars decl.type
      unless ← isDefEq input transformation.input do
        throwError "boundary_local_input_mismatch:{decl.userName}"
      match transformation.proof? with
      | none =>
          let next ← current.replaceLocalDeclDefEq entry.fvarId transformation.result
          if transformation.result.isFalse then
            next.assign (← mkFalseElim (← next.getType) (mkFVar entry.fvarId))
            pure (none, none)
          else
            pure (some next, none)
      | some proof =>
          let value ← equalityTransport transformation.input transformation.result proof
            (mkFVar entry.fvarId)
          if transformation.result.isFalse then
            current.assign (← mkFalseElim (← current.getType) value)
            pure (none, none)
          else
            pure (some current, some {
              userName := decl.userName
              type := transformation.result
              value
            })
    match outcome with
    | none => return (tail, .closedFromLocalFalse)
    | some next =>
        current := next
        if let some hypothesis := pending? then
          pending := pending.push hypothesis
          toClear := toClear.push entry.fvarId

  if let some target := artifact.target? then
    let (goals, terminal) ← applyTargetArtifact current tail target
    match terminal with
    | .closedTrue => return (goals, .closedFromTargetTrue)
    | .transported => current := goals.head!

  let (_, next) ← current.assertHypotheses pending
  current := ← next.tryClearMany toClear
  return (current :: tail, .open)

end ExplicitLean.SimpEngine.Boundary
