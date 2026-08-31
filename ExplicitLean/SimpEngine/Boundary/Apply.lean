module
prelude

public import Init.Prelude
public meta import ExplicitLean.SimpEngine.Boundary.CongruenceCodec
public meta import ExplicitLean.SimpEngine.Boundary.EquationCodec
public meta import ExplicitLean.SimpEngine.Boundary.MatcherCodec
public meta import ExplicitLean.SimpEngine.Boundary.LocalTheoremCodec
public meta import ExplicitLean.SimpEngine.Boundary.SequenceCodec
public meta import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Tactic.Util

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/- The boundary artifact protocol is deliberately independent of the legacy
   schema-27 certificate/replay format. Keep these literals synchronized with
   Experiment/boundary_protocol.py. They are part of the artifact-schema
   semantics, so changing an encoding literal requires bumping the artifact
   schema. Generated source validates that schema before it elaborates any
   evidence or executes an environment action. -/
def boundaryArtifactKind : String := "simp_engine_boundary_artifact"
def boundaryArtifactSchema : Nat := 5
def boundarySelectorSchema : Nat := 2
def boundarySemanticContract : String := "boundary-observable-v1"
def boundaryArtifactTermEncoding : String := "lean_expr_dag_v3"
def boundaryArtifactLocalReferenceEncoding : String := "local_decl_index_v1"
def boundaryArtifactExpressionReferenceEncoding : String := "pre_boundary_expression_reference_v1"
def boundaryArtifactUniverseEncoding : String := "pre_boundary_universe_reference_v1"
def boundaryArtifactInstanceEncoding : String := "explicit_terms_v1"

/- The successful artifact carries the exact post-stock auxiliary declaration
   generator.  Names are encoded structurally, rather than through
   `Name.toString`, so replay can authenticate the complete generator state. -/
def encodeBoundaryDeclNameGenerator (generator : DeclNameGenerator) : Json :=
  Json.mkObj [
    ("namePrefix", encodeBoundaryName generator.namePrefix),
    ("idx", toJson generator.idx),
    ("parentIdxs", Json.arr (generator.parentIdxs.toArray.map toJson))
  ]

/- Marker lines emitted by the recording tactic are authenticated against the
   compiler process that requested them. Direct probes which do not provide
   this environment variable use the explicit unauthenticated token. -/
def boundaryRunNonceEnv : String := "SIMP_ENGINE_BOUNDARY_RUN_NONCE"
def boundaryUnauthenticatedRunNonce : String := "unauthenticated"

/-
  Captured congruence declarations and their argument metadata are reconstructed
  and kernel checked in Lean's declaration branch. Application never invokes
  reserved-name generators or proof-search callbacks.
-/
inductive EnvironmentAction where
  | declareCongruence (name : Name) (payload : String)
  | declareEquation (name : Name) (payload : String)
  | declareMatcher (anchor : Name) (payload : String)
  | declareLocalTheorems (anchor : Name) (payload : String)
  | realizeGroups (anchor : Name) (payload : String)
  deriving Inhabited, BEq

private def executeEnvironmentAction : EnvironmentAction → MetaM Unit
  | .declareCongruence name payload => executeBoundaryCongruence name payload
  | .declareEquation name payload => executeBoundaryEquation name payload
  | .declareMatcher anchor payload => executeBoundaryMatcher anchor payload
  | .declareLocalTheorems anchor payload => executeBoundaryLocalTheorems anchor payload
  | .realizeGroups anchor payload => executeBoundaryRealizationEffects anchor payload

def executeEnvironmentActions (actions : Array EnvironmentAction) : MetaM Unit := do
  for action in actions do
    executeEnvironmentAction action

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
  environmentActions : Array EnvironmentAction := #[]
  referenceUse? : Option BoundaryReferenceUse := none

def TargetArtifact.expressions (artifact : TargetArtifact) : Array Expr :=
  #[artifact.input, artifact.result] ++ artifact.proof?.toArray

def GoalArtifact.expressions (artifact : GoalArtifact) : Array Expr :=
  artifact.locals.foldl (fun result entry => result ++ entry.transformation.expressions) #[] ++
    (artifact.target?.map (·.expressions) |>.getD #[])

private def guardReferenceUse (use? : Option BoundaryReferenceUse) (goal : MVarId)
    (expressions : Array Expr) : MetaM Unit := do
  if let some use := use? then use.checkAt goal expressions

private def checkReferenceState (use? : Option BoundaryReferenceUse) : MetaM Unit := do
  if let some use := use? then use.checkUnchanged

private def observingReferenceCheck (use? : Option BoundaryReferenceUse) (action : MetaM α) : MetaM α := do
  match use? with
  | none => action
  | some use => withBoundaryReferenceValidation use action

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
    (artifact : TargetArtifact) (referenceUse? : Option BoundaryReferenceUse := none) : MetaM (List MVarId × TargetTerminal) :=
  goal.withContext do
    guardReferenceUse referenceUse? goal artifact.expressions
    goal.checkNotAssigned `simp_engine_boundary_apply
    let target ← instantiateMVars (← goal.getType)
    unless ← observingReferenceCheck referenceUse? <| isDefEq target artifact.input do
      throwError "boundary_target_input_mismatch"
    if artifact.result.isTrue then
      match artifact.proof? with
      | some proof =>
          -- Preserve pinned builder state effects. Its fixed of_eq_true
          -- telescope has no instance binder; never assign protected opaque
          -- references while matching its fresh ordinary template parameter.
          let value ← withConfig (fun c => {c with assignSyntheticOpaque := false}) <| mkOfEqTrue proof
          goal.assign value
      | none => goal.assign (mkConst ``True.intro)
      checkReferenceState referenceUse?
      return (tail, .closedTrue)
    let next ← match artifact.proof? with
      | some proof => goal.replaceTargetEq artifact.result proof
      | none =>
          if target != artifact.result then
            goal.replaceTargetDefEq artifact.result
          else
            pure goal
    checkReferenceState referenceUse?
    return (next :: tail, .transported)

private def equalityTransport (input result proof value : Expr) : MetaM Expr := do
  let level ← getLevel input
  return mkApp4 (mkConst ``Eq.mp [level]) input result proof value

/-- Apply all captured location subjects in stock externally visible order:
    proof-free local changes happen immediately, proof-bearing local
    changes are asserted after the optional target transformation, and the old
    proof-bearing declarations are then cleared. -/
def applyGoalArtifact (goal : MVarId) (tail : List MVarId)
    (artifact : GoalArtifact) : MetaM (List MVarId × GoalTerminal) := withoutBoundaryPendingSynthesis do
  executeEnvironmentActions artifact.environmentActions
  let use? := artifact.referenceUse?
  guardReferenceUse use? goal artifact.expressions
  let mut current := goal
  let mut pending : Array Hypothesis := #[]
  let mut toClear : Array FVarId := #[]
  for entry in artifact.locals do
    let transformation := entry.transformation
    let (outcome, pending?) ← current.withContext do
      guardReferenceUse use? current transformation.expressions
      current.checkNotAssigned `simp_engine_boundary_apply
      let decl ← entry.fvarId.getDecl
      let input ← instantiateMVars decl.type
      unless ← observingReferenceCheck use? <| isDefEq input transformation.input do
        throwError "boundary_local_input_mismatch:{decl.userName}"
      match transformation.proof? with
      | none =>
          let next ← current.replaceLocalDeclDefEq entry.fvarId transformation.result
          if transformation.result.isFalse then
            guardReferenceUse use? next #[transformation.result, ← next.getType]
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
    checkReferenceState use?
    match outcome with
    | none => return (tail, .closedFromLocalFalse)
    | some next =>
        current := next
        if let some hypothesis := pending? then
          pending := pending.push hypothesis
          toClear := toClear.push entry.fvarId

  if let some target := artifact.target? then
    let (goals, terminal) ← applyTargetArtifact current tail target use?
    match terminal with
    | .closedTrue => return (goals, .closedFromTargetTrue)
    | .transported => current := goals.head!

  guardReferenceUse use? current (pending.flatMap fun h => #[h.type, h.value])
  let (_, next) ← current.assertHypotheses pending
  guardReferenceUse use? next #[]
  current := ← next.tryClearMany toClear
  checkReferenceState use?
  return (current :: tail, .open)

end ExplicitLean.SimpEngine.Boundary
