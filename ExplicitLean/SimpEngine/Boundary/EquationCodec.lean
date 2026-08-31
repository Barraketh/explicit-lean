module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.DeclarationCodec
public meta import Lean.Meta.Eqns

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/-
  Equation theorem generation records tag attributes on the realization
  branch, then may register the theorem-to-definition mapping on the caller's
  branch. Replay these captured effects without equation generation or
  definitional-equality attribute inference.
-/

private def equationPayloadTag : String := "boundary_equation_v1"

private def validateEquationAnchor (forConst name : Name) : MetaM Unit := do
  if isPrivateName name then
    throwError "boundary_equation_private_name"
  let .str parentName suffix := name
    | throwError "boundary_equation_invalid_name"
  unless parentName == forConst do
    throwError "boundary_equation_foreign_anchor"
  unless isEqnLikeSuffix suffix do
    throwError "boundary_equation_unsupported_suffix"
  unless ((← getEnv).find? forConst (skipRealize := true)).isSome do
    throwError "boundary_equation_unknown_anchor:{forConst}"

private def parseEquationPayload (source : String) : Except String
    (Name × String × Bool × Bool × Bool) := do
  let json ← Json.parse source
  let .arr #[.str tag, anchorJson, .str theoremSource,
      .bool defeqTag, .bool backwardTag, .bool registerEqn] := json
    | throw "invalid equation payload"
  unless tag == equationPayloadTag do
    throw "invalid equation payload tag"
  let forConst ← decodeBoundaryName anchorJson
  pure (forConst, theoremSource, defeqTag, backwardTag, registerEqn)

def encodeBoundaryEquation (forConst : Name) (thm : TheoremVal)
    (defeqTag backwardTag registerEqn : Bool) : MetaM String := do
  validateEquationAnchor forConst thm.name
  let theoremSource ← encodeBoundaryTheorem thm
  return (Json.arr #[.str equationPayloadTag, encodeBoundaryName forConst,
    .str theoremSource, .bool defeqTag, .bool backwardTag, .bool registerEqn]).compress

-- TagAttribute.setTag inserts a tag directly, without running the attribute
-- validator. Keep this closure limited to the checked theorem and exact tags;
-- the caller-local equation mapping must not be inserted here.
private def realizeCapturedEquation (name : Name) (theoremSource : String)
    (defeqTag backwardTag : Bool) : MetaM Unit := do
  executeBoundaryTheorem name theoremSource
  if defeqTag then
    defeqAttr.setTag name
  if backwardTag then
    backwardDefeqAttr.setTag name

private def registerCapturedEquation (forConst name : Name)
    (registerEqn : Bool) : MetaM Unit := do
  let existing? := (eqnsExt.getState (← getEnv)).mapInv.find? name
  match existing? with
  | some existing =>
      unless registerEqn && existing == forConst do
        throwError "boundary_equation_existing_registration_conflict"
  | none =>
      if registerEqn then
        modifyEnv fun env => eqnsExt.modifyState env fun state =>
          { state with mapInv := state.mapInv.insert name forConst }

def executeBoundaryEquation (expectedName : Name) (source : String) : MetaM Unit := do
  let (forConst, theoremSource, defeqTag, backwardTag, registerEqn) ←
    match parseEquationPayload source with
    | .ok payload => pure payload
    | .error error => throwError s!"boundary_equation_decode_error:{error}"
  validateEquationAnchor forConst expectedName
  -- Use the anchor's original realization context, never enable a later one.
  realizeBoundaryConst forConst expectedName <|
    realizeCapturedEquation expectedName theoremSource defeqTag backwardTag
  unless (← getEnv).containsOnBranch expectedName do
    throwError "boundary_equation_missing_realized_theorem"
  -- Recheck the payload and exact tags even when realization reused a cached
  -- result. The declaration codec cannot insert outside realization here.
  executeBoundaryTheorem expectedName theoremSource
  let env ← getEnv
  unless defeqAttr.hasTag env expectedName == defeqTag do
    throwError "boundary_equation_existing_defeq_tag_conflict"
  unless backwardDefeqAttr.hasTag env expectedName == backwardTag do
    throwError "boundary_equation_existing_backward_tag_conflict"
  registerCapturedEquation forConst expectedName registerEqn

end ExplicitLean.SimpEngine.Boundary
