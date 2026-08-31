module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.DeclarationCodec
public meta import Lean.Meta.CongrTheorems

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/-
  Reserved congruence declarations have two effects beyond their checked
  theorem: they run on the anchor's realization branch, and record argument
  kinds in congrKindsExt. Reproduce only those captured effects. In particular,
  no reserved-name action or congruence theorem generator is called here.
-/

private def congruencePayloadTag : String := "boundary_congruence_v1"

private def encodeCongrArgKind : CongrArgKind → Json
  | .fixed => .str "fixed"
  | .fixedNoParam => .str "fixedNoParam"
  | .eq => .str "eq"
  | .cast => .str "cast"
  | .heq => .str "heq"
  | .subsingletonInst => .str "subsingletonInst"

private def decodeCongrArgKind : Json → Except String CongrArgKind
  | .str "fixed" => pure .fixed
  | .str "fixedNoParam" => pure .fixedNoParam
  | .str "eq" => pure .eq
  | .str "cast" => pure .cast
  | .str "heq" => pure .heq
  | .str "subsingletonInst" => pure .subsingletonInst
  | _ => throw "invalid congruence argument kind"

private def validateCongruenceAnchor (forConst name : Name) : MetaM Unit := do
  let .str parentName suffix := name
    | throwError "boundary_congruence_invalid_name"
  unless parentName == forConst do
    throwError "boundary_congruence_foreign_anchor"
  unless suffix == congrSimpSuffix || isHCongrReservedNameSuffix suffix do
    throwError "boundary_congruence_unsupported_suffix"
  -- Do not resolve a missing anchor through a reserved-name action.
  unless ((← getEnv).find? forConst (skipRealize := true)).isSome do
    throwError "boundary_congruence_unknown_anchor:{forConst}"

private def parseCongruencePayload (source : String) : Except String
    (Name × String × Array CongrArgKind) := do
  let json ← Json.parse source
  let .arr #[.str tag, anchorJson, .str theoremSource, .arr kindParts] := json
    | throw "invalid congruence payload"
  unless tag == congruencePayloadTag do
    throw "invalid congruence payload tag"
  let forConst ← decodeBoundaryName anchorJson
  let kinds ← kindParts.mapM decodeCongrArgKind
  pure (forConst, theoremSource, kinds)

def encodeBoundaryCongruence (forConst : Name) (thm : TheoremVal)
    (kinds : Array CongrArgKind) : MetaM String := do
  validateCongruenceAnchor forConst thm.name
  let theoremSource ← encodeBoundaryTheorem thm
  return (Json.arr #[.str congruencePayloadTag, encodeBoundaryName forConst,
    .str theoremSource, .arr (kinds.map encodeCongrArgKind)]).compress

-- Keep the realization closure's inputs and effects explicit. Do not enable
-- realizations here: Lean must use the environment captured for the anchor by
-- its original elaborator, not a later environment from this replay site.
private def realizeCapturedCongruence (name : Name) (theoremSource : String)
    (kinds : Array CongrArgKind) : MetaM Unit := do
  executeBoundaryTheorem name theoremSource
  modifyEnv fun env => congrKindsExt.insert env name kinds

def executeBoundaryCongruence (expectedName : Name) (source : String) : MetaM Unit := do
  let (forConst, theoremSource, kinds) ← match parseCongruencePayload source with
    | .ok payload => pure payload
    | .error error => throwError s!"boundary_congruence_decode_error:{error}"
  validateCongruenceAnchor forConst expectedName
  realizeConst forConst expectedName <|
    realizeCapturedCongruence expectedName theoremSource kinds
  -- realizeConst can skip its closure for a declaration already present on
  -- this branch or in a shared realization cache. Validate both cases, without
  -- allowing the declaration codec to insert anything outside realization.
  unless (← getEnv).containsOnBranch expectedName do
    throwError "boundary_congruence_missing_realized_theorem"
  executeBoundaryTheorem expectedName theoremSource
  let some existingKinds := congrKindsExt.find? (← getEnv) expectedName
    | throwError "boundary_congruence_missing_argument_kinds"
  unless existingKinds == kinds do
    throwError "boundary_congruence_existing_argument_kinds_conflict"

end ExplicitLean.SimpEngine.Boundary
