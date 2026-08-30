module
prelude

public meta import ExplicitLean.SimpEngine.Boundary.Apply
public meta import ExplicitLean.SimpEngine.Boundary.Selector
public meta import Lean.Elab.Tactic.ElabTerm

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

declare_syntax_cat boundaryEvidence
syntax "(" term "==>" term ")" : boundaryEvidence
syntax "(" term "==>" term "using" term ")" : boundaryEvidence

declare_syntax_cat boundaryLocalEvidence
syntax "at" ident boundaryEvidence : boundaryLocalEvidence

declare_syntax_cat boundaryTargetEvidence
syntax "⊢" boundaryEvidence : boundaryTargetEvidence

declare_syntax_cat boundaryLocationEvidence
syntax boundaryLocalEvidence+ (boundaryTargetEvidence)? : boundaryLocationEvidence

declare_syntax_cat boundaryEncodedEvidence
syntax "(" str "==>" str ")" : boundaryEncodedEvidence
syntax "(" str "==>" str "using" str ")" : boundaryEncodedEvidence

declare_syntax_cat boundaryEncodedLocalEvidence
syntax "at_index" num boundaryEncodedEvidence : boundaryEncodedLocalEvidence

declare_syntax_cat boundaryEncodedTargetEvidence
syntax "⊢" boundaryEncodedEvidence : boundaryEncodedTargetEvidence

declare_syntax_cat boundaryEncodedLocationEvidence
syntax boundaryEncodedLocalEvidence+ (boundaryEncodedTargetEvidence)? :
  boundaryEncodedLocationEvidence

declare_syntax_cat boundaryEncodedEnvironmentAction
syntax "realize_reserved_name" str : boundaryEncodedEnvironmentAction

declare_syntax_cat boundaryEncodedActions
syntax "[" boundaryEncodedEnvironmentAction,* "]" : boundaryEncodedActions

declare_syntax_cat boundaryVariantOutcome
syntax "failure" : boundaryVariantOutcome
syntax "apply_encoded" boundaryEncodedEvidence : boundaryVariantOutcome
syntax "apply_encoded" boundaryEncodedLocationEvidence : boundaryVariantOutcome
syntax "apply_encoded_with_actions" boundaryEncodedActions boundaryEncodedEvidence :
  boundaryVariantOutcome
syntax "apply_encoded_with_actions" boundaryEncodedActions boundaryEncodedLocationEvidence :
  boundaryVariantOutcome

declare_syntax_cat boundaryVariant
syntax "| " str str str str num str str " => " boundaryVariantOutcome : boundaryVariant

declare_syntax_cat boundaryArtifactHeader
syntax "(" "artifact_kind" ":=" str "artifact_schema" ":=" num
  "selector_schema" ":=" num "semantic_contract" ":=" str
  "occurrence_id" ":=" str "recorded_module" ":=" str ")" :
  boundaryArtifactHeader

syntax (name := simpEngineBoundaryApplyDefEq)
  "simp_engine_boundary_apply" "(" term "==>" term ")" : tactic

syntax (name := simpEngineBoundaryApplyEq)
  "simp_engine_boundary_apply" "(" term "==>" term "using" term ")" : tactic

syntax (name := simpEngineBoundaryApplyLocation)
  "simp_engine_boundary_apply" boundaryLocationEvidence : tactic

syntax (name := simpEngineBoundaryApplyFailure)
  "simp_engine_boundary_apply_failure" : tactic

syntax (name := simpEngineBoundaryGuard)
  "simp_engine_boundary_guard" str str str num str str : tactic

syntax (name := simpEngineBoundaryVariantMissing)
  "simp_engine_boundary_variant_missing" : tactic

syntax (name := simpEngineBoundaryOccurrenceUnobserved)
  "simp_engine_boundary_occurrence_unobserved" : tactic

syntax (name := simpEngineBoundarySelect)
  "simp_engine_boundary_select "
    boundaryArtifactHeader
    withPosition((ppDedent(ppLine) colGe boundaryVariant)+) : tactic

end Lean.Parser.Tactic

namespace ExplicitLean.SimpEngine.Boundary

/-- Return an authored local name when it resolves uniquely; otherwise use a
    stable source-only alias. Generated artifacts cannot refer to inaccessible,
    macro-scoped, or shadowed names, and the surrounding source remains
    unchanged, so evidence rendering and elaboration share this aliasing rule. -/
def boundarySourceLocalName (lctx : LocalContext) (decl : LocalDecl) : Name :=
  if !decl.userName.isInaccessibleUserName && !decl.userName.hasMacroScopes &&
      (lctx.findFromUserName? decl.userName).any (·.fvarId == decl.fvarId) then
    decl.userName
  else
    Name.mkSimple s!"_simpBoundaryLocal{decl.index}"

def withBoundarySourceContext (x : TacticM α) : TacticM α := do
  let originalLCtx ← getLCtx
  let mut sourceLCtx := originalLCtx
  for decl in originalLCtx do
    sourceLCtx := sourceLCtx.setUserName decl.fvarId
      (boundarySourceLocalName originalLCtx decl)
  withLCtx sourceLCtx (← getLocalInstances) x

/-- Encoded generated artifacts refer to every pre-existing local by its
declaration index. Unlike authored identifiers, these aliases can be parsed
after a reusable tactic quotation expands without being captured by macro
hygiene, and they remain valid under theorem-parameter alpha-renaming. -/
private def boundaryEncodedLocalName (decl : LocalDecl) : Name :=
  Name.mkSimple s!"_simpBoundaryLocal{decl.index}"

def withBoundaryEncodedSourceContext (x : TacticM α) : TacticM α := do
  let originalLCtx ← getLCtx
  let mut sourceLCtx := originalLCtx
  for decl in originalLCtx do
    sourceLCtx := sourceLCtx.setUserName decl.fvarId
      (boundaryEncodedLocalName decl)
  withLCtx sourceLCtx (← getLocalInstances) x

private def elaborateType (stx : Syntax) : TacticM Expr :=
  runTermElab do
    let type ← Term.elabType stx
    Term.synthesizeSyntheticMVars
    instantiateMVars type

private def elaborateEvidence (stx : Syntax) : TacticM TargetArtifact := do
  let (inputSyntax, resultSyntax, proofSyntax?) ←
    match stx with
    | `(boundaryEvidence| ($input ==> $result)) => pure (input, result, none)
    | `(boundaryEvidence| ($input ==> $result using $proof)) =>
        pure (input, result, some proof)
    | _ => throwError "invalid boundary evidence"
  let input ← elaborateType inputSyntax
  let result ← elaborateType resultSyntax
  let expectedProofType ← mkEq input result
  let proof? ← proofSyntax?.mapM fun proofSyntax =>
    elabTermEnsuringType proofSyntax (some expectedProofType)
  return { input, result, proof? }

private def parseEncodedTerm (source : String) : TacticM Syntax := do
  match Parser.runParserCategory (← getEnv) `term source with
  | .ok stx => return stx
  | .error message => throwError "invalid encoded boundary term: {message}"

private def elaborateEncodedEvidence (stx : Syntax) : TacticM TargetArtifact := do
  let (inputSource, resultSource, proofSource?) ←
    match stx with
    | `(boundaryEncodedEvidence| ($input:str ==> $result:str)) =>
        pure (input.getString, result.getString, none)
    | `(boundaryEncodedEvidence| ($input:str ==> $result:str using $proof:str)) =>
        pure (input.getString, result.getString, some proof.getString)
    | _ => throwError "invalid encoded boundary evidence"
  let input ← elaborateType (← parseEncodedTerm inputSource)
  let result ← elaborateType (← parseEncodedTerm resultSource)
  let expectedProofType ← mkEq input result
  let proof? ← proofSource?.mapM fun proofSource => do
    elabTermEnsuringType (← parseEncodedTerm proofSource) (some expectedProofType)
  return { input, result, proof? }

private def runExplicitApply (inputSyntax resultSyntax : Syntax)
    (proofSyntax? : Option Syntax) : TacticM Unit := withMainContext do
  withBoundarySourceContext do
    let input ← elaborateType inputSyntax
    let result ← elaborateType resultSyntax
    let expectedProofType ← mkEq input result
    let proof? ← proofSyntax?.mapM fun proofSyntax =>
      elabTermEnsuringType proofSyntax (some expectedProofType)
    let goals ← getGoals
    let (next, _) ← applyTargetArtifact goals.head! goals.tail {
      input
      result
      proof?
    }
    setGoals next

private def runExplicitLocationApply (localSyntax : Array Syntax)
    (targetSyntax? : Option Syntax) : TacticM Unit := withMainContext do
  withBoundarySourceContext do
    let mut locals := #[]
    for entrySyntax in localSyntax do
      match entrySyntax with
      | `(boundaryLocalEvidence| at $id:ident $evidence:boundaryEvidence) =>
          let some decl := (← getLCtx).findFromUserName? id.getId
            | throwErrorAt id "unknown boundary local alias '{id.getId}'"
          locals := locals.push {
            fvarId := decl.fvarId
            transformation := ← elaborateEvidence evidence
          }
      | _ => throwError "invalid local boundary evidence"
    let target? ← targetSyntax?.mapM fun entrySyntax => do
      match entrySyntax with
      | `(boundaryTargetEvidence| ⊢ $evidence:boundaryEvidence) =>
          elaborateEvidence evidence
      | _ => throwError "invalid target boundary evidence"
    let goals ← getGoals
    let (next, _) ← applyGoalArtifact goals.head! goals.tail { locals, target? }
    setGoals next

private def findLocalByIndex (lctx : LocalContext) (index : Nat) : Option LocalDecl :=
  lctx.decls.findSome? fun decl? => decl?.filter (·.index == index)

private def parseEncodedEnvironmentActions
    (actions : Array Syntax) : TacticM (Array EnvironmentAction) := do
  let mut result : Array EnvironmentAction := #[]
  for action in actions do
    match action with
    | `(boundaryEncodedEnvironmentAction| realize_reserved_name $name:str) =>
        let name := name.getString.toName
        if name.isAnonymous then
          throwError "invalid encoded reserved-name action"
        result := result.push (EnvironmentAction.realizeReservedName name)
    | _ => throwError "invalid encoded environment action"
  return result

private def runExplicitEncodedApply (actions : Array Syntax) (evidence : Syntax) : TacticM Unit :=
  withMainContext do
    withBoundaryEncodedSourceContext do
      let environmentActions ← parseEncodedEnvironmentActions actions
      let artifact ← elaborateEncodedEvidence evidence
      let goals ← getGoals
      let (next, _) ← applyGoalArtifact goals.head! goals.tail {
        target? := some artifact
        environmentActions
      }
      setGoals next

private def runExplicitEncodedLocationApply (actions : Array Syntax)
    (localSyntax : Array Syntax) (targetSyntax? : Option Syntax) : TacticM Unit :=
  withMainContext do
  withBoundaryEncodedSourceContext do
    let environmentActions ← parseEncodedEnvironmentActions actions
    let lctx ← getLCtx
    let mut locals := #[]
    for entrySyntax in localSyntax do
      match entrySyntax with
      | `(boundaryEncodedLocalEvidence| at_index $index:num
          $evidence:boundaryEncodedEvidence) =>
          let localIndex := index.raw.isNatLit?.getD 0
          let some decl := findLocalByIndex lctx localIndex
            | throwErrorAt index "unknown boundary local index '{localIndex}'"
          locals := locals.push {
            fvarId := decl.fvarId
            transformation := ← elaborateEncodedEvidence evidence
          }
      | _ => throwError "invalid encoded local boundary evidence"
    let target? ← targetSyntax?.mapM fun entrySyntax => do
      match entrySyntax with
      | `(boundaryEncodedTargetEvidence| ⊢ $evidence:boundaryEncodedEvidence) =>
          elaborateEncodedEvidence evidence
      | _ => throwError "invalid encoded target boundary evidence"
    let goals ← getGoals
    let (next, _) ← applyGoalArtifact goals.head! goals.tail {
      locals
      target?
      environmentActions
    }
    setGoals next

private def runBoundaryGuard (targetFingerprint localContextFingerprint
    metavariableContextFingerprint : String) (goalCount : Nat)
    (optionsFingerprint caller : String) : TacticM Unit := do
  let saved ← Tactic.saveState
  try
    withMainContext do
      let expected : BoundaryStateFingerprint := {
        targetFingerprint
        localContextFingerprint
        metavariableContextFingerprint
        goalCount
      }
      let actual ← boundaryProofStateFingerprintWithTerm (← getGoals)
        (← getThe Term.State)
      let actualOptions := boundaryOptionsFingerprint (← getOptions)
      let actualCaller := boundaryCallerIdentity? (← Term.getDeclName?)
      unless actual == expected && actualOptions == optionsFingerprint &&
          actualCaller == caller do
        throwError "boundary_variant_selector_mismatch"
  catch error =>
    saved.restore
    throw error

private def runBoundaryVariantMissing : TacticM Unit := do
  let saved ← Tactic.saveState
  saved.restore
  throwError "boundary_variant_missing"

private structure ExpectedBoundarySelector where
  artifactOccurrence : String
  state : BoundaryStateFingerprint
  options : String
  caller : String

private def parseBoundaryVariant (variant : Syntax) (artifactOccurrence : String) :
    TacticM (ExpectedBoundarySelector × Syntax) := do
  match variant with
  | `(boundaryVariant| | $occurrenceId:str $targetFingerprint:str
      $localContextFingerprint:str $metavariableContextFingerprint:str $goalCount:num
      $optionsFingerprint:str $caller:str => $outcome:boundaryVariantOutcome) =>
      let occId := occurrenceId.getString
      unless !occId.isEmpty do
        throwError "invalid_boundary_occurrence"
      unless occId == artifactOccurrence do
        throwError "invalid_boundary_occurrence"
      return ({
        artifactOccurrence := occId
        state := {
          targetFingerprint := targetFingerprint.getString
          localContextFingerprint := localContextFingerprint.getString
          metavariableContextFingerprint := metavariableContextFingerprint.getString
          goalCount := goalCount.raw.isNatLit?.getD 0
        }
        options := optionsFingerprint.getString
        caller := caller.getString
      }, outcome)
  | _ => throwError "invalid boundary variant"

private def validateArtifactHeader (kind : String) (schema selectorSchema : Nat)
    (contract occId moduleName : String) : TacticM Unit := do
  unless kind == boundaryArtifactKind do
    throwError "unsupported_boundary_artifact_kind"
  unless schema == boundaryArtifactSchema do
    throwError "unsupported_boundary_artifact_schema"
  unless selectorSchema == boundarySelectorSchema do
    throwError "unsupported_boundary_selector_schema"
  unless contract == boundarySemanticContract do
    throwError "unsupported_boundary_semantic_contract"
  unless !occId.isEmpty do
    throwError "invalid_boundary_occurrence"
  unless !moduleName.isEmpty do
    throwError "boundary_module_mismatch"
  let currentModule := (← getEnv).mainModule.toString
  unless currentModule == moduleName do
    throwError "boundary_module_mismatch"

private def runBoundaryVariantOutcome (outcome : Syntax) : TacticM Unit := do
  match outcome with
  | `(boundaryVariantOutcome| failure) =>
      throwError "boundary_recorded_tactic_failure"
  | `(boundaryVariantOutcome| apply_encoded $evidence:boundaryEncodedEvidence) =>
      runExplicitEncodedApply #[] evidence
  | `(boundaryVariantOutcome| apply_encoded
      $location:boundaryEncodedLocationEvidence) =>
      let locals := location.raw[0].getArgs
      let targetSyntax? := if location.raw[1].isNone then none else some location.raw[1][0]
      runExplicitEncodedLocationApply #[] locals targetSyntax?
  | `(boundaryVariantOutcome| apply_encoded_with_actions
      [$actions:boundaryEncodedEnvironmentAction,*]
      $evidence:boundaryEncodedEvidence) =>
      runExplicitEncodedApply actions evidence
  | `(boundaryVariantOutcome| apply_encoded_with_actions
      [$actions:boundaryEncodedEnvironmentAction,*]
      $location:boundaryEncodedLocationEvidence) =>
      let locals := location.raw[0].getArgs
      let targetSyntax? := if location.raw[1].isNone then none else some location.raw[1][0]
      runExplicitEncodedLocationApply actions locals targetSyntax?
  | _ => throwError "invalid boundary variant outcome"

private def runBoundarySelect (kind : String) (schema selectorSchema : Nat)
    (contract occId moduleName : String) (variants : Array Syntax) : TacticM Unit := do
  validateArtifactHeader kind schema selectorSchema contract occId moduleName
  -- A malformed sibling is a protocol error even if another variant would
  -- otherwise select, so validate the complete serialized set first.
  let parsedVariants ← variants.mapM (parseBoundaryVariant · occId)
  let actualState ← boundaryProofStateFingerprintWithTerm (← getGoals)
    (← getThe Term.State)
  let actualOptions := boundaryOptionsFingerprint (← getOptions)
  let actualCaller := boundaryCallerIdentity? (← Term.getDeclName?)
  let mut selected? : Option Syntax := none
  for (expected, outcome) in parsedVariants do
    if actualState == expected.state && actualOptions == expected.options &&
        actualCaller == expected.caller then
      if selected?.isSome then
        throwError "ambiguous_boundary_variant"
      selected? := some outcome
  let some selected := selected?
    | throwError "boundary_variant_missing: actualState={repr actualState}; \
        actualOptions={actualOptions}; actualCaller={actualCaller}; \
        expectedStates={repr (parsedVariants.map (·.1.state))}"
  -- Selection itself is observational. Execute the chosen outcome only after
  -- the search has completed, so an intentional recorded failure propagates
  -- to the original surrounding tactic control flow instead of backtracking
  -- into another variant.
  runBoundaryVariantOutcome selected

elab_rules : tactic
  | `(tactic| simp_engine_boundary_apply ($input ==> $result)) =>
      runExplicitApply input result none
  | `(tactic| simp_engine_boundary_apply ($input ==> $result using $proof)) =>
      runExplicitApply input result (some proof)
  | `(tactic| simp_engine_boundary_apply $location:boundaryLocationEvidence) =>
      let locals := location.raw[0].getArgs
      let targetSyntax? := if location.raw[1].isNone then none else some location.raw[1][0]
      runExplicitLocationApply locals targetSyntax?
  | `(tactic| simp_engine_boundary_apply_failure) =>
      throwError "boundary_recorded_tactic_failure"
  | `(tactic| simp_engine_boundary_guard $targetFingerprint:str
      $localContextFingerprint:str $metavariableContextFingerprint:str
      $goalCount:num $optionsFingerprint:str $caller:str) =>
      let expectedGoalCount := goalCount.raw.isNatLit?.getD 0
      runBoundaryGuard targetFingerprint.getString localContextFingerprint.getString
        metavariableContextFingerprint.getString expectedGoalCount optionsFingerprint.getString
        caller.getString
  | `(tactic| simp_engine_boundary_variant_missing) =>
      runBoundaryVariantMissing
  | `(tactic| simp_engine_boundary_occurrence_unobserved) =>
      throwError "boundary_occurrence_unobserved"
  | `(tactic| simp_engine_boundary_select
      $header:boundaryArtifactHeader $variants:boundaryVariant*) =>
      match header with
      | `(boundaryArtifactHeader| (artifact_kind := $kind:str artifact_schema := $schema:num
          selector_schema := $selectorSchema:num semantic_contract := $contract:str
          occurrence_id := $occId:str recorded_module := $moduleName:str)) =>
          let schema := schema.raw.isNatLit?.getD 0
          let selectorSchema := selectorSchema.raw.isNatLit?.getD 0
          runBoundarySelect kind.getString schema selectorSchema contract.getString
            occId.getString moduleName.getString variants
      | _ => throwError "invalid boundary artifact header"

end ExplicitLean.SimpEngine.Boundary
