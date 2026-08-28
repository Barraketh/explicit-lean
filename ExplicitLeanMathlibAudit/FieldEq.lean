module
public meta import ExplicitLean.SimpEngine
public import Mathlib.Tactic.FieldSimp

/-!
  Schema-27 passive instrumentation for Mathlib's `fieldEq` simproc.  This
  module lives in a separate library so the generic ExplicitLean dynamic
  library retains no runtime dependency on Mathlib's compiled symbols.

  The engine-facing hook is deliberately small: the ordinary simproc is run
  once for the authoritative result, and this module runs a source-faithful
  FieldSimp shadow from the saved pre-state.  The audit is diagnostics only;
  the caller keeps the authoritative result and state.
-/

public meta section

open Lean Meta
open Qq

namespace Lean.Meta.Simp.Engine.FieldEqAudit

private abbrev SimpM := Lean.Meta.Simp.SimpM

private structure MutableAudit where
  nextOrdinal : Nat := 0
  calls : Array FieldEqDischargeCall := #[]

private structure MutableCall where
  attempts : Array FieldEqAttempt := #[]
  finalProof? : Option Expr := none
  finalOutcome : FieldEqOutcome := .failed
  rethrowAfterAudit : Bool := false
  terminalExpressionFingerprint : Option String := none
  terminalProofFingerprint : Option String := none
  terminalCache : Option Bool := none

private def sortStrings (xs : List String) : Array String :=
  xs.toArray.qsort (· < ·)

/-- Simp caches may retain keys created under a transient local context after
that context has been left.  Their free variables are still valid cache-key
identities, but `exprFingerprintHash` cannot classify proof subterms without
the departed declarations.  State parity needs the exact stored expression,
not a retyped certificate term, so use Lean's context-free structural hash.
It includes free/metavariable identities and is the same hash used by
`ExprStructMap`; no elaboration, type inference, or instance search occurs. -/
private def stateExprFingerprint (expression : Expr) : String :=
  s!"fieldEq-state-expr-v1:{expression.hash}"

private def resultProofFingerprint (result : Simp.Result) : MetaM String := do
  match result.proof? with
  | none => pure "none"
  | some proof => pure (stateExprFingerprint proof)

private def resultFingerprint (result : Simp.Result) : MetaM String := do
  let expression := stateExprFingerprint result.expr
  let proof ← resultProofFingerprint result
  pure s!"expr={expression};proof={proof};cache={result.cache}"

private def cacheFingerprint (cache : Simp.Cache) : MetaM String := do
  let mut entries : Array String := #[]
  for (key, value) in cache.toList do
    entries := entries.push s!"key={stateExprFingerprint key};value={← resultFingerprint value}"
  pure s!"stage1={cache.stage₁};entries={sortStrings entries.toList}"

private def congrCacheFingerprint (cache : Simp.CongrCache) : MetaM String := do
  let mut entries : Array String := #[]
  for (key, theorem?) in cache.toList do
    let theoremFingerprint ← match theorem? with
      | none => pure "none"
      | some thm => do
          let type := stateExprFingerprint thm.type
          let proof := stateExprFingerprint thm.proof
          pure s!"type={type};proof={proof};args={reprStr thm.argKinds}"
    entries := entries.push
      s!"key={stateExprFingerprint key};value={theoremFingerprint}"
  pure <| sortStrings entries.toList |>.toList |> String.intercalate ","

private def dsimpCacheFingerprint (cache : ExprStructMap Expr) : MetaM String := do
  let mut entries : Array String := #[]
  for (key, value) in cache.toList do
    entries := entries.push
      s!"key={stateExprFingerprint key.val};value={stateExprFingerprint value}"
  pure <| sortStrings entries.toList |>.toList |> String.intercalate ","

private def usedOrigins (state : Simp.State) : Array String :=
  sortStrings <| state.usedTheorems.map.toList.map fun (origin, count) =>
    s!"{reprStr origin}=>{count}"

private def badKeyFingerprint (thm : SimpTheorem) : MetaM String := do
  let proof := stateExprFingerprint thm.proof
  pure (s!"keys={reprStr thm.keys};levels={reprStr thm.levelParams};" ++
    s!"proof={proof};priority={thm.priority};post={thm.post};" ++
    s!"perm={thm.perm};origin={reprStr thm.origin};rfl={thm.rfl};" ++
    s!"backwardRfl={thm.backwardRfl}")

private def diagnosticsFingerprint (diagnostics : Simp.Diagnostics) : MetaM (Array String) := do
  let used := diagnostics.usedThmCounter.toList.map fun (origin, count) =>
    s!"used:{reprStr origin}=>{count}"
  let tried := diagnostics.triedThmCounter.toList.map fun (origin, count) =>
    s!"tried:{reprStr origin}=>{count}"
  let congr := diagnostics.congrThmCounter.toList.map fun (name, count) =>
    s!"congr:{name}=>{count}"
  let mut badKeys : Array String := #[]
  for thm in diagnostics.thmsWithBadKeys.toList do
    badKeys := badKeys.push s!"badKey:{← badKeyFingerprint thm}"
  pure <| sortStrings (used ++ tried ++ congr ++ badKeys.toList)

private def summarizeState (state : Simp.State) : MetaM FieldEqSimpStateSummary := do
  return {
    numSteps := state.numSteps
    cache := ← cacheFingerprint state.cache
    congrCache := ← congrCacheFingerprint state.congrCache
    dsimpCache := ← dsimpCacheFingerprint state.dsimpCache
    usedTheoremOrigins := usedOrigins state
    diagnostics := ← diagnosticsFingerprint state.diag
  }

private def localDeclFingerprint : LocalDecl → MetaM String
  | .cdecl index fvar userName type binderInfo kind => do
      let typeFingerprint := stateExprFingerprint type
      pure <| s!"cdecl:{index}:{reprStr fvar}:{userName}:{reprStr binderInfo}:" ++
        s!"{reprStr kind}:{typeFingerprint}"
  | .ldecl index fvar userName type value nondep kind => do
      let typeFingerprint := stateExprFingerprint type
      let valueFingerprint := stateExprFingerprint value
      pure <| s!"ldecl:{index}:{reprStr fvar}:{userName}:{nondep}:{reprStr kind}:" ++
        s!"{typeFingerprint}:{valueFingerprint}"

private def localContextFingerprint (lctx : LocalContext) : MetaM String := do
  let mut decls : Array String := #[]
  for decl? in lctx.decls.toArray do
    let fingerprint ← match decl? with
      | none => pure "none"
      | some decl => do pure s!"some:{← localDeclFingerprint decl}"
    decls := decls.push fingerprint
  let aux := lctx.auxDeclToFullName.toList.map fun (fvar, name) =>
    s!"{reprStr fvar}=>{name}"
  pure s!"decls={decls};aux={sortStrings aux}"

private def metavarDeclFingerprint (decl : MetavarDecl) : MetaM String :=
  withLCtx decl.lctx decl.localInstances do
    let localInstances ← decl.localInstances.mapM fun localInstance => do
      pure s!"{localInstance.className}:{stateExprFingerprint localInstance.fvar}"
    let lctxFingerprint ← localContextFingerprint decl.lctx
    let typeFingerprint := stateExprFingerprint decl.type
    pure <| s!"user={decl.userName};lctx={lctxFingerprint};" ++
      s!"type={typeFingerprint};depth={decl.depth};" ++
      s!"instances={localInstances};kind={reprStr decl.kind};" ++
      s!"scope={decl.numScopeArgs};index={decl.index}"

private def messageFingerprint (message : Message) : MetaM String := do
  let json ← message.toJson
  pure json.compress

private def messagesFingerprint (messages : PersistentArray Message) : MetaM String := do
  let values ← messages.toArray.mapM messageFingerprint
  pure s!"{values}"

private def metaEffectFingerprint : MetaM String := do
  let mctx ← getMCtx
  let core ← getThe Core.State
  let levelDecls := mctx.lDecls.toList.map fun (mvar, decl) =>
    s!"{reprStr mvar}:depth={decl.depth}:index={decl.index}"
  let mut metavarDecls : Array String := #[]
  for (mvar, decl) in mctx.decls.toList do
    metavarDecls := metavarDecls.push
      s!"{reprStr mvar}:{← metavarDeclFingerprint decl}"
  let userNames := mctx.userNames.toList.map fun (name, mvar) =>
    s!"{name}=>{reprStr mvar}"
  let levelAssignments := mctx.lAssignment.toList.map fun (mvar, value) =>
    s!"{reprStr mvar}={reprStr value}"
  let mut expressionAssignments : Array String := #[]
  for (mvar, value) in mctx.eAssignment.toList do
    expressionAssignments := expressionAssignments.push
      s!"{reprStr mvar}=expr-repr-v1:{hash (reprStr value)}"
  let mut delayedAssignments : Array String := #[]
  for (mvar, assignment) in mctx.dAssignment.toList do
    let fvars := assignment.fvars.map fun fvar => reprStr fvar
    delayedAssignments := delayedAssignments.push
      s!"{reprStr mvar}:fvars={fvars}:pending={reprStr assignment.mvarIdPending}"
  let payload :=
    s!"depth={mctx.depth};levelAssignDepth={mctx.levelAssignDepth};" ++
    s!"lmvarCounter={mctx.lmvarCounter};mvarCounter={mctx.mvarCounter};" ++
    s!"ldecls={sortStrings levelDecls};decls={sortStrings metavarDecls.toList};" ++
    s!"userNames={sortStrings userNames};" ++
    s!"lAssignment={sortStrings levelAssignments};" ++
    s!"eAssignment={sortStrings expressionAssignments.toList};" ++
    s!"dAssignment={sortStrings delayedAssignments.toList};" ++
    s!"reportedMessages={← messagesFingerprint core.messages.reported};" ++
    s!"unreportedMessages={← messagesFingerprint core.messages.unreported};" ++
    s!"loggedKinds={reprStr core.messages.loggedKinds.toList}"
  pure s!"fieldEq-meta-v1:{hash payload}"

private def stepDisposition : Simp.Step → StepDisposition
  | .done _ => .done
  | .visit _ => .visit
  | .continue none => .continueNone
  | .continue (some _) => .continueSome

private def stepResult? : Simp.Step → Option Simp.Result
  | .done result | .visit result | .continue (some result) => some result
  | .continue none => none

private def stepOutput (input : Expr) (step : Simp.Step) : Expr :=
  (stepResult? step).map (·.expr) |>.getD input

private def stepProofFingerprint? (step : Simp.Step) : MetaM (Option String) := do
  match stepResult? step with
  | none => pure none
  | some result => pure <| result.proof?.map stateExprFingerprint

private def stepCache? (step : Simp.Step) : Option Bool :=
  (stepResult? step).map (·.cache)

private def procedureResult (input : Expr) (step : Simp.Step)
    (state : Simp.State) (metaFingerprint : String) : MetaM FieldEqProcedureResult := do
  return {
    disposition := stepDisposition step
    outputFingerprint := stateExprFingerprint (stepOutput input step)
    proofFingerprint := ← stepProofFingerprint? step
    cache := stepCache? step
    simpState := ← summarizeState state
    metaEffectFingerprint := metaFingerprint
  }

private def stepMismatch (authoritative shadow : FieldEqProcedureResult) : Option String :=
  if authoritative.disposition != shadow.disposition then
    some "step disposition"
  else if authoritative.outputFingerprint != shadow.outputFingerprint then
    some "output fingerprint"
  else if authoritative.proofFingerprint != shadow.proofFingerprint then
    some "proof structural fingerprint"
  else if authoritative.cache != shadow.cache then
    some "cache flag"
  else if authoritative.simpState != shadow.simpState then
    some "Simp state"
  else if authoritative.metaEffectFingerprint != shadow.metaEffectFingerprint then
    some "tracked Meta effects"
  else
    none

private def addCall (audit : IO.Ref MutableAudit) (call : FieldEqDischargeCall) : MetaM Unit :=
  audit.modify fun state => { state with calls := state.calls.push call }

private def reserveCall (audit : IO.Ref MutableAudit) : MetaM Nat :=
  audit.modifyGet fun state =>
    (state.nextOrdinal, { state with nextOrdinal := state.nextOrdinal + 1 })

/-- Source-identical copy of Lean's private
`Simp.dischargeUsingAssumption?`.  Mathlib's field discharger calls that
private helper, so an external audit module cannot name it directly. -/
private def dischargeUsingAssumptionAudit? (prop : Expr) : SimpM (Option Expr) := do
  let lctxInitIndices := (← readThe Simp.Context).lctxInitIndices
  let contextual := (← Simp.getConfig).contextual
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if !contextual && localDecl.index >= lctxInitIndices then
      return none
    else if (← Simp.withSimpMetaConfig <| isDefEq prop localDecl.type) then
      return some localDecl.toExpr
    else
      return none

private def fieldEqLemmas : List Name :=
  [``two_ne_zero, ``three_ne_zero, ``four_ne_zero, ``mul_ne_zero,
    ``pow_ne_zero, ``zpow_ne_zero, ``Nat.cast_add_one_ne_zero]

private def normNumAttempt (prop : Expr) : MetaM (FieldEqOutcome × Option Expr) := do
  if !prop.isAppOf ``Ne then
    return (.notApplicable, none)
  try
    let result ← Mathlib.Meta.NormNum.derive prop
    match result with
    | .isTrue proof => pure (.success, some proof)
    | _ => pure (.returnedNonTrue, none)
  catch _ =>
    pure (.threw, none)

private abbrev DischargeFn :=
  Option Nat → Nat → Expr → SimpM (Option Expr)

private def recursiveSimpAttempt (parent : Nat)
    (depth : Nat) (prop : Expr) (dischargeFn : DischargeFn) :
    SimpM (FieldEqOutcome × Option Expr × Option Simp.Result × Simp.State × Simp.State) := do
  let discharge : Simp.Discharge := fun child =>
    dischargeFn (some parent) (depth + 1) child
  Simp.withIncDischargeDepth do
    let ctx ← readThe Simp.Context
    let ctx' := ctx.setSimpTheorems <| ctx.simpTheorems.push <|
      ← fieldEqLemmas.foldlM (SimpTheorems.addConst · · (post := false)) {}
    let stats : Simp.Stats := { (← get) with }
    let initial : Simp.State := { stats with }
    let recursive? ← try
      some <$> Lean.Meta.simpCore prop ctx' #[(← Simp.getSimprocs)]
        (some discharge) initial
    catch _ =>
      pure none
    match recursive? with
    | none =>
        pure (.threw, none, none, initial, initial)
    | some (simpResult, state') =>
        set { (← get) with
          usedTheorems := state'.usedTheorems
          diag := state'.diag }
        if simpResult.expr.isConstOf ``True then
          try
            let proof ← mkOfEqTrue (← simpResult.getProof)
            pure (.success, some proof, some simpResult, initial, state')
          catch _ =>
            pure (.conversionFailed, none, some simpResult, initial, state')
        else
          pure (.terminalNotTrue, none, some simpResult, initial, state')

private partial def instrumentedDischarge (audit : IO.Ref MutableAudit)
    (parentOrdinal : Option Nat) (depth : Nat) (prop : Expr) : SimpM (Option Expr) := do
  let ordinal ← reserveCall audit
  let proposition ← liftM (exprFingerprint prop)
  let size ← liftM (exprSize prop)
  let callState ← IO.mkRef ({} : MutableCall)
  let runAttempt (strategy : FieldEqStrategy)
      (action : SimpM (FieldEqOutcome × Option Expr × Option Simp.Result ×
        Option Simp.State × Option Simp.State)) : SimpM Bool := do
    let beforeMeta ← liftM metaEffectFingerprint
    let action? ← try
      some <$> action
    catch _ =>
      pure none
    let (outcome, proof?, terminal?, beforeRecursive?, afterRecursive?) :=
      action?.getD (.threw, none, none, none, none)
    let afterMeta ← liftM metaEffectFingerprint
    let proofFingerprint ← match proof? with
      | none => pure none
      | some proof => pure (some (stateExprFingerprint proof))
    let terminalExpressionFingerprint ← match terminal? with
      | none => pure none
      | some result => pure (some (stateExprFingerprint result.expr))
    let terminalProofFingerprint ← match terminal? with
      | none => pure none
      | some result => match result.proof? with
          | none => pure none
          | some proof => pure (some (stateExprFingerprint proof))
    let terminalCache := terminal?.map (·.cache)
    let beforeSimpState ← match beforeRecursive? with
      | none => pure none
      | some state => some <$> liftM (summarizeState state)
    let afterSimpState ← match afterRecursive? with
      | none => pure none
      | some state => some <$> liftM (summarizeState state)
    let attempt : FieldEqAttempt := {
      strategy
      outcome
      proofFingerprint
      beforeMetaEffectFingerprint := beforeMeta
      afterMetaEffectFingerprint := afterMeta
      beforeSimpState
      afterSimpState
      terminalExpressionFingerprint
      terminalProofFingerprint
      terminalCache
    }
    callState.modify fun state => { state with
      attempts := state.attempts.push attempt
      terminalExpressionFingerprint := terminalExpressionFingerprint
      terminalProofFingerprint := terminalProofFingerprint
      terminalCache := terminalCache
      finalOutcome := outcome }
    match outcome, proof? with
    | .success, some proof =>
        callState.modify fun state => { state with
          finalOutcome := .success
          finalProof? := some proof }
        return true
    | _, _ =>
        return false
  let solved ← runAttempt .assumption do
    match ← dischargeUsingAssumptionAudit? prop with
    | some proof => pure (.success, some proof, none, none, none)
    | none => pure (.notApplicable, none, none, none, none)
  unless solved do
    let solved ← runAttempt .normNum do
      let (outcome, proof?) ← liftM (normNumAttempt prop)
      pure (outcome, proof?, none, none, none)
    unless solved do
      let solved ← runAttempt .positivity do
        try
          let proof ← liftM (Mathlib.Meta.Positivity.solve prop)
          pure (.success, some proof, none, none, none)
        catch _ =>
          pure (.threw, none, none, none, none)
      unless solved do
        let _ ← runAttempt .recursiveSimp do
          let (outcome, proof?, terminal?, before, after) ←
            recursiveSimpAttempt ordinal depth prop
              (fun parent depth prop => instrumentedDischarge audit parent depth prop)
          pure (outcome, proof?, terminal?, some before, some after)
        if (← callState.get).finalOutcome == .threw then
          callState.modify fun state => { state with rethrowAfterAudit := true }
  let callState' ← callState.get
  let finalProofFingerprint ← match callState'.finalProof? with
    | none => pure none
    | some proof => pure (some (stateExprFingerprint proof))
  let call : FieldEqDischargeCall := {
    ordinal
    parentOrdinal
    recursionDepth := depth
    proposition
    size
    attempts := callState'.attempts
    outcome := callState'.finalOutcome
    proofFingerprint := finalProofFingerprint
    terminalExpressionFingerprint := callState'.terminalExpressionFingerprint
    terminalProofFingerprint := callState'.terminalProofFingerprint
    terminalCache := callState'.terminalCache
  }
  addCall audit call
  if callState'.rethrowAfterAudit then
    throwError "fieldEq audit recursive simp threw"
  return callState'.finalProof?

private def shadowProc (input : Expr) (ctx : Simp.Context) (audit : IO.Ref MutableAudit) :
    SimpM Simp.Step := do
  let disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type) := fun e => do
    let (proof?, _) ← (instrumentedDischarge audit none 0 e).run ctx
    let some proof := proof? | throwError "fieldEq audit discharger failed"
    return proof
  try
    let result ← Mathlib.Tactic.AtomM.run .reducible <|
      Mathlib.Tactic.FieldSimp.reduceProp disch input
    return .visit <| ← result.mkEqTrans (← Lean.Meta.simpOnlyNames
      [``one_div, ``mul_inv] result.expr)
  catch _ =>
    return .continue

private def auditHook (input : Expr) (proc : Simp.Simproc) : SimpM (Simp.Step × FieldEqAudit) := do
  let audit ← IO.mkRef ({} : MutableAudit)
  let initialState ← get
  let initialMetaState ← liftM saveFullMetaState
  let initialMeta ← liftM metaEffectFingerprint
  let authoritative ← proc input
  let authoritativeState ← get
  let authoritativeMeta ← liftM metaEffectFingerprint
  let authoritativeEvidence ←
    procedureResult input authoritative authoritativeState authoritativeMeta
  let authoritativeMetaState ← liftM saveFullMetaState
  liftM initialMetaState.restore
  set initialState
  try
    let ctx ← Simp.getContext
    let shadow ← shadowProc input ctx audit
    let shadowState ← get
    let shadowMeta ← liftM metaEffectFingerprint
    let shadowEvidence ← procedureResult input shadow shadowState shadowMeta
    let evidence : FieldEqShadowEvidence := {
      exact := (stepMismatch authoritativeEvidence shadowEvidence).isNone
      authoritative := authoritativeEvidence
      shadow := shadowEvidence
      diagnostic := stepMismatch authoritativeEvidence shadowEvidence
    }
    if let some mismatch := evidence.diagnostic then
      throwError "fieldEq audit shadow mismatch: {mismatch}"
    let calls := (← audit.get).calls.qsort (fun lhs rhs => lhs.ordinal < rhs.ordinal)
    return (authoritative, {
      initialMetaEffectFingerprint := initialMeta
      authoritativeFinalMetaEffectFingerprint := authoritativeMeta
      shadowFinalMetaEffectFingerprint := shadowMeta
      dischargeCalls := calls
      shadow := evidence
    })
  finally
    liftM authoritativeMetaState.restore
    set authoritativeState

def withFieldEqAudit (methods : Lean.Meta.Simp.Engine.Methods) :
    Lean.Meta.Simp.Engine.Methods :=
  { methods with fieldEqAudit? := some auditHook }

end Lean.Meta.Simp.Engine.FieldEqAudit
