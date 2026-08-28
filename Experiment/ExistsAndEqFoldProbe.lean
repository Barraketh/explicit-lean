import Mathlib.Tactic.Simproc.ExistsAndEq
import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace ExistsAndEqFoldProbe

open Lean.Meta.Simp.Engine

def natType : Expr := mkConst ``Nat

def natLiteral (value : Nat) : Expr :=
  mkRawNatLit value

def natEq (lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.succ .zero]) natType lhs rhs

def natAnd (lhs rhs : Expr) : Expr :=
  mkApp2 (mkConst ``And) lhs rhs

def natLe (lhs rhs : Expr) : Expr :=
  mkApp2 (mkConst ``Nat.le) lhs rhs

def natSucc (value : Expr) : Expr :=
  mkApp (mkConst ``Nat.succ) value

def natAdd (lhs rhs : Expr) : Expr :=
  mkApp2 (mkConst ``Nat.add) lhs rhs

def natExists (name : Name) (body : Expr) : Expr :=
  mkApp2 (mkConst ``Exists [.succ .zero]) natType
    (mkLambda name BinderInfo.default natType body)

def existsWithType (name : Name) (binderType body : Expr) : Expr :=
  mkApp2 (mkConst ``Exists [.succ .zero]) binderType
    (mkLambda name BinderInfo.default binderType body)

def doneSimproc : Simp.Simproc := fun expression =>
  pure (.done { expr := expression })

def noOpSimproc : Simp.Simproc := fun _ =>
  pure .continue

def doneEngineSimproc : Simp.Engine.Simproc := fun expression =>
  pure (.done { expr := expression })

def noOpEngineSimproc : Simp.Engine.Simproc := fun _ =>
  pure .continue

def existsSets : MetaM Simp.SimprocsArray := do
  let set ← ({} : Simp.Simprocs).add `ExistsAndEq.existsAndEq false
  pure #[set]

def existsPostSets : MetaM Simp.SimprocsArray := do
  let set ← ({} : Simp.Simprocs).add `ExistsAndEq.existsAndEq true
  pure #[set]

def sourceMethodsPre (sets : Simp.SimprocsArray) : Simp.Methods :=
  { Simp.mkDefaultMethodsCore #[] with
    pre := Simp.userPreSimprocs sets
    post := doneSimproc
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }

def recordingMethodsPre (sets : Simp.SimprocsArray) : Simp.Engine.Methods :=
  { Simp.Engine.mkDefaultMethodsCore #[] with
    pre := Simp.Engine.userPreSimprocsRecorded sets
    post := doneEngineSimproc
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue
    base := sourceMethodsPre sets }

def sourceMethodsPost (sets : Simp.SimprocsArray) : Simp.Methods :=
  { Simp.mkDefaultMethodsCore #[] with
    pre := noOpSimproc
    post := Simp.userPreSimprocs sets
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }

def recordingMethodsPost (sets : Simp.SimprocsArray) : Simp.Engine.Methods :=
  { Simp.Engine.mkDefaultMethodsCore #[] with
    pre := noOpEngineSimproc
    post := Simp.Engine.userPreSimprocsRecorded sets
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue
    base := sourceMethodsPost sets }

def sourceMethodsRegistryPost (sets : Simp.SimprocsArray) : Simp.Methods :=
  { Simp.mkDefaultMethodsCore #[] with
    pre := noOpSimproc
    post := Simp.userPostSimprocs sets
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }

def recordingMethodsRegistryPost (sets : Simp.SimprocsArray) : Simp.Engine.Methods :=
  { Simp.Engine.mkDefaultMethodsCore #[] with
    pre := noOpEngineSimproc
    post := Simp.Engine.userPostSimprocsRecorded sets
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue
    base := sourceMethodsRegistryPost sets }

def sortStrings (values : List String) : List String :=
  values.toArray.qsort (· < ·) |>.toList

def listFingerprint (values : List String) : String :=
  String.intercalate "," (sortStrings values)

private structure StateExprIds where
  fvars : FVarIdSet := {}
  mvars : MVarIdSet := {}

private partial def collectStateExprIds (expression : Expr)
    (initial : StateExprIds) : StateExprIds :=
  match expression with
  | .fvar id => { initial with fvars := initial.fvars.insert id }
  | .mvar id => { initial with mvars := initial.mvars.insert id }
  | .app function argument =>
      collectStateExprIds argument (collectStateExprIds function initial)
  | .lam _ type body _ | .forallE _ type body _ =>
      collectStateExprIds body (collectStateExprIds type initial)
  | .letE _ type value body _ =>
      collectStateExprIds body (collectStateExprIds value
        (collectStateExprIds type initial))
  | .mdata _ body | .proj _ _ body => collectStateExprIds body initial
  | _ => initial

private def collectStateResultIds (result : Simp.Result)
    (initial : StateExprIds) : StateExprIds :=
  let initial := collectStateExprIds result.expr initial
  match result.proof? with
  | some proof => collectStateExprIds proof initial
  | none => initial

private def collectStateSimpTheoremIds (thm : SimpTheorem)
    (initial : StateExprIds) : StateExprIds :=
  collectStateExprIds thm.proof initial

private def collectStateIds (state : Simp.State) : StateExprIds := Id.run do
  let mut ids : StateExprIds := {}
  for (key, value) in state.cache.toList do
    ids := collectStateResultIds value (collectStateExprIds key ids)
  for (key, value) in state.congrCache.toList do
    ids := collectStateExprIds key ids
    match value with
    | some thm => ids := collectStateExprIds thm.type (collectStateExprIds thm.proof ids)
    | none => pure ()
  for (key, value) in state.dsimpCache.toList do
    ids := collectStateExprIds value (collectStateExprIds key.val ids)
  for thm in state.diag.thmsWithBadKeys.toList do
    ids := collectStateSimpTheoremIds thm ids
  ids

private structure StateExprCanon where
  fvars : Array FVarId := #[]
  mvars : Array MVarId := #[]

private partial def canonicalStateExprWith (expression : Expr)
    (initial : StateExprCanon) : String × StateExprCanon :=
  let rec go (expression : Expr) (state : StateExprCanon) :
      String × StateExprCanon :=
    match expression with
    | .bvar index => (s!"bvar:{index}", state)
    | .fvar id =>
        let (index, fvars) := match state.fvars.findIdx? (· == id) with
          | some index => (index, state.fvars)
          | none => (state.fvars.size, state.fvars.push id)
        (s!"fvar:{index}", { state with fvars })
    | .mvar id =>
        let (index, mvars) := match state.mvars.findIdx? (· == id) with
          | some index => (index, state.mvars)
          | none => (state.mvars.size, state.mvars.push id)
        (s!"mvar:{index}", { state with mvars })
    | .sort level => (s!"sort:{reprStr level}", state)
    | .const name levels => (s!"const:{name}:{reprStr levels}", state)
    | .lit literal => (s!"lit:{reprStr literal}", state)
    | .app function argument =>
        let (function, state) := go function state
        let (argument, state) := go argument state
        (s!"app({function},{argument})", state)
    | .lam _ type body binderInfo =>
        let (type, state) := go type state
        let (body, state) := go body state
        (s!"lam({reprStr binderInfo},{type},{body})", state)
    | .forallE _ type body binderInfo =>
        let (type, state) := go type state
        let (body, state) := go body state
        (s!"forall({reprStr binderInfo},{type},{body})", state)
    | .letE _ type value body nondep =>
        let (type, state) := go type state
        let (value, state) := go value state
        let (body, state) := go body state
        (s!"let({nondep},{type},{value},{body})", state)
    | .mdata data body =>
        let (body, state) := go body state
        (s!"mdata({reprStr data},{body})", state)
    | .proj name index st =>
        let (st, state) := go st state
        (s!"proj({name},{index},{st})", state)
  go expression initial

private def canonicalStateResult (result : Simp.Result) (initial : StateExprCanon) :
    String × StateExprCanon :=
  let (expression, state) := canonicalStateExprWith result.expr initial
  let (proof, state) := match result.proof? with
    | none => ("none", state)
    | some proof =>
        let (proof, state) := canonicalStateExprWith proof state
        (proof, state)
  (s!"{expression}|{proof}|{result.cache}", state)

private def canonicalStateCache (cache : Simp.Cache) (initial : StateExprCanon) :
    String × StateExprCanon := Id.run do
  let mut state := initial
  let mut entries : Array String := #[]
  for (key, value) in cache.toList do
    let (key, state') := canonicalStateExprWith key state
    state := state'
    let (value, state') := canonicalStateResult value state
    state := state'
    entries := entries.push s!"{key}=>{value}"
  return (s!"stage₁={cache.stage₁};{listFingerprint entries.toList}", state)

private def canonicalStateCongrTheorem (theorem? : Option CongrTheorem)
    (initial : StateExprCanon) : String × StateExprCanon :=
  match theorem? with
  | none => ("none", initial)
  | some thm =>
      let (type, state) := canonicalStateExprWith thm.type initial
      let (proof, state) := canonicalStateExprWith thm.proof state
      (s!"{type}|{proof}|{reprStr thm.argKinds}", state)

private def canonicalStateCongrCache (cache : ExprMap (Option CongrTheorem))
    (initial : StateExprCanon) : String × StateExprCanon := Id.run do
  let mut state := initial
  let mut entries : Array String := #[]
  for (key, value) in cache.toList do
    let (key, state') := canonicalStateExprWith key state
    state := state'
    let (value, state') := canonicalStateCongrTheorem value state
    state := state'
    entries := entries.push s!"{key}=>{value}"
  return (listFingerprint entries.toList, state)

private def canonicalStateDsimpCache (cache : ExprStructMap Expr)
    (initial : StateExprCanon) : String × StateExprCanon := Id.run do
  let mut state := initial
  let mut entries : Array String := #[]
  for (key, value) in cache.toList do
    let (key, state') := canonicalStateExprWith key.val state
    state := state'
    let (value, state') := canonicalStateExprWith value state
    state := state'
    entries := entries.push s!"{key}=>{value}"
  return (listFingerprint entries.toList, state)

private def canonicalStateSimpTheorem (thm : SimpTheorem) (initial : StateExprCanon) :
    String × StateExprCanon :=
  let (proof, state) := canonicalStateExprWith thm.proof initial
  (s!"keys={reprStr thm.keys}|levels={reprStr thm.levelParams}|" ++
    s!"proof={proof}|priority={thm.priority}|" ++
    s!"post={thm.post}|perm={thm.perm}|origin={reprStr thm.origin}|" ++
    s!"rfl={thm.rfl}|backwardRfl={thm.backwardRfl}", state)

private def canonicalStateDiagnostics (diagnostics : Simp.Diagnostics)
    (initial : StateExprCanon) : String × StateExprCanon := Id.run do
  let used := diagnostics.usedThmCounter.toList.map fun (origin, count) =>
    s!"{reprStr origin}=>{count}"
  let tried := diagnostics.triedThmCounter.toList.map fun (origin, count) =>
    s!"{reprStr origin}=>{count}"
  let congr := diagnostics.congrThmCounter.toList.map fun (name, count) =>
    s!"{name}=>{count}"
  let mut state := initial
  let mut badKeys : Array String := #[]
  for thm in diagnostics.thmsWithBadKeys.toList do
    let (thm, state') := canonicalStateSimpTheorem thm state
    state := state'
    badKeys := badKeys.push thm
  return (s!"used={listFingerprint used};tried={listFingerprint tried};" ++
    s!"congr={listFingerprint congr};badKeys={listFingerprint badKeys.toList}", state)

structure StateSummary where
  numSteps : Nat
  cache : String
  congrCache : String
  dsimpCache : String
  usedTheorems : String
  diagnostics : String
  deriving BEq, Repr

def summarizeState (state : Simp.State) : MetaM StateSummary := do
  let ids := collectStateIds state
  let fvars := ids.fvars.toArray.qsort (fun lhs rhs => Name.lt lhs.name rhs.name)
  let mvars := ids.mvars.toArray.qsort (fun lhs rhs => Name.lt lhs.name rhs.name)
  let initial : StateExprCanon := { fvars, mvars }
  let (cache, canon) := canonicalStateCache state.cache initial
  let (congrCache, canon) := canonicalStateCongrCache state.congrCache canon
  let (dsimpCache, canon) := canonicalStateDsimpCache state.dsimpCache canon
  let (diagnostics, _) := canonicalStateDiagnostics state.diag canon
  pure {
    numSteps := state.numSteps
    cache
    congrCache
    dsimpCache
    usedTheorems := listFingerprint (state.usedTheorems.toArray.toList.map reprStr)
    diagnostics
  }

private def metaEffectSummary : MetaM String := do
  let mctx ← getMCtx
  let core ← getThe Core.State
  pure <| s!"depth={mctx.depth};levelAssignDepth={mctx.levelAssignDepth};" ++
    s!"lmvarCounter={mctx.lmvarCounter};mvarCounter={mctx.mvarCounter};" ++
    s!"ldecls={mctx.lDecls.toList.length};decls={mctx.decls.toList.length};" ++
    s!"userNames={mctx.userNames.toList.length};" ++
    s!"lAssignment={mctx.lAssignment.toList.length};eAssignment={mctx.eAssignment.toList.length};" ++
    s!"dAssignment={mctx.dAssignment.toList.length};messages={core.messages.reported.size + core.messages.unreported.size};" ++
    s!"loggedKinds={core.messages.loggedKinds.toList.length}"

def jsonRoundtrip {α : Type} [BEq α] [ToJson α] [FromJson α]
    (label : String) (value : α) : MetaM Unit := do
  let decoded ← match Lean.fromJson? (Lean.toJson value) with
    | .ok value => pure value
    | .error message => throwError "{label}: JSON decode failed: {message}"
  unless decoded == value do
    throwError "{label}: JSON roundtrip mismatch"

def semanticEvents (program : Simp.Engine.Program) : Array Simp.Engine.Event :=
  program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc fold => fold.candidates.any fun candidate =>
        candidate.declaration == `ExistsAndEq.existsAndEq
    | _ => false

def checkExistsObservations (label : String)
    (trace : Simp.Engine.SimprocTrace) (post : Bool) (changedCount : Nat) : MetaM Unit := do
  let observations := trace.observations
  unless !observations.isEmpty do
    throwError "{label}: no ExistsAndEq observations were recorded"
  let mut changed := 0
  for observation in observations do
    unless observation.name == `ExistsAndEq.existsAndEq &&
        observation.phase == (if post then .post else .pre) &&
        observation.setIndex == 0 && observation.procedureKind == .simp &&
        observation.numExtraArgs == 0 && observation.executed do
      throwError "{label}: unexpected observation protocol: {repr observation}"
    if observation.outputChanged then
      changed := changed + 1
      unless observation.stepDisposition == .visit && observation.proofPresent &&
          observation.cache == some true && observation.outputSize.isSome do
        throwError "{label}: changed observation protocol: {repr observation}"
    else
      unless observation.inputFingerprint == observation.outputFingerprint &&
          observation.stepDisposition == .continueNone && !observation.proofPresent &&
          observation.cache.isNone && observation.outputSize.isNone do
        throwError "{label}: no-result observation was not inert: {repr observation}"
  unless changed == changedCount do
    throwError "{label}: expected {changedCount} changed observations, got {changed}"

structure Artifacts where
  expression : Expr
  reference : Simp.Result
  recorded : Simp.Result
  referenceState : Simp.State
  recordedState : Simp.State
  recording : Simp.Engine.Recording
  context : Simp.Context
  config : Simp.Engine.ReplayConfig

def runCase (label : String) (expression : Expr) (post : Bool) : MetaM Artifacts := do
  let sets ← existsSets
  let sourceMethods := if post then sourceMethodsPost sets else sourceMethodsPre sets
  let recordingMethods := if post then recordingMethodsPost sets else recordingMethodsPre sets
  let context ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let saved ← Meta.saveState
  let (reference, referenceState) ←
    Simp.mainCore expression context (methods := sourceMethods)
  let referenceSummary ← summarizeState referenceState
  saved.restore
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression context (methods := recordingMethods)
  unless Expr.equal reference.expr recorded.expr do
    throwError "{label}: reference/record result mismatch"
  unless reference.proof?.isSome == recorded.proof?.isSome do
    throwError "{label}: reference/record proof-presence mismatch"
  match reference.proof?, recorded.proof? with
  | some referenceProof, some recordedProof =>
      unless Expr.equal referenceProof recordedProof do
        throwError "{label}: reference/record proof-expression mismatch"
  | _, _ => pure ()
  unless reference.cache == recorded.cache do
    throwError "{label}: reference/record cache mismatch"
  let recordedSummary ← summarizeState recordedState
  unless referenceSummary == recordedSummary do
    throwError "{label}: reference/record state mismatch"
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  checkExistsObservations label recording.simprocs post 1
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  let events := semanticEvents recording.program
  unless events.size == 1 do
    throwError "{label}: expected one ExistsAndEq semantic event, got {events.size}"
  let some event := events[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == (if post then .post else .pre) && fold.candidates.size == 1 &&
      fold.finalDisposition == .visit && fold.finalProofPresent &&
      fold.finalCache == some true && event.stepDisposition == .visit do
    throwError "{label}: wrong fold protocol: {repr fold}"
  let candidate := fold.candidates[0]!
  unless candidate.declaration == `ExistsAndEq.existsAndEq &&
      candidate.procedureKind == .simp && candidate.setIndex == 0 &&
      !candidate.registryPost && candidate.disposition == .visit &&
      candidate.proofPresent && candidate.cache == some true &&
      candidate.numExtraArgs == 0 && candidate.extraArgumentFingerprints.isEmpty do
    throwError "{label}: wrong candidate protocol: {repr candidate}"
  match candidate.semantics with
  | .existentialEqualityElim derivation =>
      jsonRoundtrip (label ++ ":derivation-json") derivation
  | _ => throwError "{label}: candidate has wrong semantics"
  jsonRoundtrip (label ++ ":fold-json") fold
  jsonRoundtrip (label ++ ":trace-json") recording.simprocs
  let config ← Simp.Engine.replayConfigOfContext context
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay expression context config recording.program
  unless Expr.equal recorded.expr replayed.expr do
    throwError "{label}: replay result mismatch"
  unless recorded.proof?.isSome == replayed.proof?.isSome do
    throwError "{label}: replay proof-presence mismatch"
  match recorded.proof?, replayed.proof? with
  | some recordedProof, some replayedProof =>
      unless exprEqualIgnoringBinderNames recordedProof replayedProof do
        throwError "{label}: replay proof semantic-structure mismatch"
  | _, _ => pure ()
  unless recorded.cache == replayed.cache do
    throwError "{label}: replay cache mismatch"
  let replayedSummary ← summarizeState replayedState
  unless recordedSummary == replayedSummary do
    throwError "{label}: replay state mismatch"
  pure {
    expression
    reference
    recorded
    referenceState
    recordedState
    recording
    context
    config
  }

def runLoopCase (label : String) (expression : Expr) : MetaM Artifacts := do
  let sets ← existsSets
  let sourceMethods := sourceMethodsPre sets
  let recordingMethods := recordingMethodsPre sets
  let context ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let saved ← Meta.saveState
  let (reference, referenceState) ←
    Simp.mainCore expression context (methods := sourceMethods)
  let referenceSummary ← summarizeState referenceState
  saved.restore
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression context (methods := recordingMethods)
  let recordedSummary ← summarizeState recordedState
  unless Expr.equal reference.expr recorded.expr do
    throwError "{label}: reference/record result mismatch"
  unless reference.proof?.isSome == recorded.proof?.isSome do
    throwError "{label}: reference/record proof-presence mismatch"
  match reference.proof?, recorded.proof? with
  | some referenceProof, some recordedProof =>
      unless Expr.equal referenceProof recordedProof do
        throwError "{label}: reference/record proof-expression mismatch"
  | _, _ => pure ()
  unless reference.cache == recorded.cache && referenceSummary == recordedSummary do
    throwError "{label}: reference/record state or cache mismatch"
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  checkExistsObservations label recording.simprocs false 2
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  let events := semanticEvents recording.program
  unless events.size == 2 do
    throwError "{label}: expected two ExistsAndEq semantic events, got {events.size}"
  for event in events do
    let .semanticSimproc fold := event.operation | unreachable!
    unless fold.phase == .pre && fold.candidates.size == 1 &&
        fold.finalDisposition == .visit && fold.finalProofPresent &&
        fold.finalCache == some true && event.stepDisposition == .visit do
      throwError "{label}: wrong loop fold protocol: {repr fold}"
    let candidate := fold.candidates[0]!
    unless candidate.declaration == `ExistsAndEq.existsAndEq &&
        candidate.procedureKind == .simp && candidate.setIndex == 0 &&
        !candidate.registryPost && candidate.disposition == .visit &&
        candidate.proofPresent && candidate.cache == some true &&
        candidate.numExtraArgs == 0 && candidate.extraArgumentFingerprints.isEmpty do
      throwError "{label}: wrong loop candidate protocol: {repr candidate}"
    match candidate.semantics with
    | .existentialEqualityElim derivation =>
        jsonRoundtrip (label ++ ":derivation-json") derivation
    | _ => throwError "{label}: loop candidate has wrong semantics"
    jsonRoundtrip (label ++ ":fold-json") fold
  jsonRoundtrip (label ++ ":trace-json") recording.simprocs
  let config ← Simp.Engine.replayConfigOfContext context
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay expression context config recording.program
  unless Expr.equal recorded.expr replayed.expr do
    throwError "{label}: replay result mismatch"
  unless recorded.proof?.isSome == replayed.proof?.isSome do
    throwError "{label}: replay proof-presence mismatch"
  match recorded.proof?, replayed.proof? with
  | some recordedProof, some replayedProof =>
      unless exprEqualIgnoringBinderNames recordedProof replayedProof do
        throwError "{label}: replay proof semantic-structure mismatch"
  | _, _ => pure ()
  unless recorded.cache == replayed.cache do
    throwError "{label}: replay cache mismatch"
  let replayedSummary ← summarizeState replayedState
  unless recordedSummary == replayedSummary do
    throwError "{label}: replay state mismatch"
  pure {
    expression
    reference
    recorded
    referenceState
    recordedState
    recording
    context
    config
  }

def expectReplayReject (label : String) (artifacts : Artifacts)
    (program : Simp.Engine.Program := artifacts.recording.program)
    (trace : Simp.Engine.SimprocTrace := artifacts.recording.simprocs) : MetaM Nat := do
  let saved ← Meta.saveState
  let succeeded ← try
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations program trace
    let (_, replayedState) ←
      Simp.Engine.mainCoreReplay artifacts.expression artifacts.context artifacts.config program
    let replayedSummary ← summarizeState replayedState
    let recordedSummary ← summarizeState artifacts.recordedState
    unless replayedSummary == recordedSummary do
      throwError "{label}: mutated replay state mismatch"
    pure true
  catch _ => pure false
  saved.restore
  unless !succeeded do
    throwError "{label}: mutation was accepted"
  pure 1

def basicLeft : Expr :=
  natExists `a (natEq (mkBVar 0) (natLiteral 3))

def basicRight : Expr :=
  natExists `a (natEq (natLiteral 3) (mkBVar 0))

def nestedSuccLeft : Expr :=
  let nestedBody := natEq (mkBVar 1) (natSucc (mkBVar 0))
  let body := natAnd (natLe (mkBVar 0) (mkBVar 0)) (natExists `b nestedBody)
  natExists `a body

def nestedSuccRight : Expr :=
  let nestedBody := natEq (natSucc (mkBVar 0)) (mkBVar 1)
  let body := natAnd (natLe (mkBVar 0) (mkBVar 0)) (natExists `b nestedBody)
  natExists `a body

def multipleCrossed : Expr :=
  let terminal := natEq (mkBVar 2) (natAdd (mkBVar 1) (mkBVar 0))
  let nested := natExists `c terminal
  let body := natAnd (natLe (mkBVar 0) (mkBVar 0)) (natExists `b nested)
  natExists `a body

def nestedAndLeft : Expr :=
  let terminal := natEq (mkBVar 1) (natSucc (mkBVar 0))
  let nested := natAnd (natExists `b terminal) (natLe (mkBVar 0) (mkBVar 0))
  let body := natAnd (natLe (mkBVar 0) (mkBVar 0)) nested
  natExists `a body

def nestedAndRight : Expr :=
  let terminal := natEq (mkBVar 1) (natSucc (mkBVar 0))
  let nested := natAnd (natLe (mkBVar 0) (mkBVar 0)) (natExists `b terminal)
  let body := natAnd (natLe (mkBVar 0) (mkBVar 0)) nested
  natExists `a body

def noRoute : Expr :=
  natExists `a (natLe (mkBVar 0) (mkBVar 0))

def dependentCrossedType : Expr :=
  let nestedType := mkApp (mkConst ``Fin) (mkBVar 0)
  let nestedBody := natEq (mkBVar 1) (mkBVar 1)
  natExists `a (existsWithType `b nestedType nestedBody)

def outerDependentReplacement : Expr :=
  natExists `a (natEq (mkBVar 0) (natSucc (mkBVar 0)))

def malformedShape : Expr :=
  natAnd (natLe (natLiteral 0) (natLiteral 0))
    (natEq (natLiteral 1) (natLiteral 1))

def runNoResultCase (label : String) (expression : Expr) (post : Bool)
    (expectObservation : Bool := true) : MetaM Unit := do
  let sets ← existsSets
  let sourceMethods := if post then sourceMethodsPost sets else sourceMethodsPre sets
  let recordingMethods := if post then recordingMethodsPost sets else recordingMethodsPre sets
  let context ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let initialMetaEffect ← metaEffectSummary
  let saved ← Meta.saveState
  let (reference, referenceState) ←
    Simp.mainCore expression context (methods := sourceMethods)
  let referenceSummary ← summarizeState referenceState
  let sourceMetaEffect ← metaEffectSummary
  saved.restore
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression context (methods := recordingMethods)
  let recordingMetaEffect ← metaEffectSummary
  let recordedSummary ← summarizeState recordedState
  unless sourceMetaEffect == initialMetaEffect && recordingMetaEffect == initialMetaEffect do
    throwError "{label}: no-result path changed mctx or message state"
  unless Expr.equal reference.expr recorded.expr &&
      reference.proof?.isSome == recorded.proof?.isSome &&
      reference.cache == recorded.cache && referenceSummary == recordedSummary do
    throwError "{label}: reference/record mismatch"
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  if expectObservation then
    checkExistsObservations label recording.simprocs post 0
  else
    unless recording.simprocs.observations.isEmpty do
      throwError "{label}: unexpected simproc observation"
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  unless (semanticEvents recording.program).isEmpty do
    throwError "{label}: unexpected semantic event"
  jsonRoundtrip (label ++ ":trace-json") recording.simprocs
  let config ← Simp.Engine.replayConfigOfContext context
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay expression context config recording.program
  unless Expr.equal recorded.expr replayed.expr &&
      recorded.proof?.isSome == replayed.proof?.isSome &&
      recorded.cache == replayed.cache do
    throwError "{label}: replay result mismatch"
  unless recordedSummary == (← summarizeState replayedState) do
    throwError "{label}: replay state mismatch"

/-- The semantic adapter deliberately supports the pre registry only.  The
same declaration can be installed in the post registry, but accepting both
without binding registry provenance into the observation trace would make a
certificate mutation invisible.  Preserve the source result and defer. -/
def runRegistryPostDeferredCase (label : String) (expression : Expr) : MetaM Unit := do
  let sets ← existsPostSets
  let sourceMethods := sourceMethodsRegistryPost sets
  let recordingMethods := recordingMethodsRegistryPost sets
  let context ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let saved ← Meta.saveState
  let (reference, referenceState) ←
    Simp.mainCore expression context (methods := sourceMethods)
  let referenceSummary ← summarizeState referenceState
  saved.restore
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression context (methods := recordingMethods)
  unless Expr.equal reference.expr recorded.expr &&
      reference.proof?.isSome == recorded.proof?.isSome &&
      reference.cache == recorded.cache &&
      referenceSummary == (← summarizeState recordedState) do
    throwError "{label}: reference/record mismatch"
  unless recording.deferred ==
      some (.simproc `ExistsAndEq.existsAndEq .post) do
    throwError "{label}: expected post-registry deferral, got {repr recording.deferred}"
  checkExistsObservations label recording.simprocs true 1
  unless (semanticEvents recording.program).isEmpty do
    throwError "{label}: unsupported registry produced a semantic event"
  jsonRoundtrip (label ++ ":trace-json") recording.simprocs

def assertDerivationNone (label : String) (expression : Expr) : MetaM Unit := do
  let derivation? ← deriveExistsAndEq? `ExistsAndEq.existsAndEq expression expression
  unless derivation?.isNone do
    throwError "{label}: unsupported derivation was accepted"

private partial def existsEventIndexFrom (events : Array Simp.Engine.Event) (index : Nat) :
    Option Nat :=
  if h : index < events.size then
    let event := events[index]'h
    match event.operation with
    | .semanticSimproc fold =>
        if fold.candidates.any fun candidate =>
            candidate.declaration == `ExistsAndEq.existsAndEq then
          some index
        else
          existsEventIndexFrom events (index + 1)
    | _ => existsEventIndexFrom events (index + 1)
  else
    none

def existsEventIndex (program : Simp.Engine.Program) : Option Nat :=
  existsEventIndexFrom program.events 0

def mutateExistsFold (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocFold → Simp.Engine.SimprocFold) :
    Simp.Engine.Program :=
  match existsEventIndex program with
  | none => program
  | some index =>
      if h : index < program.events.size then
        let event := program.events[index]'h
        match event.operation with
        | .semanticSimproc fold =>
            let updated := { event with operation := .semanticSimproc (mutate fold) }
            { program with events := program.events.set index updated h }
        | _ => program
      else
        program

def mutateExistsCandidate (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocCandidateEvent → Simp.Engine.SimprocCandidateEvent) :
    Simp.Engine.Program :=
  mutateExistsFold program fun fold =>
    if fold.candidates.size > 0 then
      { fold with candidates := fold.candidates.set! 0 (mutate fold.candidates[0]!) }
    else
      fold

def mutateExistsDerivation
    (mutate : ExistsAndEqDerivation → ExistsAndEqDerivation)
    (program : Simp.Engine.Program) : Simp.Engine.Program :=
  mutateExistsCandidate program fun candidate =>
    match candidate.semantics with
    | .existentialEqualityElim derivation =>
        { candidate with semantics := .existentialEqualityElim (mutate derivation) }
    | _ => candidate

def mutateExistsEvent (program : Simp.Engine.Program)
    (mutate : Simp.Engine.Event → Simp.Engine.Event) : Simp.Engine.Program :=
  match existsEventIndex program with
  | none => program
  | some index =>
      if h : index < program.events.size then
        let event := program.events[index]'h
        { program with events := program.events.set index (mutate event) h }
      else
        program

def mutateExistsObservation (trace : Simp.Engine.SimprocTrace)
    (mutate : Simp.Engine.SimprocObservation → Simp.Engine.SimprocObservation) :
    Simp.Engine.SimprocTrace :=
  { observations := trace.observations.map fun observation =>
      if observation.name == `ExistsAndEq.existsAndEq then mutate observation else observation }

def expectValidationReject (label : String) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let saved ← Meta.saveState
  let succeeded ← try
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations program trace
    pure true
  catch _ => pure false
  saved.restore
  unless !succeeded do
    throwError "{label}: observation mutation was accepted"
  pure 1

def expectProgramReject (label : String) (artifacts : Artifacts)
    (program : Simp.Engine.Program := artifacts.recording.program)
    (trace : Simp.Engine.SimprocTrace := artifacts.recording.simprocs) : MetaM Nat := do
  let saved ← Meta.saveState
  let succeeded ← try
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations program trace
    let _ ← Simp.Engine.mainCoreReplay artifacts.expression artifacts.context artifacts.config program
    pure true
  catch _ => pure false
  saved.restore
  unless !succeeded do
    throwError "{label}: program mutation was accepted"
  pure 1

def mutateExistsRouteAt (index : Nat) (step : ExistsEqRouteStep)
    (derivation : ExistsAndEqDerivation) : ExistsAndEqDerivation :=
  { derivation with route := derivation.route.set! index step }

def mutateExistsReplacement (mutate : BoundSubtermRef → BoundSubtermRef)
    (derivation : ExistsAndEqDerivation) : ExistsAndEqDerivation :=
  { derivation with replacement := mutate derivation.replacement }

def checkReplayMutations (artifacts : Artifacts) : MetaM Nat := do
  let program := artifacts.recording.program
  let trace := artifacts.recording.simprocs
  let routeMutations : Array (String × Simp.Engine.Program) := #[
      ("route first kind", mutateExistsDerivation
        (mutateExistsRouteAt 0 .andLeft) program),
      ("route second kind", mutateExistsDerivation
        (mutateExistsRouteAt 1 .andRight) program),
      ("route third kind", mutateExistsDerivation
        (mutateExistsRouteAt 2 .andLeft) program),
      ("route order", mutateExistsDerivation (fun derivation =>
        { derivation with route := derivation.route.reverse }) program),
      ("route length shorter", mutateExistsDerivation (fun derivation =>
        { derivation with route := derivation.route.pop }) program),
      ("route length longer", mutateExistsDerivation (fun derivation =>
        { derivation with route := derivation.route.push .andLeft }) program),
      ("binder orientation", mutateExistsDerivation (fun derivation =>
        { derivation with binderSide := match derivation.binderSide with
          | .left => .right
          | .right => .left }) program),
      ("binder depth", mutateExistsDerivation (fun derivation =>
        mutateExistsReplacement (fun replacement =>
          { replacement with binderDepth := replacement.binderDepth + 1 }) derivation) program),
      ("replacement path", mutateExistsDerivation (fun derivation =>
        mutateExistsReplacement (fun replacement =>
          { replacement with reference :=
              { replacement.reference with path := replacement.reference.path.push .appFunction } }) derivation) program),
      ("replacement path step", mutateExistsDerivation (fun derivation =>
        mutateExistsReplacement (fun replacement =>
          { replacement with reference :=
              { replacement.reference with path := replacement.reference.path.set! 0 .appFunction } }) derivation) program),
      ("replacement fingerprint", mutateExistsDerivation (fun derivation =>
        mutateExistsReplacement (fun replacement =>
          { replacement with reference :=
              { replacement.reference with fingerprint := "mutated" } }) derivation) program),
      ("replacement envelope", mutateExistsDerivation (fun derivation =>
        mutateExistsReplacement (fun replacement =>
          { replacement with reference :=
              { replacement.reference with path := #[.appArgument, .lambdaBody] } }) derivation) program)
    ]
  let candidateMutations : Array (String × Simp.Engine.Program) := #[
      ("semantic constructor", mutateExistsCandidate program fun candidate =>
        { candidate with semantics := .canonicalValue (.natBinary default) }),
      ("candidate declaration", mutateExistsCandidate program fun candidate =>
        { candidate with declaration := `Nat.reduceAdd }),
      ("candidate procedure kind", mutateExistsCandidate program fun candidate =>
        { candidate with procedureKind := .dsimp }),
      ("candidate registry provenance", mutateExistsCandidate program fun candidate =>
        { candidate with registryPost := true }),
      ("candidate set index", mutateExistsCandidate program fun candidate =>
        { candidate with setIndex := candidate.setIndex + 1 }),
      ("candidate input fingerprint", mutateExistsCandidate program fun candidate =>
        { candidate with inputFingerprint := "mutated" }),
      ("candidate peeled input fingerprint", mutateExistsCandidate program fun candidate =>
        { candidate with peeledInputFingerprint := "mutated" }),
      ("candidate procedure output fingerprint", mutateExistsCandidate program fun candidate =>
        { candidate with procedureOutputFingerprint := "mutated" }),
      ("candidate output fingerprint", mutateExistsCandidate program fun candidate =>
        { candidate with outputFingerprint := "mutated" }),
      ("candidate extra count", mutateExistsCandidate program fun candidate =>
        { candidate with numExtraArgs := 1 }),
      ("candidate extra fingerprints", mutateExistsCandidate program fun candidate =>
        { candidate with extraArgumentFingerprints := #["mutated"] }),
      ("candidate disposition", mutateExistsCandidate program fun candidate =>
        { candidate with disposition := .done }),
      ("candidate proof fact", mutateExistsCandidate program fun candidate =>
        { candidate with proofPresent := false }),
      ("candidate cache fact", mutateExistsCandidate program fun candidate =>
        { candidate with cache := none }),
      ("fold phase", mutateExistsFold program fun fold =>
        { fold with phase := .post }),
      ("fold candidates empty", mutateExistsFold program fun fold =>
        { fold with candidates := #[] }),
      ("fold candidate duplication", mutateExistsFold program fun fold =>
        { fold with candidates := #[fold.candidates[0]!, fold.candidates[0]!] }),
      ("fold output fingerprint", mutateExistsFold program fun fold =>
        { fold with finalOutputFingerprint := "mutated" }),
      ("fold disposition", mutateExistsFold program fun fold =>
        { fold with finalDisposition := .done }),
      ("fold proof fact", mutateExistsFold program fun fold =>
        { fold with finalProofPresent := false }),
      ("fold cache fact", mutateExistsFold program fun fold =>
        { fold with finalCache := none }),
      ("event input fingerprint", mutateExistsEvent program fun event =>
        { event with inputFingerprint := "mutated" }),
      ("event output fingerprint", mutateExistsEvent program fun event =>
        { event with outputFingerprint := "mutated" }),
      ("event path", mutateExistsEvent program fun event =>
        { event with path := { steps := #[] } }),
      ("event phase", mutateExistsEvent program fun event =>
        { event with phase := .post }),
      ("event invocation ordinal", mutateExistsEvent program fun event =>
        { event with invocationOrdinal := event.invocationOrdinal + 1 }),
      ("event disposition", mutateExistsEvent program fun event =>
        { event with stepDisposition := .done }),
      ("event operation", mutateExistsEvent program fun event =>
        { event with operation := .builtin .decideTrue })
    ]
  let mut rejected := 0
  for (label, mutation) in routeMutations do
    rejected := rejected + (← expectProgramReject label artifacts mutation trace)
  for (label, mutation) in candidateMutations do
    rejected := rejected + (← expectProgramReject label artifacts mutation trace)
  let observationMutations : Array (String × Simp.Engine.SimprocTrace) := #[
      ("observation path", mutateExistsObservation trace fun observation =>
        { observation with path := { steps := #[] } }),
      ("observation name", mutateExistsObservation trace fun observation =>
        { observation with name := `Nat.reduceAdd }),
      ("observation phase", mutateExistsObservation trace fun observation =>
        { observation with phase := .post }),
      ("observation ordinal", mutateExistsObservation trace fun observation =>
        { observation with phaseInvocationOrdinal := observation.phaseInvocationOrdinal + 1 }),
      ("observation set index", mutateExistsObservation trace fun observation =>
        { observation with setIndex := observation.setIndex + 1 }),
      ("observation input fingerprint", mutateExistsObservation trace fun observation =>
        { observation with inputFingerprint := "mutated" }),
      ("observation output fingerprint", mutateExistsObservation trace fun observation =>
        { observation with outputFingerprint := "mutated" }),
      ("observation changed fact", mutateExistsObservation trace fun observation =>
        { observation with outputChanged := false }),
      ("observation definitional phase", mutateExistsObservation trace fun observation =>
        { observation with definitional := true }),
      ("observation procedure kind", mutateExistsObservation trace fun observation =>
        { observation with procedureKind := .dsimp }),
      ("observation extra count", mutateExistsObservation trace fun observation =>
        { observation with numExtraArgs := observation.numExtraArgs + 1 }),
      ("observation executed fact", mutateExistsObservation trace fun observation =>
        { observation with executed := false }),
      ("observation proof fact", mutateExistsObservation trace fun observation =>
        { observation with proofPresent := false }),
      ("observation cache fact", mutateExistsObservation trace fun observation =>
        { observation with cache := none }),
      ("observation output size", mutateExistsObservation trace fun observation =>
        { observation with outputSize := none }),
      ("observation disposition", mutateExistsObservation trace fun observation =>
        { observation with stepDisposition := .done }),
      ("observation removed", {
        observations := trace.observations.filter fun observation =>
          observation.name != `ExistsAndEq.existsAndEq }),
      ("observation duplicated", {
        observations := trace.observations ++
          (trace.observations.filter fun observation =>
            observation.name == `ExistsAndEq.existsAndEq) })
    ]
  for (label, mutation) in observationMutations do
    rejected := rejected + (← expectValidationReject label program mutation)
  pure rejected

def checkObservationOrderMutation (artifacts : Artifacts) : MetaM Nat := do
  expectValidationReject "observation order" artifacts.recording.program
    { observations := artifacts.recording.simprocs.observations.reverse }

def loopCase : Expr :=
  let terminal := natAnd (natEq (mkBVar 1) (mkBVar 0))
    (natEq (mkBVar 0) (natLiteral 1))
  let nested := natExists `b terminal
  let body := natAnd (natLe (mkBVar 0) (mkBVar 0)) nested
  natExists `a body

def leftFirst : Expr :=
  let body := natAnd (natEq (mkBVar 0) (natLiteral 0))
    (natEq (mkBVar 0) (natLiteral 1))
  natExists `a body

def hygienicOuterBinderName : Name :=
  Name.mkNum
    (Name.str (Name.str (Name.str (Name.str Name.anonymous "a") "_@") "_internal") "_hyg") 0

/-- Exercise a hygienic binder name through the complete fold/replay path. -/
def hygienicOuterBinder : Expr :=
  let selected := natAnd (natLe (natLiteral 0) (natLiteral 0))
    (natEq (natLiteral 3) (mkBVar 0))
  let body := natAnd selected (natLe (mkBVar 0) (mkBVar 0))
  natExists hygienicOuterBinderName body

def checkBinderNameBoundary : MetaM Unit := do
  let plain := mkLambda `a BinderInfo.default natType (mkBVar 0)
  let hygienic := mkLambda hygienicOuterBinderName BinderInfo.default natType (mkBVar 0)
  unless !Expr.equal plain hygienic && exprEqualIgnoringBinderNames plain hygienic do
    throwError "binder-name equality boundary was not isolated"
  let differentBody := mkLambda hygienicOuterBinderName BinderInfo.default natType (natLiteral 0)
  unless !exprEqualIgnoringBinderNames plain differentBody do
    throwError "binder-name equality accepted a substantive body change"

def checkPositive : MetaM Unit := do
  let _ ← runCase "basic-left" basicLeft false
  let _ ← runCase "basic-right" basicRight false
  let _ ← runCase "left-first" leftFirst false
  let _ ← runCase "nested-left" nestedSuccLeft false
  let _ ← runCase "nested-right" nestedSuccRight false
  let multiple ← runCase "multiple-crossed" multipleCrossed false
  let _ ← runCase "nested-and-left" nestedAndLeft false
  let _ ← runCase "nested-and-right" nestedAndRight false
  checkBinderNameBoundary
  let _ ← runCase "hygienic-outer-binder" hygienicOuterBinder false
  let loop ← runLoopCase "two-event-loop" loopCase
  let _ ← runCase "nested-post" nestedSuccLeft true
  runRegistryPostDeferredCase "registry-post-deferred" basicLeft
  runNoResultCase "no-route" noRoute false
  runNoResultCase "no-route-post" noRoute true
  runNoResultCase "dependent-crossed-type" dependentCrossedType false
  runNoResultCase "outer-dependent-replacement" outerDependentReplacement false
  runNoResultCase "non-exists" malformedShape false false
  assertDerivationNone "malformed-direct-shape" malformedShape
  let replacementMVar ← mkFreshExprMVar (some natType)
  assertDerivationNone "open-replacement" (natExists `a (natEq (mkBVar 0) replacementMVar))
  let rejected ← checkReplayMutations multiple
  let orderRejected ← checkObservationOrderMutation loop
  logInfo m!"SIMP_ENGINE_EXISTS_AND_EQ_MUTATIONS rejected={rejected + orderRejected}"

elab "check_exists_and_eq" : command => Elab.Command.liftTermElabM do
  checkPositive
  logInfo "SIMP_ENGINE_EXISTS_AND_EQ direct,nested,multiple,hygienic,loop,post,registry-post-deferred,unsupported: ok"

check_exists_and_eq
