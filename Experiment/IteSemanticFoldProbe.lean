import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace IteSemanticFoldProbe

open Lean.Meta.Simp.Engine

def mkIte (α condition thenBranch elseBranch : Expr) : Expr :=
  mkApp5 (mkConst ``ite [.succ .zero]) α condition
    (if condition.isTrue then mkConst ``instDecidableTrue
     else if condition.isFalse then mkConst ``instDecidableFalse
     else mkConst ``Classical.propDecidable) thenBranch elseBranch

def natIte (condition : Expr) (thenBranch elseBranch : Nat) : Expr :=
  mkIte (mkConst ``Nat) condition (mkRawNatLit thenBranch) (mkRawNatLit elseBranch)

def natLiteral (value : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit value)
    (mkInstOfNatNat (mkRawNatLit value))

def propIte (condition : Expr) (thenBranch elseBranch : Bool) : Expr :=
  mkIte (mkSort .zero) condition
    (if thenBranch then mkConst ``True else mkConst ``False)
    (if elseBranch then mkConst ``True else mkConst ``False)

def summarizeSemantics (program : Simp.Engine.Program) : String :=
  let folds := program.events.filterMap fun event =>
    match event.operation with
    | .semanticSimproc fold => some fold
    | _ => none
  String.intercalate ";" <| folds.toList.map fun fold =>
    let candidate := fold.candidates[0]!
    s!"phase={reprStr fold.phase},decl={candidate.declaration},candidate={reprStr candidate.disposition},fold={reprStr fold.finalDisposition},proof={fold.finalProofPresent},cache={reprStr fold.finalCache},nested={match candidate.semantics with | .iteSelect _ => true | _ => false}"

def listFingerprint (values : List String) : String :=
  String.intercalate "," (values.toArray.qsort (· < ·) |>.toList)

def resultFingerprint (result : Simp.Result) : MetaM String := do
  let expression ← exprFingerprintHash result.expr
  let proof ← result.proof?.mapM exprFingerprintHash
  return s!"{expression}|{proof}|{result.cache}"

def cacheFingerprint (cache : Simp.Cache) : MetaM String := do
  let entries ← cache.toList.mapM fun (key, value) => do
    let keyFingerprint ← exprFingerprintHash key
    let valueFingerprint ← resultFingerprint value
    pure s!"{keyFingerprint}=>{valueFingerprint}"
  return s!"stage₁={cache.stage₁};{listFingerprint entries}"

def dsimpCacheFingerprint (cache : ExprStructMap Expr) : MetaM String := do
  let entries ← cache.toList.mapM fun (key, value) => do
    let keyFingerprint ← exprFingerprintHash key.val
    let valueFingerprint ← exprFingerprintHash value
    pure s!"{keyFingerprint}=>{valueFingerprint}"
  return listFingerprint entries

def simpTheoremFingerprint (simpThm : SimpTheorem) : MetaM String := do
  let proof ← exprFingerprintHash simpThm.proof
  pure s!"keys={reprStr simpThm.keys}|levels={reprStr simpThm.levelParams}|proof={proof}|priority={simpThm.priority}|post={simpThm.post}|perm={simpThm.perm}|origin={reprStr simpThm.origin}|rfl={simpThm.rfl}|backwardRfl={simpThm.backwardRfl}"

def diagnosticsFingerprint (diagnostics : Simp.Diagnostics) : MetaM String := do
  let used := diagnostics.usedThmCounter.toList.map fun (origin, count) =>
    s!"{reprStr origin}=>{count}"
  let tried := diagnostics.triedThmCounter.toList.map fun (origin, count) =>
    s!"{reprStr origin}=>{count}"
  let congr := diagnostics.congrThmCounter.toList.map fun (name, count) =>
    s!"{name}=>{count}"
  let badKeys ← diagnostics.thmsWithBadKeys.toList.mapM simpTheoremFingerprint
  return s!"used={listFingerprint used};tried={listFingerprint tried};" ++
    s!"congr={listFingerprint congr};badKeys={listFingerprint badKeys}"

structure StateSummary where
  numSteps : Nat
  cache : String
  dsimpCache : String
  usedTheorems : String
  diagnostics : String
  deriving BEq, Repr

def summarizeState (state : Simp.State) : MetaM StateSummary := do
  return {
    numSteps := state.numSteps
    cache := ← cacheFingerprint state.cache
    dsimpCache := ← dsimpCacheFingerprint state.dsimpCache
    usedTheorems := listFingerprint (state.usedTheorems.toArray.toList.map reprStr)
    diagnostics := ← diagnosticsFingerprint state.diag
  }

def expectReplayReject (label : String) (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program) : MetaM Nat := do
  let saved ← Meta.saveState
  let succeeded ← try
    let _ ← Simp.Engine.mainCoreReplay expression ctx config program
    pure true
  catch _ => pure false
  saved.restore
  unless !succeeded do
    throwError "{label}: replay mutation was accepted"
  pure 1

def expectObservationReject (label : String) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let succeeded ← try
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations program trace
    pure true
  catch _ => pure false
  if succeeded then
    throwError "{label}: simproc observation mutation was accepted"
  pure 1

def mutateOuterEvent (program : Simp.Engine.Program)
    (mutate : Simp.Engine.Event → Simp.Engine.Event) : Simp.Engine.Program :=
  match program.events[0]? with
  | none => program
  | some event => { program with events := program.events.set! 0 (mutate event) }

def mutateOuterFold (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocFold → Simp.Engine.SimprocFold) : Simp.Engine.Program :=
  match program.events[0]? with
  | none => program
  | some event =>
      match event.operation with
      | .semanticSimproc fold =>
          { program with events := program.events.set! 0 {
              event with operation := .semanticSimproc (mutate fold) } }
      | _ => program

def mutateOuterCandidate (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocCandidateEvent → Simp.Engine.SimprocCandidateEvent) :
    Simp.Engine.Program :=
  mutateOuterFold program fun fold =>
    { fold with candidates := fold.candidates.set! 0 (mutate fold.candidates[0]!) }

def mutateNested (program : Simp.Engine.Program)
    (mutate : Simp.Engine.NestedProgram → Simp.Engine.NestedProgram) :
    Simp.Engine.Program :=
  mutateOuterCandidate program fun candidate =>
    match candidate.semantics with
    | .iteSelect selection =>
        let conditionProgram := mutate selection.conditionProgram
        { candidate with semantics := .iteSelect { selection with conditionProgram } }
    | _ => candidate

def nestedProgramOf (program : Simp.Engine.Program) : Simp.Engine.NestedProgram :=
  match program.events[0]? with
  | some event =>
      match event.operation with
      | .semanticSimproc fold =>
          match fold.candidates[0]? with
          | some candidate =>
              match candidate.semantics with
              | .iteSelect selection => selection.conditionProgram
              | _ => default
          | none => default
      | _ => default
  | _ => default

def checkNestedTraceMutation (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let nested := nestedProgramOf program
  let nestedProgram := nested.program
  let nestedTrace := nested.simprocs
  let nestedEventMutation :=
    match nestedProgram.events[0]? with
    | some event =>
        { nestedProgram with events := nestedProgram.events.set! 0 {
            event with outputFingerprint := "mutated-nested-event" } }
    | none => { nestedProgram with finalFingerprint := "mutated-nested-event" }
  let eventRejected ← expectReplayReject "nested event" expression ctx config
    (mutateNested program fun nested => { nested with program := nestedEventMutation })
  let observationRejected ←
    match nestedTrace.observations[0]? with
    | some observation =>
        let mutatedTrace := { nestedTrace with observations := nestedTrace.observations.set! 0 {
            observation with name := `IteSemanticFoldProbe.mutatedObservation } }
        let mutatedProgram := mutateNested program fun nested =>
          { nested with simprocs := mutatedTrace }
        expectObservationReject "nested observation" mutatedProgram trace
    | none => throwError "nested condition has no committed observations"
  return eventRejected + observationRejected

def checkMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let some event := program.events[0]? | throwError "ite mutation fixture has no event"
  let .semanticSimproc fold := event.operation |
    throwError "ite mutation fixture has no semantic fold"
  let candidate := fold.candidates[0]!
  let .iteSelect _ := candidate.semantics |
    throwError "ite mutation fixture has no ite selection"
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("decision", mutateOuterCandidate program fun candidate =>
      match candidate.semantics with
      | .iteSelect selection => { candidate with semantics := .iteSelect {
          selection with decision := match selection.decision with
            | .trueBranch => .falseBranch
            | .falseBranch => .trueBranch } }
      | _ => candidate),
    ("condition ref", mutateOuterCandidate program fun candidate =>
      match candidate.semantics with
      | .iteSelect selection => { candidate with semantics := .iteSelect {
          selection with conditionRef := { selection.conditionRef with fingerprint := "mutated" } } }
      | _ => candidate),
    ("branch ref", mutateOuterCandidate program fun candidate =>
      match candidate.semantics with
      | .iteSelect selection => { candidate with semantics := .iteSelect {
          selection with selectedBranchRef := { selection.selectedBranchRef with fingerprint := "mutated" } } }
      | _ => candidate),
    ("extra argument fingerprint", mutateOuterCandidate program fun candidate =>
      { candidate with extraArgumentFingerprints := #["mutated"] }),
    ("extra argument count", mutateOuterCandidate program fun candidate =>
      { candidate with numExtraArgs := candidate.numExtraArgs + 1 }),
    ("nested policy state", mutateNested program fun nested =>
      { nested with statePolicy := .isolatedStats }),
    ("nested policy config", mutateNested program fun nested =>
      { nested with configPolicy := .defaultSimp }),
    ("nested policy depth", mutateNested program fun nested =>
      { nested with dischargeDepthIncrement := 1 }),
    ("candidate disposition", mutateOuterCandidate program fun candidate =>
      { candidate with disposition := .done }),
    ("candidate proof", mutateOuterCandidate program fun candidate =>
      { candidate with proofPresent := false }),
    ("candidate cache", mutateOuterCandidate program fun candidate =>
      { candidate with cache := none }),
    ("candidate registry provenance", mutateOuterCandidate program fun candidate =>
      { candidate with registryPost := true }),
    ("fold disposition", mutateOuterFold program fun fold =>
      { fold with finalDisposition := .done }),
    ("fold proof", mutateOuterFold program fun fold =>
      { fold with finalProofPresent := false }),
    ("fold cache", mutateOuterFold program fun fold =>
      { fold with finalCache := none }),
    ("candidate input fingerprint", mutateOuterCandidate program fun candidate =>
      { candidate with inputFingerprint := "mutated" }),
    ("candidate peeled fingerprint", mutateOuterCandidate program fun candidate =>
      { candidate with peeledInputFingerprint := "mutated" }),
    ("candidate procedure output fingerprint", mutateOuterCandidate program fun candidate =>
      { candidate with procedureOutputFingerprint := "mutated" }),
    ("candidate output fingerprint", mutateOuterCandidate program fun candidate =>
      { candidate with outputFingerprint := "mutated" }),
    ("fold output fingerprint", mutateOuterFold program fun fold =>
      { fold with finalOutputFingerprint := "mutated" }),
    ("outer input fingerprint", mutateOuterEvent program fun event =>
      { event with inputFingerprint := "mutated" }),
    ("outer output fingerprint", mutateOuterEvent program fun event =>
      { event with outputFingerprint := "mutated" }),
    ("outer disposition", mutateOuterEvent program fun event =>
      { event with stepDisposition := .done })]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayReject label expression ctx config mutation)
  let nestedMutations ← checkNestedTraceMutation expression ctx config program
    trace
  return rejected + nestedMutations

def checkExpr (label : String) (expression : Expr) (expected : Nat)
    (checkMutations? : Bool := false) (singlePass : Bool := false) : MetaM Nat := do
  let builtins ← Simp.getSimprocs
  let methods := Simp.Engine.mkDefaultMethodsCore #[builtins]
  let baseCtx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let ctx ← baseCtx.setConfig { baseCtx.config with singlePass }
  let initialMeta ← Meta.saveState
  let (reference, referenceState) ← Simp.mainCore expression ctx (methods := methods.base)
  let referenceSummary ← summarizeState referenceState
  initialMeta.restore
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression ctx (methods := methods)
  unless Expr.equal recorded.expr (natLiteral expected) do
    throwError "{label}: recorded result mismatch: {recorded.expr}"
  unless Expr.equal reference.expr (natLiteral expected) do
    throwError "{label}: reference result mismatch: {reference.expr}"
  unless Expr.equal recorded.expr reference.expr &&
      recorded.proof?.isSome == reference.proof?.isSome &&
      recorded.cache == reference.cache do
    throwError "{label}: ordinary/reference result parity mismatch"
  let recordedSummary ← summarizeState recordedState
  unless recordedSummary == referenceSummary do
    throwError "{label}: ordinary/reference state parity mismatch: {repr recordedSummary} != {repr referenceSummary}"
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  let semanticEvents := recording.program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false
  unless semanticEvents.size >= 1 do
    throwError "{label}: missing semantic reduceIte event"
  let some event := recording.program.events[0]? | throwError "{label}: empty program"
  let .semanticSimproc fold := event.operation |
    throwError "{label}: first event is not semantic reduceIte"
  let candidate := fold.candidates[0]!
  unless candidate.declaration == `reduceIte && candidate.procedureKind == .simp &&
      candidate.setIndex == 0 && candidate.disposition == .visit &&
      candidate.proofPresent && candidate.cache == some true &&
      fold.finalDisposition == .visit && fold.finalProofPresent &&
      fold.finalCache == some true && event.stepDisposition == .visit do
    throwError "{label}: reduceIte protocol mismatch: {repr fold}"
  let config ← Simp.Engine.replayConfigOfContext ctx
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay expression ctx config recording.program
  let replayedSummary ← summarizeState replayedState
  unless Expr.equal recorded.expr (natLiteral expected) &&
      Expr.equal replayed.expr (natLiteral expected) &&
      Expr.equal recorded.expr replayed.expr &&
      replayed.proof?.isSome == recorded.proof?.isSome &&
      replayed.cache == recorded.cache do
    throwError "{label}: replay result parity mismatch"
  unless replayedSummary == recordedSummary do
    throwError "{label}: replay state parity mismatch: {repr replayedSummary} != {repr recordedSummary}"
  if checkMutations? then
    return ← checkMutations expression ctx config recording.program recording.simprocs
  return 0

def checkUnsupportedCondition : MetaM Unit := do
  let builtins ← Simp.getSimprocs
  let methods := Simp.Engine.mkDefaultMethodsCore #[builtins]
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  withLocalDeclD `condition (mkSort .zero) fun condition => do
    let expression := natIte condition 3 4
    let initialMeta ← Meta.saveState
    let (reference, referenceState) ← Simp.mainCore expression ctx (methods := methods.base)
    let referenceSummary ← summarizeState referenceState
    initialMeta.restore
    let (recorded, recordedState, recording) ←
      Simp.Engine.mainCoreRecording expression ctx (methods := methods)
    unless Expr.equal recorded.expr reference.expr &&
        recorded.proof?.isSome == reference.proof?.isSome &&
        recorded.cache == reference.cache do
      throwError "unsupported condition ordinary/reference result mismatch"
    let recordedSummary ← summarizeState recordedState
    unless recordedSummary == referenceSummary do
      throwError "unsupported condition ordinary/reference state mismatch: {repr recordedSummary} != {repr referenceSummary}"
    unless recording.deferred matches some (.simproc `reduceIte .pre) do
      throwError "unsupported condition did not defer reduceIte: {repr recording.deferred}"
    unless !recording.program.events.any fun event =>
        match event.operation with
        | .semanticSimproc _ => true
        | _ => false do
      throwError "unsupported condition invented a semantic event"

elab "check_simp_engine_ite" : tactic => withMainContext do
  let trueExpression := natIte (mkConst ``True) 11 22
  let falseExpression := natIte (mkConst ``False) 11 22
  let nestedCondition := propIte (mkConst ``True) false true
  let nestedExpression := natIte nestedCondition 31 47
  let functionType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let identity := mkLambda `n .default (mkConst ``Nat) (mkBVar 0)
  let successor := mkLambda `n .default (mkConst ``Nat)
    (mkRawNatLit 99)
  let extraExpression := mkApp (mkIte functionType (mkConst ``False) identity successor)
    (mkRawNatLit 7)
  let trueMutations ← checkExpr "true" trueExpression 11
  let falseMutations ← checkExpr "false" falseExpression 22
  let singlePassMutations ← checkExpr "singlePass" trueExpression 11 false true
  let nestedMutations ← checkExpr "nested" nestedExpression 47 true
  let extraMutations ← checkExpr "extra" extraExpression 99 true
  checkUnsupportedCondition
  unless nestedMutations > 0 && extraMutations > 0 do
    throwError "ite focused mutation fixtures did not execute"
  logInfo m!"SIMP_ENGINE_ITE true=false,nested,extra,singlePass,unsupported: ok mutations={trueMutations + falseMutations + nestedMutations + extraMutations + singlePassMutations}"

example : True := by
  check_simp_engine_ite
  trivial

end IteSemanticFoldProbe
