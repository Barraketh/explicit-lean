import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace DIteSemanticFoldProbe

open Lean.Meta.Simp.Engine

def mkDite (α condition : Expr) (decidable : Expr) (thenBranch elseBranch : Expr) : Expr :=
  mkApp5 (mkConst ``dite [.succ .zero]) α condition decidable thenBranch elseBranch

def mkIte (α condition thenBranch elseBranch : Expr) : Expr :=
  mkApp5 (mkConst ``ite [.succ .zero]) α condition
    (if condition.isTrue then mkConst ``instDecidableTrue
     else if condition.isFalse then mkConst ``instDecidableFalse
     else mkConst ``Classical.propDecidable) thenBranch elseBranch

def propIte (condition : Expr) (thenBranch elseBranch : Bool) : Expr :=
  mkIte (mkSort .zero) condition
    (if thenBranch then mkConst ``True else mkConst ``False)
    (if elseBranch then mkConst ``True else mkConst ``False)

def propDite (condition : Expr) (thenBranch elseBranch : Bool) : Expr :=
  let decidable := if condition.isTrue then mkConst ``instDecidableTrue
    else if condition.isFalse then mkConst ``instDecidableFalse
    else mkConst ``Classical.propDecidable
  let branch (value : Bool) (domain : Expr) :=
    mkLambda `h .default domain (if value then mkConst ``True else mkConst ``False)
  mkDite (mkSort .zero) condition decidable (branch thenBranch condition)
    (branch elseBranch (mkApp (mkConst ``Not) condition))

def natDite (condition : Expr) (thenBranch elseBranch : Nat) : Expr :=
  let decidable := if condition.isTrue then mkConst ``instDecidableTrue
    else if condition.isFalse then mkConst ``instDecidableFalse
    else mkConst ``Classical.propDecidable
  let branch (value : Nat) (domain : Expr) :=
    mkLambda `h .default domain (mkRawNatLit value)
  mkDite (mkConst ``Nat) condition decidable (branch thenBranch condition)
    (branch elseBranch (mkApp (mkConst ``Not) condition))

def natLiteral (value : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit value)
    (mkInstOfNatNat (mkRawNatLit value))

def proofTag {p : Prop} (_h : p) : Nat := 37

def dependentBranch (domain : Expr) (extraArgs : Nat) : Expr :=
  Id.run do
    let tagged := mkApp (mkApp (mkConst ``DIteSemanticFoldProbe.proofTag) domain)
      (mkBVar extraArgs)
    let mut body := tagged
    for _ in *...extraArgs do
      body := mkLambda `x .default (mkConst ``Nat) body
    return mkLambda `h .default domain body

def dependentDiteWithDecidable (condition α decidable : Expr) (extraArgs : Nat) : Expr :=
  mkDite α condition decidable (dependentBranch condition extraArgs)
    (dependentBranch (mkApp (mkConst ``Not) condition) extraArgs)

def dependentDite (condition : Expr) (α : Expr) (extraArgs : Nat) : Expr :=
  let decidable := if condition.isTrue then mkConst ``instDecidableTrue
    else if condition.isFalse then mkConst ``instDecidableFalse
    else mkConst ``Classical.propDecidable
  dependentDiteWithDecidable condition α decidable extraArgs

def summarizeSemantics (program : Simp.Engine.Program) : String :=
  let folds := program.events.filterMap fun event =>
    match event.operation with
    | .semanticSimproc fold => some fold
    | _ => none
  String.intercalate ";" <| folds.toList.map fun fold =>
    let candidate := fold.candidates[0]!
    s!"phase={reprStr fold.phase},decl={candidate.declaration},candidate={reprStr candidate.disposition},fold={reprStr fold.finalDisposition},proof={fold.finalProofPresent},cache={reprStr fold.finalCache},nested={match candidate.semantics with | .diteSelect _ => true | _ => false}"

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

def checkExpression (label : String) (expression : Expr)
    (expectedExpr? : Option Expr := none) (singlePass : Bool := false) : MetaM
    (Simp.Context × Simp.Engine.ReplayConfig × Simp.Engine.Program × Simp.Engine.SimprocTrace) := do
  let builtins ← Simp.getSimprocs
  let methods := Simp.Engine.mkDefaultMethodsCore #[builtins]
  let baseCtx₀ ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let baseCtx ← baseCtx₀.setConfig { baseCtx₀.config with singlePass }
  let initialMeta ← Meta.saveState
  let (reference, referenceState) ← Simp.mainCore expression baseCtx (methods := methods.base)
  let referenceSummary ← summarizeState referenceState
  initialMeta.restore
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression baseCtx (methods := methods)
  if let some expectedExpr := expectedExpr? then
    unless Expr.equal recorded.expr expectedExpr && Expr.equal reference.expr expectedExpr do
      throwError "{label}: result mismatch: recorded={repr recorded.expr}; reference={repr reference.expr}; expected={repr expectedExpr}"
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
  let some event := recording.program.events[0]? | throwError "{label}: empty program"
  let .semanticSimproc fold := event.operation |
    throwError "{label}: first event is not semantic reduceDIte"
  let candidate := fold.candidates[0]!
  unless candidate.declaration == `reduceDIte && candidate.procedureKind == .simp &&
      candidate.setIndex == 0 && candidate.registryPost == false &&
      candidate.disposition == .visit && candidate.proofPresent &&
      candidate.cache == some true && fold.finalDisposition == .visit &&
      fold.finalProofPresent && fold.finalCache == some true &&
      event.stepDisposition == .visit do
    throwError "{label}: reduceDIte protocol mismatch: {repr fold}"
  let .diteSelect selection := candidate.semantics |
    throwError "{label}: first candidate is not diteSelect"
  unless selection.headBeta.inputFingerprint != "" &&
      selection.headBeta.outputFingerprint != "" do
    throwError "{label}: missing headBeta witness"
  unless selection.headBeta.inputFingerprint != selection.headBeta.outputFingerprint &&
      candidate.procedureOutputFingerprint == selection.headBeta.outputFingerprint do
    throwError "{label}: headBeta witness does not describe the procedure output"
  let config ← Simp.Engine.replayConfigOfContext baseCtx
  let decodedProgram : Simp.Engine.Program ←
    match Lean.fromJson? (Lean.toJson recording.program) with
    | .ok decoded => pure decoded
    | .error message => throwError "{label}: DIte program JSON roundtrip failed: {message}"
  unless decodedProgram == recording.program do
    throwError "{label}: DIte program JSON roundtrip changed the payload"
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay expression baseCtx config recording.program
  let replayedSummary ← summarizeState replayedState
  unless expectedExpr?.all fun expectedExpr => Expr.equal replayed.expr expectedExpr &&
      Expr.equal recorded.expr expectedExpr && Expr.equal reference.expr expectedExpr &&
      Expr.equal recorded.expr replayed.expr &&
      replayed.proof?.isSome == recorded.proof?.isSome &&
      replayed.cache == recorded.cache do
    throwError "{label}: replay result parity mismatch"
  unless replayedSummary == recordedSummary do
    throwError "{label}: replay state parity mismatch: {repr replayedSummary} != {repr recordedSummary}"
  return (baseCtx, config, recording.program, recording.simprocs)

def checkExpr (label : String) (expression : Expr) (expected : Nat) : MetaM Unit := do
  let _ ← checkExpression label expression (some (natLiteral expected))

def expectReplayReject (label : String) (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let saved ← Meta.saveState
  let succeeded ← try
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations program trace
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
    | .diteSelect selection =>
        let conditionProgram := mutate selection.conditionProgram
        { candidate with semantics := .diteSelect { selection with conditionProgram } }
    | _ => candidate

def nestedProgramOf (program : Simp.Engine.Program) : Simp.Engine.NestedProgram :=
  match program.events[0]? with
  | some event =>
      match event.operation with
      | .semanticSimproc fold =>
          match fold.candidates[0]? with
          | some candidate =>
              match candidate.semantics with
              | .diteSelect selection => selection.conditionProgram
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
    (mutateNested program fun nested => { nested with program := nestedEventMutation }) trace
  let observationRejected ←
    match nestedTrace.observations[0]? with
    | some observation =>
        let mutatedTrace := { nestedTrace with observations := nestedTrace.observations.set! 0 {
            observation with name := `DIteSemanticFoldProbe.mutatedObservation } }
        let mutatedProgram := mutateNested program fun nested =>
          { nested with simprocs := mutatedTrace }
        expectObservationReject "nested observation" mutatedProgram trace
    | none => throwError "dite nested condition has no committed observations"
  return eventRejected + observationRejected

def checkMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let some event := program.events[0]? | throwError "dite mutation fixture has no event"
  let .semanticSimproc fold := event.operation |
    throwError "dite mutation fixture has no semantic fold"
  let candidate := fold.candidates[0]!
  let .diteSelect _selection := candidate.semantics |
    throwError "dite mutation fixture has no dite selection"
  let mut mutations : Array (String × Simp.Engine.Program) := #[
    ("decision", mutateOuterCandidate program fun candidate =>
      match candidate.semantics with
      | .diteSelect selection => { candidate with semantics := .diteSelect {
          selection with decision := match selection.decision with
            | .trueBranch => .falseBranch
            | .falseBranch => .trueBranch } }
      | _ => candidate),
    ("condition ref", mutateOuterCandidate program fun candidate =>
      match candidate.semantics with
      | .diteSelect selection => { candidate with semantics := .diteSelect {
          selection with conditionRef := { selection.conditionRef with fingerprint := "mutated" } } }
      | _ => candidate),
    ("branch ref", mutateOuterCandidate program fun candidate =>
      match candidate.semantics with
      | .diteSelect selection => { candidate with semantics := .diteSelect {
          selection with selectedBranchRef := { selection.selectedBranchRef with fingerprint := "mutated" } } }
      | _ => candidate),
    ("headBeta input fingerprint", mutateOuterCandidate program fun candidate =>
      match candidate.semantics with
      | .diteSelect selection => { candidate with semantics := .diteSelect {
          selection with headBeta := { selection.headBeta with inputFingerprint := "mutated" } } }
      | _ => candidate),
    ("headBeta output fingerprint", mutateOuterCandidate program fun candidate =>
      match candidate.semantics with
      | .diteSelect selection => { candidate with semantics := .diteSelect {
          selection with headBeta := { selection.headBeta with outputFingerprint := "mutated" } } }
      | _ => candidate),
    ("extra argument count", mutateOuterCandidate program fun candidate =>
      { candidate with numExtraArgs := candidate.numExtraArgs + 1 }),
    ("candidate set index", mutateOuterCandidate program fun candidate =>
      { candidate with setIndex := candidate.setIndex + 1 }),
    ("candidate procedure kind", mutateOuterCandidate program fun candidate =>
      { candidate with procedureKind := .dsimp }),
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
  for index in *...candidate.extraArgumentFingerprints.size do
    let label := s!"extra argument fingerprint {index}"
    mutations := mutations.push (label, mutateOuterCandidate program fun candidate =>
      { candidate with extraArgumentFingerprints := candidate.extraArgumentFingerprints.set! index "mutated" })
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayReject label expression ctx config mutation trace)
  let nestedMutations ← checkNestedTraceMutation expression ctx config program trace
  return rejected + nestedMutations

def checkUnsupportedCondition : MetaM Unit := do
  let builtins ← Simp.getSimprocs
  let methods := Simp.Engine.mkDefaultMethodsCore #[builtins]
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  withLocalDeclD `condition (mkSort .zero) fun condition => do
    let expression := natDite condition 3 4
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
    unless recording.deferred matches some (.simproc `reduceDIte .pre) do
      throwError "unsupported condition did not defer reduceDIte: {repr recording.deferred}"
    unless !recording.program.events.any fun event =>
        match event.operation with
        | .semanticSimproc _ => true
        | _ => false do
      throwError "unsupported condition invented a semantic event"

elab "check_simp_engine_dite" : tactic => withMainContext do
  let trueExpression := natDite (mkConst ``True) 11 22
  let falseExpression := natDite (mkConst ``False) 11 22
  checkExpr "true" trueExpression 11
  checkExpr "false" falseExpression 22
  let nestedCondition := propIte (mkConst ``True) false true
  let (nestedCtx, nestedConfig, nestedProgram, nestedTrace) ←
    checkExpression "nested" (natDite nestedCondition 31 47) (some (natLiteral 47))
  let nestedMutations ← checkMutations (natDite nestedCondition 31 47) nestedCtx
    nestedConfig nestedProgram nestedTrace
  let nestedDiteCondition := propDite (mkConst ``True) false true
  let nestedDiteExpression := natDite nestedDiteCondition 53 59
  let (nestedDiteCtx, nestedDiteConfig, nestedDiteProgram, nestedDiteTrace) ←
    checkExpression "nested dite" nestedDiteExpression (some (natLiteral 59))
  let nestedDiteMutations ← checkMutations nestedDiteExpression nestedDiteCtx
    nestedDiteConfig nestedDiteProgram nestedDiteTrace
  let natType := mkConst ``Nat
  let oneArgType ← mkArrow natType natType
  let twoArgType ← mkArrow natType oneArgType
  let dependentTrue := mkApp
    (dependentDite (mkConst ``True) oneArgType 1) (mkRawNatLit 5)
  let dependentFalse := mkAppN
    (dependentDite (mkConst ``False) twoArgType 2)
      #[mkRawNatLit 5, mkRawNatLit 6]
  let (dependentCtx, dependentConfig, dependentProgram, dependentTrace) ←
    checkExpression "dependent false" dependentFalse
  let dependentMutations ← checkMutations dependentFalse dependentCtx
    dependentConfig dependentProgram dependentTrace
  let _ ← checkExpression "dependent true" dependentTrue
  let _ ← checkExpression "singlePass" trueExpression (some (natLiteral 11)) true
  checkUnsupportedCondition
  logInfo m!"SIMP_ENGINE_DITE true=false,nested,nested-dite,headBeta,extra,singlePass,unsupported: ok mutations={nestedMutations + nestedDiteMutations + dependentMutations}"

example : True := by
  check_simp_engine_dite
  trivial

end DIteSemanticFoldProbe
