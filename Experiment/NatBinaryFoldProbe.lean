import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace NatBinaryFoldProbe

open Lean.Meta.Simp.Engine

def natBinary (name : Name) (inst lhs rhs : Expr) : Expr :=
  mkApp6 (mkConst name [.zero, .zero, .zero]) (mkConst ``Nat) (mkConst ``Nat)
    (mkConst `Nat) inst lhs rhs

def sortStrings (values : List String) : List String :=
  values.toArray.qsort (· < ·) |>.toList

def listFingerprint (values : List String) : String :=
  String.intercalate "," (sortStrings values)

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
    -- Closed replay uses the explicit congruence witness.  The pre-existing
    -- negative generic-congruence lookup cache is not part of this fold slice.
    dsimpCache := ← dsimpCacheFingerprint state.dsimpCache
    usedTheorems := listFingerprint (state.usedTheorems.toArray.toList.map reprStr)
    diagnostics := ← diagnosticsFingerprint state.diag
  }

def mutateCandidate (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocCandidateEvent → Simp.Engine.SimprocCandidateEvent) :
    Simp.Engine.Program :=
  match program.events[0]? with
  | none => program
  | some event =>
      match event.operation with
      | .semanticSimproc fold =>
          let candidate := fold.candidates[0]!
          let fold := { fold with candidates := fold.candidates.set! 0 (mutate candidate) }
          { program with events := program.events.set! 0 {
              event with operation := .semanticSimproc fold } }
      | _ => program

def mutateFold (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocFold → Simp.Engine.SimprocFold) :
    Simp.Engine.Program :=
  match program.events[0]? with
  | none => program
  | some event =>
      match event.operation with
      | .semanticSimproc fold =>
          { program with events := program.events.set! 0 {
              event with operation := .semanticSimproc (mutate fold) } }
      | _ => program

def mutateOuterEvent (program : Simp.Engine.Program)
    (mutate : Simp.Engine.Event → Simp.Engine.Event) : Simp.Engine.Program :=
  match program.events[0]? with
  | none => program
  | some event => { program with events := program.events.set! 0 (mutate event) }

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

def checkNatWfPreludeObservations (label : String)
    (observations : Array SimprocObservation) : MetaM Unit := do
  let continueNone := observations.filter fun observation =>
    observation.executed && observation.stepDisposition == .continueNone
  let allowed := fun name : Name =>
    name == `Lean.Elab.WF.paramProj || name == `Lean.Elab.WF.paramMatcher ||
      name == `Lean.Elab.WF.paramLet
  for observation in continueNone do
    unless allowed observation.name do
      throwError "{label}: unsupported ignored continue-none observation {observation.name}"
  for declaration in #[`Lean.Elab.WF.paramProj, `Lean.Elab.WF.paramMatcher,
      `Lean.Elab.WF.paramLet] do
    unless continueNone.any fun observation => observation.name == declaration do
      throwError "{label}: missing WF prelude observation {declaration}"
  unless observations.any fun observation =>
      observation.executed && observation.name == `Nat.reduceAdd &&
        observation.stepDisposition == .done ||
      observation.executed && observation.name == `Nat.reduceDiv &&
        observation.stepDisposition == .done do
    throwError "{label}: missing terminating Nat binary observation"

def expectObservationReject (label : String) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let succeeded ← try
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations program trace
    pure true
  catch _ => pure false
  if succeeded then
    throwError "{label}: simproc observation mutation was accepted"
  return 1

def checkObservationMutations (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let renamed : Simp.Engine.SimprocTrace := {
    observations := trace.observations.map fun observation =>
      if observation.name == `Lean.Elab.WF.paramProj then
        { observation with name := `NatBinaryFoldProbe.unsupported }
      else
        observation
  }
  let renamedRejected ←
    expectObservationReject "unrecognized no-result observation" program renamed
  let missingFoldRejected ← expectObservationReject "unrepresented result observation"
    { program with events := #[] } trace
  return renamedRejected + missingFoldRejected

def checkMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let some event := program.events[0]? | throwError "mutation fixture has no event"
  let .semanticSimproc fold := event.operation | throwError "mutation fixture has no semantic fold"
  let candidate := fold.candidates[0]!
  let alternateDeclaration :=
    if candidate.declaration == `Nat.reduceAdd then `Nat.reduceDiv else `Nat.reduceAdd
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("candidate declaration provenance", mutateCandidate program fun candidate =>
      { candidate with declaration := alternateDeclaration }),
    ("candidate procedure kind", mutateCandidate program fun candidate =>
      { candidate with procedureKind := .simp }),
    ("candidate registry provenance", mutateCandidate program fun candidate =>
      { candidate with registryPost := false }),
    ("candidate semantics result", mutateCandidate program fun candidate =>
      match candidate.semantics with
      | .canonicalValue (.natBinary derivation) =>
          { candidate with semantics := .canonicalValue (.natBinary {
              derivation with result := derivation.result + 1 }) }
      | _ => candidate),
    ("candidate semantics operator", mutateCandidate program fun candidate =>
      match candidate.semantics with
      | .canonicalValue (.natBinary derivation) =>
          { candidate with semantics := .canonicalValue (.natBinary {
              derivation with operator := .div }) }
      | _ => candidate),
    ("candidate set index", mutateCandidate program fun candidate =>
      { candidate with setIndex := 1 }),
    ("candidate input fingerprint", mutateCandidate program fun candidate =>
      { candidate with inputFingerprint := "mutated" }),
    ("candidate peeled input fingerprint", mutateCandidate program fun candidate =>
      { candidate with peeledInputFingerprint := "mutated" }),
    ("candidate extra argument fingerprints", mutateCandidate program fun candidate =>
      { candidate with extraArgumentFingerprints := #["mutated"] }),
    ("candidate procedure output fingerprint", mutateCandidate program fun candidate =>
      { candidate with procedureOutputFingerprint := "mutated" }),
    ("candidate output fingerprint", mutateCandidate program fun candidate =>
      { candidate with outputFingerprint := "mutated" }),
    ("candidate extra argument count", mutateCandidate program fun candidate =>
      { candidate with numExtraArgs := candidate.numExtraArgs + 1 }),
    ("candidate extra argument order", mutateCandidate program fun candidate =>
      let candidate := { candidate with extraArgumentFingerprints := #["first", "second"] }
      { candidate with numExtraArgs := 2 }),
    ("candidate disposition", mutateCandidate program fun candidate =>
      { candidate with disposition := .visit }),
    ("candidate proof fact", mutateCandidate program fun candidate =>
      { candidate with proofPresent := true }),
    ("candidate cache fact", mutateCandidate program fun candidate =>
      { candidate with cache := none }),
    ("fold phase", mutateFold program fun fold => { fold with phase := .pre }),
    ("fold candidate list", mutateFold program fun fold => { fold with candidates := #[] }),
    ("fold candidate duplication", mutateFold program fun fold => {
      fold with candidates := #[fold.candidates[0]!, fold.candidates[0]!] }),
    ("fold output fingerprint", mutateFold program fun fold =>
      { fold with finalOutputFingerprint := "mutated" }),
    ("fold disposition", mutateFold program fun fold =>
      { fold with finalDisposition := .visit }),
    ("fold proof fact", mutateFold program fun fold =>
      { fold with finalProofPresent := true }),
    ("fold cache fact", mutateFold program fun fold => { fold with finalCache := none }),
    ("outer input fingerprint", mutateOuterEvent program fun event =>
      { event with inputFingerprint := "mutated" }),
    ("outer output fingerprint", mutateOuterEvent program fun event =>
      { event with outputFingerprint := "mutated" }),
    ("outer disposition", mutateOuterEvent program fun event =>
      { event with stepDisposition := .visit }),
    ("outer phase", mutateOuterEvent program fun event => { event with phase := .pre }),
    ("outer invocation ordinal", mutateOuterEvent program fun event =>
      { event with invocationOrdinal := event.invocationOrdinal + 1 }),
    ("outer operation summary", mutateOuterEvent program fun event =>
      { event with operation := .builtin .decideTrue })]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayReject label expression ctx config mutation trace)
  return rejected

def checkDSimpMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("dphase candidate cache fact", mutateCandidate program fun candidate =>
      { candidate with cache := some true }),
    ("dphase fold cache fact", mutateFold program fun fold =>
      { fold with finalCache := some true }),
    ("dphase fold phase", mutateFold program fun fold => { fold with phase := .post })]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayReject label expression ctx config mutation trace)
  return rejected

def checkExpr (label : String) (expression : Expr) : MetaM Nat := do
  let builtins ← Simp.getSimprocs
  let methods := { Simp.Engine.mkDefaultMethodsCore #[builtins] with
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression ctx (methods := methods)
  checkNatWfPreludeObservations label recording.simprocs.observations
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  let semantics := recording.program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  unless semantics.size == 1 do
    throwError "{label}: expected exactly one semantic event, got {semantics.size}"
  let some event := semantics[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == .post && fold.candidates.size == 1 &&
      fold.finalDisposition == .done && !fold.finalProofPresent &&
      fold.finalCache == some true && event.stepDisposition == .done do
    throwError "{label}: fold summary mismatch: {repr fold}"
  let candidate := fold.candidates[0]!
  unless candidate.declaration == (if label == "add" then `Nat.reduceAdd else `Nat.reduceDiv) &&
      candidate.setIndex == 0 && candidate.procedureKind == .dsimp &&
      candidate.disposition == .done && !candidate.proofPresent && candidate.cache == some true do
    throwError "{label}: candidate mismatch: {repr candidate}"
  let config ← Simp.Engine.replayConfigOfContext ctx
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay expression ctx config recording.program
  unless Expr.equal recorded.expr replayed.expr do
    throwError "{label}: replay expression mismatch"
  let recordedSummary ← summarizeState recordedState
  let replayedSummary ← summarizeState replayedState
  unless recordedSummary == replayedSummary do
    throwError "{label}: replay state summary mismatch: {repr recordedSummary} != {repr replayedSummary}"
  if label == "add" then
    let semanticMutations ← checkMutations expression ctx config recording.program
      recording.simprocs
    let observationMutations ←
      checkObservationMutations recording.program recording.simprocs
    return semanticMutations + observationMutations
  return 0

def checkDSimpExpr (label : String) (expression : Expr) : MetaM Nat := do
  let builtins ← Simp.getSimprocs
  let methods := Simp.Engine.mkDefaultMethodsCore #[builtins]
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (recorded, recordedState, recording) ←
    Simp.Engine.dsimpMainCoreRecording expression ctx (methods := methods)
  checkNatWfPreludeObservations label recording.simprocs.observations
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  let semantics := recording.program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  unless semantics.size == 1 do
    throwError "{label}: expected exactly one semantic event, got {semantics.size}"
  let some event := semantics[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == .dpost && fold.candidates.size == 1 &&
      fold.finalDisposition == .done && !fold.finalProofPresent && fold.finalCache.isNone &&
      event.stepDisposition == .done do
    throwError "{label}: wrong dsimp fold summary: {repr fold}"
  let candidate := fold.candidates[0]!
  unless candidate.declaration == (if label == "dadd" then `Nat.reduceAdd else `Nat.reduceDiv) &&
      candidate.setIndex == 0 && candidate.procedureKind == .dsimp &&
      candidate.disposition == .done && candidate.cache.isNone && !candidate.proofPresent do
    throwError "{label}: dsimp candidate mismatch: {repr candidate}"
  let config ← Simp.Engine.replayConfigOfContext ctx
  let (replayed, replayedState) ←
    Simp.Engine.dsimpMainCoreReplay expression ctx config recording.program
  unless Expr.equal recorded replayed do
    throwError "{label}: dsimp replay expression mismatch"
  let recordedSummary ← summarizeState recordedState
  let replayedSummary ← summarizeState replayedState
  unless recordedSummary == replayedSummary do
    throwError "{label}: dsimp replay state summary mismatch: {repr recordedSummary} != {repr replayedSummary}"
  if label == "dadd" then
    return ← checkDSimpMutations expression ctx config recording.program recording.simprocs
  return 0

elab "check_nat_binary_fold" : tactic => withMainContext do
  let raw7 := mkNatLit 7
  let raw11 := mkNatLit 11
  let raw20 := mkNatLit 20
  let raw5 := mkNatLit 5
  let add := natBinary ``HAdd.hAdd Nat.mkInstHAdd raw7 raw11
  let div := natBinary ``HDiv.hDiv Nat.mkInstHDiv raw20 raw5
  let ordinaryMutations ← checkExpr "add" add
  let _ ← checkExpr "div" div
  let dphaseMutations ← checkDSimpExpr "dadd" add
  let _ ← checkDSimpExpr "ddiv" div
  let mutations := ordinaryMutations + dphaseMutations
  unless mutations == 34 do
    throwError "unexpected Nat binary fold mutation count: {mutations}"
  logInfo m!"SIMP_ENGINE_NAT_BINARY_FOLD_MUTATIONS rejected={mutations}"
  logInfo "SIMP_ENGINE_NAT_BINARY_FOLD add,div,dadd,ddiv: ok"

example : True := by
  check_nat_binary_fold
  trivial

end NatBinaryFoldProbe
