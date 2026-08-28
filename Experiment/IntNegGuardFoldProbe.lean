import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace IntNegGuardFoldProbe

open Lean.Meta.Simp.Engine

def intNegOfNatArgument (negInstance argument : Expr) : Expr :=
  mkApp3 (mkConst ``Neg.neg [.zero]) (mkConst ``Int) negInstance argument

def intNegOfNat (negInstance ofNatInstance : Expr) (value : Nat) : Expr :=
  let argument := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int)
    (mkNatLit value) ofNatInstance
  intNegOfNatArgument negInstance argument

def standardNegIntInstance : Expr := mkConst ``Int.instNegInt

def standardIntOfNatInstance (value : Nat) : Expr :=
  mkApp (mkConst ``instOfNat) (mkRawNatLit value)

def standardIntLiteral (value : Nat) (metadataDepth : Nat := 0) : Expr :=
  let numeral := if metadataDepth == 0 then
    mkRawNatLit value
  else
    mkMData MData.empty (mkRawNatLit value)
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int) numeral
    (standardIntOfNatInstance value)

def intNegateLiteral (value : Nat) (metadataDepth : Nat := 0) : Expr :=
  let positive := standardIntLiteral value metadataDepth
  let inner := intNegOfNatArgument standardNegIntInstance positive
  intNegOfNatArgument standardNegIntInstance inner

def customIntNegateLiteral (outerNeg innerNeg literalInstance : Expr) (value : Nat) : Expr :=
  let positive := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int)
    (mkRawNatLit value) literalInstance
  let inner := intNegOfNatArgument innerNeg positive
  intNegOfNatArgument outerNeg inner

@[reducible] def customNegInt : Neg Int := ⟨fun value => value⟩

@[reducible] def customOfNatInt7 : OfNat Int 7 := ⟨0⟩

def resultFingerprint (result : Simp.Result) : MetaM String := do
  let expression ← exprFingerprintHash result.expr
  let proof ← result.proof?.mapM exprFingerprintHash
  return s!"{expression}|{proof}|{result.cache}"

def cacheFingerprint (cache : Simp.Cache) : MetaM String := do
  let entries ← cache.toList.mapM fun (key, value) => do
    let keyFingerprint ← exprFingerprintHash key
    let valueFingerprint ← resultFingerprint value
    pure s!"{keyFingerprint}=>{valueFingerprint}"
  return s!"stage₁={cache.stage₁};{entries.toArray.qsort (· < ·) |>.toList |> String.intercalate ","}"

def dsimpCacheFingerprint (cache : ExprStructMap Expr) : MetaM String := do
  let entries ← cache.toList.mapM fun (key, value) => do
    let keyFingerprint ← exprFingerprintHash key.val
    let valueFingerprint ← exprFingerprintHash value
    pure s!"{keyFingerprint}=>{valueFingerprint}"
  return entries.toArray.qsort (· < ·) |>.toList |> String.intercalate ","

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
  let sort := fun values : List String => values.toArray.qsort (· < ·) |>.toList
  return s!"used={String.intercalate "," (sort used)};tried={String.intercalate "," (sort tried)};congr={String.intercalate "," (sort congr)};badKeys={String.intercalate "," (sort badKeys)}"

structure StateSummary where
  numSteps : Nat
  cache : String
  dsimpCache : String
  usedTheorems : String
  diagnostics : String
  deriving BEq, Repr

def summarizeState (state : Simp.State) : MetaM StateSummary := do
  let used := state.usedTheorems.toArray.toList.map reprStr
  return {
    numSteps := state.numSteps
    cache := ← cacheFingerprint state.cache
    dsimpCache := ← dsimpCacheFingerprint state.dsimpCache
    usedTheorems := String.intercalate "," (used.toArray.qsort (· < ·) |>.toList)
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

def mutateInstancePath (witness : InstanceWitness) : InstanceWitness :=
  match witness.term with
  | .input reference =>
      { witness with term := .input { reference with path := #[] } }
  | _ => { witness with term := .literal (.nat 0) }

def mutateInstanceFingerprint (witness : InstanceWitness) : InstanceWitness :=
  match witness.term with
  | .input reference =>
      { witness with term := .input { reference with fingerprint := "mutated" } }
  | _ => { witness with term := .literal (.nat 0) }

def mutateInstanceTerm (witness : InstanceWitness) : InstanceWitness :=
  { witness with term := .literal (.nat 0) }

def mutateInstanceTypeFingerprint (witness : InstanceWitness) : InstanceWitness :=
  { witness with typeFingerprint := "mutated" }

def literalEventIndex? (program : Simp.Engine.Program) : Option Nat := Id.run do
  let mut found? : Option Nat := none
  for h : index in *...program.events.size do
    if found?.isNone then
      let event := program.events[index]
      let found := match event.operation with
        | .semanticSimproc fold => fold.candidates.any fun candidate =>
            match candidate.semantics with
            | .canonicalValue (.intNegateLiteral _) => true
            | _ => false
        | _ => false
      if found then
        found? := some index
  return found?

def mutateLiteralCandidateRaw (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocCandidateEvent → Simp.Engine.SimprocCandidateEvent) :
    Simp.Engine.Program :=
  match literalEventIndex? program with
  | none => program
  | some eventIndex =>
      match program.events[eventIndex]? with
      | some event =>
          match event.operation with
          | .semanticSimproc fold =>
              let candidate := mutate fold.candidates[0]!
              let fold := { fold with candidates := fold.candidates.set! 0 candidate }
              { program with events := program.events.set! eventIndex {
                  event with operation := .semanticSimproc fold } }
          | _ => program
      | none => program

def mutateLiteralCandidate (program : Simp.Engine.Program)
    (mutate : IntNegateLiteralDerivation → IntNegateLiteralDerivation) :
    Simp.Engine.Program :=
  mutateLiteralCandidateRaw program fun candidate =>
    match candidate.semantics with
    | .canonicalValue (.intNegateLiteral derivation) =>
        { candidate with semantics :=
            .canonicalValue (.intNegateLiteral (mutate derivation)) }
    | _ => candidate

def mutateLiteralFold (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocFold → Simp.Engine.SimprocFold) :
    Simp.Engine.Program :=
  match literalEventIndex? program with
  | none => program
  | some eventIndex =>
      match program.events[eventIndex]? with
      | some event =>
          match event.operation with
          | .semanticSimproc fold =>
              { program with events := program.events.set! eventIndex {
                  event with operation := .semanticSimproc (mutate fold) } }
          | _ => program
      | none => program

def mutateLiteralOuterEvent (program : Simp.Engine.Program)
    (mutate : Simp.Engine.Event → Simp.Engine.Event) : Simp.Engine.Program :=
  match literalEventIndex? program with
  | none => program
  | some eventIndex =>
      match program.events[eventIndex]? with
      | none => program
      | some event =>
          { program with events := program.events.modify eventIndex fun _ => mutate event }

def literalSemanticEvents (program : Simp.Engine.Program) : Array Simp.Engine.Event :=
  program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc fold => fold.candidates.any fun candidate =>
        match candidate.semantics with
        | .canonicalValue (.intNegateLiteral _) => true
        | _ => false
    | _ => false

def expectFailure {α : Type} (label : String) (action : MetaM α) : MetaM Nat := do
  let saved ← Meta.saveState
  let succeeded ← try
    let _ ← action
    pure true
  catch _ => pure false
  saved.restore
  unless !succeeded do
    throwError "{label}: rejection was not local"
  pure 1

def expectReplayFailure (label : String) (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace? : Option Simp.Engine.SimprocTrace := none) : MetaM Nat :=
  expectFailure label (do
    if let some trace := trace? then
      ExplicitLean.SimpEngine.Replay.validateSimprocObservations program trace
    let _ ← Simp.Engine.mainCoreReplay expression ctx config program
    pure ())

def checkPreludeObservations (label : String) (observations : Array SimprocObservation) :
    MetaM Unit := do
  let continueNone := observations.filter fun observation =>
    observation.executed && observation.stepDisposition == .continueNone
  let allowed := fun name : Name => isIgnorableWfContinueNone name
  for observation in continueNone do
    unless allowed observation.name do
      throwError "{label}: unsupported ignored continue-none observation {observation.name}"
  unless observations.any fun observation =>
      observation.executed && observation.name == `Int.reduceNeg &&
        observation.stepDisposition == .done do
    throwError "{label}: missing terminating Int.reduceNeg observation"

def checkGuardMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let some event := program.events[0]? | throwError "mutation fixture has no event"
  let .semanticSimproc _ := event.operation | throwError "mutation fixture has no semantic fold"
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("candidate declaration", mutateCandidate program fun candidate =>
      { candidate with declaration := `Nat.reduceAdd }),
    ("candidate procedure kind", mutateCandidate program fun candidate =>
      { candidate with procedureKind := .simp }),
    ("candidate registry provenance", mutateCandidate program fun candidate =>
      { candidate with registryPost := false }),
    ("candidate semantics path", mutateCandidate program fun candidate =>
      match candidate.semantics with
      | .valueGuard (.intNegOfNatSyntax argument) =>
          { candidate with semantics := .valueGuard (.intNegOfNatSyntax {
              argument with path := #[] }) }
      | _ => candidate),
    ("candidate semantics fingerprint", mutateCandidate program fun candidate =>
      match candidate.semantics with
      | .valueGuard (.intNegOfNatSyntax argument) =>
          { candidate with semantics := .valueGuard (.intNegOfNatSyntax {
              argument with fingerprint := "mutated" }) }
      | _ => candidate),
    ("candidate wrong semantic constructor", mutateCandidate program fun candidate =>
      { candidate with semantics := .canonicalValue (.natBinary default) }),
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
    ("fold candidates empty", mutateFold program fun fold => { fold with candidates := #[] }),
    ("fold candidates duplicated", mutateFold program fun fold => {
      fold with candidates := #[fold.candidates[0]!, fold.candidates[0]!] }),
    ("fold phase", mutateFold program fun fold => { fold with phase := .pre }),
    ("fold output fingerprint", mutateFold program fun fold =>
      { fold with finalOutputFingerprint := "mutated" }),
    ("fold disposition", mutateFold program fun fold =>
      { fold with finalDisposition := .visit }),
    ("fold proof fact", mutateFold program fun fold =>
      { fold with finalProofPresent := true }),
    ("fold cache fact", mutateFold program fun fold => { fold with finalCache := none }),
    ("outer phase", mutateOuterEvent program fun event => { event with phase := .pre }),
    ("outer input fingerprint", mutateOuterEvent program fun event =>
      { event with inputFingerprint := "mutated" }),
    ("outer output fingerprint", mutateOuterEvent program fun event =>
      { event with outputFingerprint := "mutated" }),
    ("outer disposition", mutateOuterEvent program fun event =>
      { event with stepDisposition := .visit }),
    ("outer invocation ordinal", mutateOuterEvent program fun event =>
      { event with invocationOrdinal := event.invocationOrdinal + 1 }),
    ("outer operation", mutateOuterEvent program fun event =>
      { event with operation := .builtin .decideTrue })]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayFailure label expression ctx config mutation (some trace))
  return rejected

def checkLiteralMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("literal candidate declaration", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with declaration := `Nat.reduceAdd }),
    ("literal candidate procedure kind", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with procedureKind := .simp }),
    ("literal candidate registry provenance", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with registryPost := false }),
    ("literal candidate wrong semantic constructor", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with semantics := .valueGuard (.intNegOfNatSyntax default) }),
    ("literal candidate set index", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with setIndex := 1 }),
    ("literal candidate input fingerprint", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with inputFingerprint := "mutated" }),
    ("literal candidate peeled input fingerprint", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with peeledInputFingerprint := "mutated" }),
    ("literal candidate extra argument fingerprints", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with extraArgumentFingerprints := #["mutated"] }),
    ("literal candidate procedure output fingerprint", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with procedureOutputFingerprint := "mutated" }),
    ("literal candidate output fingerprint", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with outputFingerprint := "mutated" }),
    ("literal candidate extra argument count", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with numExtraArgs := candidate.numExtraArgs + 1 }),
    ("literal candidate disposition", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with disposition := .visit }),
    ("literal candidate proof fact", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with proofPresent := true }),
    ("literal candidate cache fact", mutateLiteralCandidateRaw program fun candidate =>
      { candidate with cache := none }),
    ("literal magnitude", mutateLiteralCandidate program fun derivation =>
      { derivation with magnitude := derivation.magnitude + 1 }),
    ("literal result", mutateLiteralCandidate program fun derivation =>
      { derivation with result := Int.ofNat (derivation.magnitude + 1) }),
    ("literal argument path", mutateLiteralCandidate program fun derivation =>
      { derivation with argument := { derivation.argument with path := #[] } }),
    ("literal argument fingerprint", mutateLiteralCandidate program fun derivation =>
      { derivation with argument := { derivation.argument with fingerprint := "mutated" } }),
    ("literal numeral path", mutateLiteralCandidate program fun derivation =>
      { derivation with numeral := { derivation.numeral with path := #[] } }),
    ("literal numeral fingerprint", mutateLiteralCandidate program fun derivation =>
      { derivation with numeral := { derivation.numeral with fingerprint := "mutated" } }),
    ("literal numeral metadata depth", mutateLiteralCandidate program fun derivation =>
      { derivation with numeralMetadataDepth := derivation.numeralMetadataDepth + 1 }),
    ("literal outer instance path", mutateLiteralCandidate program fun derivation =>
      { derivation with outerNegInstance :=
          mutateInstancePath derivation.outerNegInstance }),
    ("literal outer instance fingerprint", mutateLiteralCandidate program fun derivation =>
      { derivation with outerNegInstance :=
          mutateInstanceFingerprint derivation.outerNegInstance }),
    ("literal outer instance term", mutateLiteralCandidate program fun derivation =>
      { derivation with outerNegInstance := mutateInstanceTerm derivation.outerNegInstance }),
    ("literal outer instance type fingerprint", mutateLiteralCandidate program fun derivation =>
      { derivation with outerNegInstance :=
          mutateInstanceTypeFingerprint derivation.outerNegInstance }),
    ("literal inner instance path", mutateLiteralCandidate program fun derivation =>
      { derivation with innerNegInstance :=
          mutateInstancePath derivation.innerNegInstance }),
    ("literal inner instance fingerprint", mutateLiteralCandidate program fun derivation =>
      { derivation with innerNegInstance :=
          mutateInstanceFingerprint derivation.innerNegInstance }),
    ("literal inner instance term", mutateLiteralCandidate program fun derivation =>
      { derivation with innerNegInstance := mutateInstanceTerm derivation.innerNegInstance }),
    ("literal inner instance type fingerprint", mutateLiteralCandidate program fun derivation =>
      { derivation with innerNegInstance :=
          mutateInstanceTypeFingerprint derivation.innerNegInstance }),
    ("literal OfNat instance path", mutateLiteralCandidate program fun derivation =>
      { derivation with literalInstance := mutateInstancePath derivation.literalInstance }),
    ("literal OfNat instance fingerprint", mutateLiteralCandidate program fun derivation =>
      { derivation with literalInstance :=
          mutateInstanceFingerprint derivation.literalInstance }),
    ("literal OfNat instance term", mutateLiteralCandidate program fun derivation =>
      { derivation with literalInstance := mutateInstanceTerm derivation.literalInstance }),
    ("literal OfNat instance type fingerprint", mutateLiteralCandidate program fun derivation =>
      { derivation with literalInstance :=
          mutateInstanceTypeFingerprint derivation.literalInstance }),
    ("literal fold candidates empty", mutateLiteralFold program fun fold =>
      { fold with candidates := #[] }),
    ("literal fold candidates duplicated", mutateLiteralFold program fun fold => {
      fold with candidates := #[fold.candidates[0]!, fold.candidates[0]!] }),
    ("literal fold phase", mutateLiteralFold program fun fold => { fold with phase := .pre }),
    ("literal fold output fingerprint", mutateLiteralFold program fun fold =>
      { fold with finalOutputFingerprint := "mutated" }),
    ("literal fold disposition", mutateLiteralFold program fun fold =>
      { fold with finalDisposition := .visit }),
    ("literal fold proof fact", mutateLiteralFold program fun fold =>
      { fold with finalProofPresent := true }),
    ("literal fold cache fact", mutateLiteralFold program fun fold =>
      { fold with finalCache := none }),
    ("literal outer phase", mutateLiteralOuterEvent program fun event =>
      { event with phase := .pre }),
    ("literal outer input fingerprint", mutateLiteralOuterEvent program fun event =>
      { event with inputFingerprint := "mutated" }),
    ("literal outer output fingerprint", mutateLiteralOuterEvent program fun event =>
      { event with outputFingerprint := "mutated" }),
    ("literal outer disposition", mutateLiteralOuterEvent program fun event =>
      { event with stepDisposition := .visit }),
    ("literal outer invocation ordinal", mutateLiteralOuterEvent program fun event =>
      { event with invocationOrdinal := event.invocationOrdinal + 1 }),
    ("literal outer operation", mutateLiteralOuterEvent program fun event =>
      { event with operation := .builtin .decideTrue })]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayFailure label expression ctx config mutation (some trace))
  return rejected

def checkGuardRecording (expression : Expr) : MetaM Nat := do
  let builtins ← Simp.getSimprocs
  let methods := { Simp.Engine.mkDefaultMethodsCore #[builtins] with
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression ctx (methods := methods)
  checkPreludeObservations "ordinary" recording.simprocs.observations
  unless recording.deferred.isNone do
    throwError "ordinary: recording deferred: {repr recording.deferred}"
  let semantics := recording.program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false
  unless semantics.size == 1 do
    throwError "ordinary: expected one semantic fold, got {semantics.size}"
  let some event := semantics[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == .post && fold.candidates.size == 1 &&
      fold.finalDisposition == .done && !fold.finalProofPresent &&
      fold.finalCache == some true && event.stepDisposition == .done do
    throwError "ordinary: fold summary mismatch: {repr fold}"
  let candidate := fold.candidates[0]!
  let .valueGuard (.intNegOfNatSyntax argument) := candidate.semantics
    | throwError "ordinary: wrong semantic constructor"
  unless candidate.declaration == `Int.reduceNeg && candidate.procedureKind == .dsimp &&
      candidate.setIndex == 0 && candidate.inputFingerprint == event.inputFingerprint &&
      candidate.peeledInputFingerprint == candidate.procedureOutputFingerprint &&
      candidate.outputFingerprint == event.outputFingerprint &&
      candidate.extraArgumentFingerprints.isEmpty && candidate.numExtraArgs == 0 &&
      candidate.disposition == .done && !candidate.proofPresent &&
      candidate.cache == some true && candidate.registryPost &&
      argument.path == #[.appArgument] do
    throwError "ordinary: candidate mismatch: {repr candidate}"
  let config ← Simp.Engine.replayConfigOfContext ctx
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay expression ctx config recording.program
  unless Expr.equal recorded.expr replayed.expr do
    throwError "ordinary: replay expression mismatch"
  let recordedSummary ← summarizeState recordedState
  let replayedSummary ← summarizeState replayedState
  unless recordedSummary == replayedSummary do
    throwError "ordinary: replay state summary mismatch: {repr recordedSummary} != {repr replayedSummary}"
  let mutationCount ← checkGuardMutations expression ctx config recording.program
    recording.simprocs
  let observationProgram := { recording.program with events := #[] }
  let _ ← expectFailure "observation without fold" <|
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations observationProgram
      recording.simprocs
  return mutationCount

def checkGuardDSimpRecording (expression : Expr) : MetaM Nat := do
  let builtins ← Simp.getSimprocs
  let methods := Simp.Engine.mkDefaultMethodsCore #[builtins]
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (recorded, recordedState, recording) ←
    Simp.Engine.dsimpMainCoreRecording expression ctx (methods := methods)
  checkPreludeObservations "dphase" recording.simprocs.observations
  unless recording.deferred.isNone do
    throwError "dphase: recording deferred: {repr recording.deferred}"
  let semantics := recording.program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false
  unless semantics.size == 1 do
    throwError "dphase: expected one semantic fold, got {semantics.size}"
  let some event := semantics[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == .dpost && fold.candidates.size == 1 &&
      fold.finalDisposition == .done && !fold.finalProofPresent &&
      fold.finalCache.isNone && event.stepDisposition == .done do
    throwError "dphase: fold summary mismatch: {repr fold}"
  let candidate := fold.candidates[0]!
  unless candidate.declaration == `Int.reduceNeg && candidate.procedureKind == .dsimp &&
      candidate.setIndex == 0 && candidate.disposition == .done &&
      candidate.registryPost && !candidate.proofPresent && candidate.cache.isNone do
    throwError "dphase: candidate mismatch: {repr candidate}"
  let config ← Simp.Engine.replayConfigOfContext ctx
  let (replayed, replayedState) ←
    Simp.Engine.dsimpMainCoreReplay expression ctx config recording.program
  unless Expr.equal recorded replayed do
    throwError "dphase: replay expression mismatch"
  let recordedSummary ← summarizeState recordedState
  let replayedSummary ← summarizeState replayedState
  unless recordedSummary == replayedSummary do
    throwError "dphase: replay state summary mismatch: {repr recordedSummary} != {repr replayedSummary}"
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("dphase candidate cache", mutateCandidate recording.program fun candidate =>
      { candidate with cache := some true }),
    ("dphase fold cache", mutateFold recording.program fun fold =>
      { fold with finalCache := some true }),
    ("dphase phase", mutateFold recording.program fun fold => { fold with phase := .post })]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayFailure label expression ctx config mutation
      (some recording.simprocs))
  return rejected

def checkLiteralRecording (label : String) (expression : Expr) (magnitude : Nat)
    (numeralMetadataDepth : Nat := 0) : MetaM Nat := do
  let builtins ← Simp.getSimprocs
  let methods := { Simp.Engine.mkDefaultMethodsCore #[builtins] with
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression ctx (methods := methods)
  checkPreludeObservations label recording.simprocs.observations
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  let semantics := literalSemanticEvents recording.program
  unless semantics.size == 1 do
    throwError "{label}: expected one semantic fold, got {semantics.size}"
  let some event := semantics[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == .post && fold.candidates.size == 1 &&
      fold.finalDisposition == .done && !fold.finalProofPresent &&
      fold.finalCache == some true && event.stepDisposition == .done &&
      fold.finalOutputFingerprint == event.outputFingerprint do
    throwError "{label}: fold summary mismatch: {repr fold}"
  let candidate := fold.candidates[0]!
  let .canonicalValue (.intNegateLiteral derivation) := candidate.semantics
    | throwError "{label}: wrong semantic constructor"
  unless candidate.declaration == `Int.reduceNeg && candidate.procedureKind == .dsimp &&
      candidate.setIndex == 0 && candidate.registryPost &&
      candidate.inputFingerprint == event.inputFingerprint &&
      candidate.outputFingerprint == event.outputFingerprint &&
      candidate.extraArgumentFingerprints.isEmpty && candidate.numExtraArgs == 0 &&
      candidate.disposition == .done && !candidate.proofPresent &&
      candidate.cache == some true && derivation.magnitude == magnitude &&
      derivation.result == Int.ofNat magnitude &&
      derivation.argument.path == #[.appArgument] &&
      derivation.numeralMetadataDepth == numeralMetadataDepth do
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
  let mutationCount ← checkLiteralMutations expression ctx config recording.program
    recording.simprocs
  let observationProgram := { recording.program with events := #[] }
  let _ ← expectFailure "{label}: observation without fold" <|
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations observationProgram
      recording.simprocs
  return mutationCount

def checkLiteralDSimpRecording (label : String) (expression : Expr) (magnitude : Nat) :
    MetaM Nat := do
  let builtins ← Simp.getSimprocs
  let methods := Simp.Engine.mkDefaultMethodsCore #[builtins]
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (recorded, recordedState, recording) ←
    Simp.Engine.dsimpMainCoreRecording expression ctx (methods := methods)
  checkPreludeObservations label recording.simprocs.observations
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  let semantics := literalSemanticEvents recording.program
  unless semantics.size == 1 do
    throwError "{label}: expected one semantic fold, got {semantics.size}"
  let some event := semantics[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == .dpost && fold.candidates.size == 1 &&
      fold.finalDisposition == .done && !fold.finalProofPresent &&
      fold.finalCache.isNone && event.stepDisposition == .done &&
      fold.finalOutputFingerprint == event.outputFingerprint do
    throwError "{label}: fold summary mismatch: {repr fold}"
  let candidate := fold.candidates[0]!
  let .canonicalValue (.intNegateLiteral derivation) := candidate.semantics
    | throwError "{label}: wrong semantic constructor"
  unless candidate.declaration == `Int.reduceNeg && candidate.procedureKind == .dsimp &&
      candidate.setIndex == 0 && candidate.registryPost &&
      candidate.outputFingerprint == event.outputFingerprint &&
      candidate.extraArgumentFingerprints.isEmpty && candidate.numExtraArgs == 0 &&
      candidate.disposition == .done && !candidate.proofPresent &&
      candidate.cache.isNone && derivation.magnitude == magnitude do
    throwError "{label}: candidate mismatch: {repr candidate}"
  let config ← Simp.Engine.replayConfigOfContext ctx
  let (replayed, replayedState) ←
    Simp.Engine.dsimpMainCoreReplay expression ctx config recording.program
  unless Expr.equal recorded replayed do
    throwError "{label}: replay expression mismatch"
  let recordedSummary ← summarizeState recordedState
  let replayedSummary ← summarizeState replayedState
  unless recordedSummary == replayedSummary do
    throwError "{label}: replay state summary mismatch: {repr recordedSummary} != {repr replayedSummary}"
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("{label}: candidate cache", mutateCandidate recording.program fun candidate =>
      { candidate with cache := some true }),
    ("{label}: fold cache", mutateFold recording.program fun fold =>
      { fold with finalCache := some true }),
    ("{label}: phase", mutateFold recording.program fun fold =>
      { fold with phase := .post })]
  let mut rejected := 0
  for (mutationLabel, mutation) in mutations do
    rejected := rejected + (← expectReplayFailure mutationLabel expression ctx config mutation
      (some recording.simprocs))
  return rejected

def checkLiteralSemanticHelper (label : String) (expression : Expr) (magnitude : Nat)
    (numeralMetadataDepth : Nat := 0) : MetaM Unit := do
  let output := toExpr (Int.ofNat magnitude)
  let some derivation ← deriveIntNegateLiteral? `Int.reduceNeg expression output
    | do
      throwError "{label}: changing Int negation was not recognized"
  unless derivation.magnitude == magnitude && derivation.result == Int.ofNat magnitude &&
      derivation.argument.path == #[.appArgument] &&
      derivation.numeralMetadataDepth == numeralMetadataDepth do
    throwError "{label}: changing derivation fields mismatch: {repr derivation}"
  let semantics : SemanticSimproc := .canonicalValue (.intNegateLiteral derivation)
  let decoded : SemanticSimproc ←
    match Lean.fromJson? (Lean.toJson semantics) with
    | .ok decoded => pure decoded
    | .error message => throwError "{label}: changing JSON roundtrip failed: {message}"
  unless decoded == semantics do
    throwError "{label}: changing JSON roundtrip changed the semantic payload"
  let interpreted ← interpretIntNegateLiteral expression derivation
  unless Expr.equal interpreted output do
    throwError "{label}: changing interpretation did not build the canonical output"

def checkLiteralUnsupported : MetaM Unit := do
  let standardOuter := standardNegIntInstance
  let standardInner := standardNegIntInstance
  let standardOfNat := standardIntOfNatInstance 7
  let expression := intNegateLiteral 7
  let output := toExpr (Int.ofNat 7)
  let metadataOuter := mkMData MData.empty expression
  let inner := intNegOfNatArgument standardInner (standardIntLiteral 7)
  let metadataInner := intNegOfNatArgument standardOuter (mkMData MData.empty inner)
  let wrongOuterArity := mkApp2 (mkConst ``Neg.neg [.zero]) (mkConst ``Int) standardOuter
  let wrongInnerName := intNegOfNatArgument standardOuter
    (mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
      (mkConst ``Int) (mkConst ``Int) (mkConst ``Int)
      standardInner (mkNatLit 1) (mkNatLit 2))
  let wrongOfNatArity := intNegOfNatArgument standardOuter
    (mkApp2 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int) (mkRawNatLit 7))
  let mvar ← mkFreshExprMVar (mkConst ``Nat)
  let openOfNat := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int) mvar standardOfNat
  let openInput := intNegOfNatArgument standardOuter (intNegOfNatArgument standardInner openOfNat)
  for (label, candidate) in #[
      ("changing metadata outer", metadataOuter),
      ("changing metadata inner", metadataInner),
      ("changing wrong outer arity", wrongOuterArity),
      ("changing wrong inner name", wrongInnerName),
      ("changing wrong OfNat arity", wrongOfNatArity),
      ("changing open input", openInput)] do
    unless (← deriveIntNegateLiteral? `Int.reduceNeg candidate output).isNone do
      throwError "{label}: unsupported changing shape was accepted"
  let customOuter := customIntNegateLiteral (mkConst ``customNegInt)
    standardInner standardOfNat 7
  let customInner := customIntNegateLiteral standardOuter
    (mkConst ``customNegInt) standardOfNat 7
  let customOfNat := customIntNegateLiteral standardOuter standardInner
    (mkConst ``customOfNatInt7) 7
  for (label, candidate) in #[
      ("changing custom outer instance", customOuter),
      ("changing custom inner instance", customInner),
      ("changing custom OfNat instance", customOfNat)] do
    unless (← deriveIntNegateLiteral? `Int.reduceNeg candidate output).isNone do
      throwError "{label}: nonstandard changing instance was accepted"
  return ()

def checkLiteralDeferred (label : String) (expression : Expr) (dphase : Bool) : MetaM Unit := do
  let builtins ← Simp.getSimprocs
  let methods ← if dphase then
    pure (Simp.Engine.mkDefaultMethodsCore #[builtins])
  else
    pure { Simp.Engine.mkDefaultMethodsCore #[builtins] with
      dpre := fun _ => pure .continue
      dpost := fun _ => pure .continue }
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let recording ← if dphase then
    let (_, _, recording) ← Simp.Engine.dsimpMainCoreRecording expression ctx (methods := methods)
    pure recording
  else
    let (_, _, recording) ← Simp.Engine.mainCoreRecording expression ctx (methods := methods)
    pure recording
  checkPreludeObservations label recording.simprocs.observations
  unless recording.deferred.isSome do
    throwError "{label}: unsupported changing instance was not deferred"
  unless recording.program.events.all fun event =>
      match event.operation with
      | .semanticSimproc fold => fold.candidates.all fun candidate =>
          match candidate.semantics with
          | .canonicalValue (.intNegateLiteral _) => false
          | _ => true
      | _ => true do
    throwError "{label}: unsupported changing instance emitted a changing fold"
  return ()

def checkSemanticHelpers : MetaM Unit := do
  let negInstance := mkConst ``customNegInt
  let ofNatInstance := mkConst ``customOfNatInt7
  let guard := intNegOfNat negInstance ofNatInstance 7
  let some reference ← deriveIntNegOfNatSyntax? `Int.reduceNeg guard guard
    | throwError "custom guard was not recognized"
  let semantics : SemanticSimproc := .valueGuard (.intNegOfNatSyntax reference)
  let decoded : SemanticSimproc ←
    match Lean.fromJson? (Lean.toJson semantics) with
    | .ok decoded => pure decoded
    | .error message => throwError "guard JSON roundtrip failed: {message}"
  unless decoded == semantics do
    throwError "guard JSON roundtrip changed the semantic payload"
  let interpreted ← interpretIntNegOfNatSyntax guard reference
  unless Expr.equal guard interpreted do
    throwError "custom guard interpretation changed the expression"
  let metadataGuard := mkMData MData.empty guard
  unless (← deriveIntNegOfNatSyntax? `Int.reduceNeg metadataGuard metadataGuard).isNone do
    throwError "metadata-wrapped guard was accepted"
  let metadataOfNat := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int)
    (mkNatLit 7) ofNatInstance
  let metadataArgument := intNegOfNatArgument negInstance
    (mkMData MData.empty metadataOfNat)
  unless (← deriveIntNegOfNatSyntax? `Int.reduceNeg metadataArgument metadataArgument).isNone do
    throwError "metadata-wrapped OfNat argument was accepted"
  let wrongArity := mkApp2 (mkConst ``Neg.neg [.zero]) (mkConst ``Int) negInstance
  unless (← deriveIntNegOfNatSyntax? `Int.reduceNeg wrongArity wrongArity).isNone do
    throwError "wrong-arity Neg.neg was accepted"
  let wrongName := mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    (mkConst ``Int) (mkConst ``Int) (mkConst ``Int)
    negInstance (mkNatLit 1) (mkNatLit 2)
  unless (← deriveIntNegOfNatSyntax? `Int.reduceNeg wrongName wrongName).isNone do
    throwError "wrong-name expression was accepted"
  let mvar ← mkFreshExprMVar (mkConst ``Nat)
  let openArgument := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int)
    mvar ofNatInstance
  let openGuard := intNegOfNatArgument negInstance openArgument
  unless (← deriveIntNegOfNatSyntax? `Int.reduceNeg openGuard openGuard).isNone do
    throwError "open guard was accepted"
  unless (← deriveIntNegOfNatSyntax? `Int.reduceNeg guard (mkNatLit 0)).isNone do
    throwError "changed-output guard was accepted"
  let wrongOfNat := mkApp2 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int) (mkNatLit 7)
  let wrongOfNatGuard := mkApp3 (mkConst ``Neg.neg [.zero]) (mkConst ``Int)
    negInstance wrongOfNat
  unless (← deriveIntNegOfNatSyntax? `Int.reduceNeg wrongOfNatGuard wrongOfNatGuard).isNone do
    throwError "wrong-arity OfNat was accepted"

elab "check_int_neg_guard_fold" : tactic => withMainContext do
  checkSemanticHelpers
  checkLiteralSemanticHelper "changing nonzero" (intNegateLiteral 7) 7
  checkLiteralSemanticHelper "changing zero" (intNegateLiteral 0) 0
  checkLiteralSemanticHelper "changing metadata" (intNegateLiteral 7 1) 7 1
  checkLiteralUnsupported
  let guard := intNegOfNat (mkConst ``customNegInt) (mkConst ``customOfNatInt7) 7
  let customOuter := customIntNegateLiteral (mkConst ``customNegInt)
    standardNegIntInstance (standardIntOfNatInstance 7) 7
  let customInner := customIntNegateLiteral standardNegIntInstance
    (mkConst ``customNegInt) (standardIntOfNatInstance 7) 7
  let customOfNat := customIntNegateLiteral standardNegIntInstance standardNegIntInstance
    (mkConst ``customOfNatInt7) 7
  checkLiteralDeferred "custom outer ordinary" customOuter false
  checkLiteralDeferred "custom inner ordinary" customInner false
  checkLiteralDeferred "custom OfNat ordinary" customOfNat false
  checkLiteralDeferred "custom outer dphase" customOuter true
  checkLiteralDeferred "custom inner dphase" customInner true
  checkLiteralDeferred "custom OfNat dphase" customOfNat true
  let ordinaryMutations ← checkGuardRecording guard
  let dphaseMutations ← checkGuardDSimpRecording guard
  let zeroOrdinaryMutations ← checkLiteralRecording "changing zero ordinary"
    (intNegateLiteral 0) 0
  let nonzeroOrdinaryMutations ← checkLiteralRecording "changing nonzero ordinary"
    (intNegateLiteral 7) 7
  let zeroDphaseMutations ← checkLiteralDSimpRecording "changing zero dphase"
    (intNegateLiteral 0) 0
  let nonzeroDphaseMutations ← checkLiteralDSimpRecording "changing nonzero dphase"
    (intNegateLiteral 7) 7
  logInfo m!"INT_NEG_GUARD_FOLD_MUTATIONS rejected={ordinaryMutations + dphaseMutations + zeroOrdinaryMutations + nonzeroOrdinaryMutations + zeroDphaseMutations + nonzeroDphaseMutations}"
  logInfo "INT_NEG_GUARD_FOLD custom,ordinary,dphase,changing,unsupported: ok"

example : True := by
  check_int_neg_guard_fold
  trivial

end IntNegGuardFoldProbe
