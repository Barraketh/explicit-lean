import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace FinLiteralFoldProbe

open Lean.Meta.Simp.Engine

def finLiteral (modulusExpression sourceExpression literalInstance : Expr) : Expr :=
  let type := mkApp (mkConst ``Fin) modulusExpression
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) type sourceExpression literalInstance

def standardFinInstance (modulus source : Nat) : Expr :=
  mkApp3 (mkConst ``Fin.instOfNat) (mkNatLit modulus)
    (mkApp (mkConst ``Nat.instNeZeroSucc) (mkNatLit (modulus - 1)))
    (mkRawNatLit source)

def standardFinLiteral (modulus source : Nat) : Expr :=
  finLiteral (mkNatLit modulus) (mkRawNatLit source)
    (standardFinInstance modulus source)

def rawFinLiteral (modulus source : Nat) : Expr :=
  finLiteral (mkRawNatLit modulus) (mkRawNatLit source)
    (standardFinInstance modulus source)

def standardNatOfNat (value : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit value)
    (mkInstOfNatNat (mkRawNatLit value))

def standardFinInstanceOfNat (modulus source : Nat) : Expr :=
  let modulusExpression := standardNatOfNat modulus
  mkApp3 (mkConst ``Fin.instOfNat) modulusExpression
    (mkApp (mkConst ``Nat.instNeZeroSucc) (standardNatOfNat (modulus - 1)))
    (mkRawNatLit source)

def standardFinLiteralOfNatModulus (modulus source : Nat) : Expr :=
  finLiteral (standardNatOfNat modulus) (mkRawNatLit source)
    (standardFinInstanceOfNat modulus source)

@[reducible] def customFinKeep : OfNat (Fin 5) 2 :=
  ⟨⟨2, by decide⟩⟩

@[reducible] def customFinReduce : OfNat (Fin 3) 5 :=
  ⟨⟨0, by decide⟩⟩

@[reducible] def customNatModulus : OfNat Nat 3 :=
  ⟨4⟩

def customKeepLiteral : Expr :=
  finLiteral (mkNatLit 5) (mkRawNatLit 2) (mkConst ``customFinKeep)

def customReduceLiteral : Expr :=
  finLiteral (mkNatLit 3) (mkRawNatLit 5) (mkConst ``customFinReduce)

def nonstandardModulusLiteral : Expr :=
  let modulusExpression := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat)
    (mkRawNatLit 3) (mkConst ``customNatModulus)
  finLiteral modulusExpression (mkRawNatLit 1) (standardFinInstance 4 1)

abbrev FinAlias := Fin 5

def aliasTypeLiteral : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``FinAlias)
    (mkRawNatLit 2) (mkConst ``customFinKeep)

def resultFingerprint (result : Simp.Result) : MetaM String := do
  let expression ← exprFingerprintHash result.expr
  let proof ← result.proof?.mapM exprFingerprintHash
  return s!"{expression}|{proof}|{result.cache}"

def sortStrings (values : List String) : List String :=
  values.toArray.qsort (· < ·) |>.toList

def listFingerprint (values : List String) : String :=
  String.intercalate "," (sortStrings values)

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
  return s!"used={listFingerprint used};tried={listFingerprint tried};congr={listFingerprint congr};badKeys={listFingerprint badKeys}"

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
    -- Closed replay consumes the explicit congruence witness.  The existing
    -- generic negative congruence lookup cache is outside this fold slice.
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
    (mutate : Simp.Engine.Event → Simp.Engine.Event) :
    Simp.Engine.Program :=
  match program.events[0]? with
  | none => program
  | some event => { program with events := program.events.set! 0 (mutate event) }

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

def mutateViewValue : NatValueView → NatValueView
  | .raw reference value metadataDepth =>
      .raw reference (value + 1) metadataDepth
  | .ofNat reference value metadataDepth witness =>
      .ofNat reference (value + 1) metadataDepth witness

def mutateViewPath : NatValueView → NatValueView
  | .raw reference value metadataDepth =>
      .raw { reference with path := #[] } value metadataDepth
  | .ofNat reference value metadataDepth witness =>
      .ofNat { reference with path := #[] } value metadataDepth witness

def mutateViewFingerprint : NatValueView → NatValueView
  | .raw reference value metadataDepth =>
      .raw { reference with fingerprint := "mutated" } value metadataDepth
  | .ofNat reference value metadataDepth witness =>
      .ofNat { reference with fingerprint := "mutated" } value metadataDepth witness

def mutateViewMetadata : NatValueView → NatValueView
  | .raw reference value metadataDepth =>
      .raw reference value (metadataDepth + 1)
  | .ofNat reference value metadataDepth witness =>
      .ofNat reference value (metadataDepth + 1) witness

def mutateViewConstructor : NatValueView → NatValueView
  | .raw reference value metadataDepth =>
      .ofNat reference value metadataDepth default
  | .ofNat reference value metadataDepth _ =>
      .raw reference value metadataDepth

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

def mutateGuardCandidate (program : Simp.Engine.Program)
    (mutate : FinLiteralGuard → FinLiteralGuard) : Simp.Engine.Program :=
  mutateCandidate program fun candidate =>
    match candidate.semantics with
    | .valueGuard (.finLiteralInRange derivation) =>
        { candidate with semantics :=
            (.valueGuard (.finLiteralInRange (mutate derivation))) }
    | _ => candidate

def mutateModuloCandidate (program : Simp.Engine.Program)
    (mutate : FinLiteralModuloDerivation → FinLiteralModuloDerivation) :
    Simp.Engine.Program :=
  mutateCandidate program fun candidate =>
    match candidate.semantics with
    | .canonicalValue (.finLiteralModulo derivation) =>
        { candidate with semantics :=
            (.canonicalValue (.finLiteralModulo (mutate derivation))) }
    | _ => candidate

def checkCommonMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("candidate declaration", mutateCandidate program fun candidate =>
      { candidate with declaration := `Nat.reduceAdd }),
    ("candidate procedure kind", mutateCandidate program fun candidate =>
      { candidate with procedureKind := .simp }),
    ("candidate registry provenance", mutateCandidate program fun candidate =>
      { candidate with registryPost := false }),
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
    ("candidate disposition", mutateCandidate program fun candidate =>
      { candidate with disposition := .visit }),
    ("candidate proof fact", mutateCandidate program fun candidate =>
      { candidate with proofPresent := true }),
    ("candidate cache fact", mutateCandidate program fun candidate =>
      { candidate with cache := none }),
    ("fold phase", mutateFold program fun fold => { fold with phase := .pre }),
    ("fold candidates empty", mutateFold program fun fold =>
      { fold with candidates := #[] }),
    ("fold candidates duplicated", mutateFold program fun fold => {
      fold with candidates := #[fold.candidates[0]!, fold.candidates[0]!] }),
    ("fold output fingerprint", mutateFold program fun fold =>
      { fold with finalOutputFingerprint := "mutated" }),
    ("fold disposition", mutateFold program fun fold =>
      { fold with finalDisposition := .visit }),
    ("fold proof fact", mutateFold program fun fold =>
      { fold with finalProofPresent := true }),
    ("fold cache fact", mutateFold program fun fold =>
      { fold with finalCache := none }),
    ("outer phase", mutateOuterEvent program fun event =>
      { event with phase := .pre }),
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

def checkGuardMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("guard modulus", mutateGuardCandidate program fun derivation =>
      { derivation with modulus := derivation.modulus + 1 }),
    ("guard source", mutateGuardCandidate program fun derivation =>
      { derivation with source := derivation.source + 1 }),
    ("guard normalized", mutateGuardCandidate program fun derivation =>
      { derivation with normalized := derivation.normalized + 1 }),
    ("guard modulus view value", mutateGuardCandidate program fun derivation =>
      { derivation with modulusView := mutateViewValue derivation.modulusView }),
    ("guard source view value", mutateGuardCandidate program fun derivation =>
      { derivation with sourceView := mutateViewValue derivation.sourceView }),
    ("guard modulus view path", mutateGuardCandidate program fun derivation =>
      { derivation with modulusView := mutateViewPath derivation.modulusView }),
    ("guard source view path", mutateGuardCandidate program fun derivation =>
      { derivation with sourceView := mutateViewPath derivation.sourceView }),
    ("guard modulus view fingerprint", mutateGuardCandidate program fun derivation =>
      { derivation with modulusView := mutateViewFingerprint derivation.modulusView }),
    ("guard source view fingerprint", mutateGuardCandidate program fun derivation =>
      { derivation with sourceView := mutateViewFingerprint derivation.sourceView }),
    ("guard modulus view metadata", mutateGuardCandidate program fun derivation =>
      { derivation with modulusView := mutateViewMetadata derivation.modulusView }),
    ("guard source view metadata", mutateGuardCandidate program fun derivation =>
      { derivation with sourceView := mutateViewMetadata derivation.sourceView }),
    ("guard modulus view constructor", mutateGuardCandidate program fun derivation =>
      { derivation with modulusView := mutateViewConstructor derivation.modulusView }),
    ("guard source view constructor", mutateGuardCandidate program fun derivation =>
      { derivation with sourceView := mutateViewConstructor derivation.sourceView })]
  let mut rejected ← checkCommonMutations expression ctx config program trace
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayFailure label expression ctx config mutation (some trace))
  return rejected

def checkModuloMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("modulo modulus", mutateModuloCandidate program fun derivation =>
      { derivation with modulus := derivation.modulus + 1 }),
    ("modulo source", mutateModuloCandidate program fun derivation =>
      { derivation with source := derivation.source + 1 }),
    ("modulo normalized", mutateModuloCandidate program fun derivation =>
      { derivation with normalized := derivation.normalized + 1 }),
    ("modulo modulus view value", mutateModuloCandidate program fun derivation =>
      { derivation with modulusView := mutateViewValue derivation.modulusView }),
    ("modulo source view value", mutateModuloCandidate program fun derivation =>
      { derivation with sourceView := mutateViewValue derivation.sourceView }),
    ("modulo modulus view path", mutateModuloCandidate program fun derivation =>
      { derivation with modulusView := mutateViewPath derivation.modulusView }),
    ("modulo source view path", mutateModuloCandidate program fun derivation =>
      { derivation with sourceView := mutateViewPath derivation.sourceView }),
    ("modulo modulus view fingerprint", mutateModuloCandidate program fun derivation =>
      { derivation with modulusView := mutateViewFingerprint derivation.modulusView }),
    ("modulo source view fingerprint", mutateModuloCandidate program fun derivation =>
      { derivation with sourceView := mutateViewFingerprint derivation.sourceView }),
    ("modulo modulus view metadata", mutateModuloCandidate program fun derivation =>
      { derivation with modulusView := mutateViewMetadata derivation.modulusView }),
    ("modulo source view metadata", mutateModuloCandidate program fun derivation =>
      { derivation with sourceView := mutateViewMetadata derivation.sourceView }),
    ("modulo modulus view constructor", mutateModuloCandidate program fun derivation =>
      { derivation with modulusView := mutateViewConstructor derivation.modulusView }),
    ("modulo source view constructor", mutateModuloCandidate program fun derivation =>
      { derivation with sourceView := mutateViewConstructor derivation.sourceView }),
    ("modulo instance path", mutateModuloCandidate program fun derivation =>
      { derivation with literalInstance := mutateInstancePath derivation.literalInstance }),
    ("modulo instance fingerprint", mutateModuloCandidate program fun derivation =>
      { derivation with literalInstance := mutateInstanceFingerprint derivation.literalInstance }),
    ("modulo instance term", mutateModuloCandidate program fun derivation =>
      { derivation with literalInstance := mutateInstanceTerm derivation.literalInstance }),
    ("modulo instance type fingerprint", mutateModuloCandidate program fun derivation =>
      { derivation with literalInstance :=
          mutateInstanceTypeFingerprint derivation.literalInstance })]
  let mut rejected ← checkCommonMutations expression ctx config program trace
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayFailure label expression ctx config mutation (some trace))
  return rejected

def expectObservationFailure (label : String) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat :=
  expectFailure label <| ExplicitLean.SimpEngine.Replay.validateSimprocObservations program trace

def checkObservationMutations (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let renamed : Simp.Engine.SimprocTrace := {
    observations := trace.observations.map fun observation =>
      if observation.name == `Fin.isValue then
        { observation with name := `FinLiteralFoldProbe.unexpected }
      else observation
  }
  let changed : Simp.Engine.SimprocTrace := {
    observations := trace.observations.map fun observation =>
      if observation.name == `Fin.isValue then
        { observation with inputFingerprint := "mutated" }
      else observation
  }
  let renamedRejected ← expectObservationFailure "renamed observation" program renamed
  let changedRejected ← expectObservationFailure "changed observation" program changed
  let missingFoldRejected ← expectObservationFailure "observation without fold"
    { program with events := #[] } trace
  return renamedRejected + changedRejected + missingFoldRejected

def checkSemanticShape (label : String) (candidate : Simp.Engine.SimprocCandidateEvent) :
    MetaM Unit := do
  if label == "reduce" || label == "dreduce" then
    let .canonicalValue (.finLiteralModulo derivation) := candidate.semantics
      | throwError "{label}: expected Fin modulo semantic constructor"
    unless derivation.modulus == 3 && derivation.source == 5 &&
        derivation.normalized == 2 do
      throwError "{label}: modulo scalar mismatch: {repr derivation}"
    unless derivation.literalInstance.term matches .input _ do
      throwError "{label}: modulo instance witness is not an input reference"
  else
    let .valueGuard (.finLiteralInRange derivation) := candidate.semantics
      | throwError "{label}: expected Fin in-range semantic constructor"
    unless derivation.modulus == 5 && derivation.source == 2 &&
        derivation.normalized == 2 do
      throwError "{label}: guard scalar mismatch: {repr derivation}"
  return ()

def checkDSimpMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("dphase candidate cache", mutateCandidate program fun candidate =>
      { candidate with cache := some true }),
    ("dphase fold cache", mutateFold program fun fold =>
      { fold with finalCache := some true }),
    ("dphase fold phase", mutateFold program fun fold =>
      { fold with phase := .dpost })]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayFailure label expression ctx config mutation (some trace))
  return rejected

def checkPaths (expression : Expr) : MetaM Unit := do
  let arguments := expression.getAppArgs
  unless arguments.size == 3 do
    throwError "arity-3 path fixture has {arguments.size} arguments"
  let paths : Array (Array ExprPathStep) := #[
    #[.appFunction, .appFunction, .appArgument],
    #[.appFunction, .appArgument],
    #[.appArgument]]
  for index in *...paths.size do
    let reference : InputSubtermRef := {
      path := paths[index]!
      fingerprint := ← exprFingerprintHash arguments[index]!
    }
    let resolved ← resolveInputSubterm expression reference
    unless Expr.equal resolved arguments[index]! do
      throwError "arity-3 argument path {index} resolved incorrectly"

def checkPreludeObservations (label : String) (observations : Array SimprocObservation)
    (requirePrelude : Bool := true) :
    MetaM Unit := do
  let continueNone := observations.filter fun observation =>
    observation.executed && observation.stepDisposition == .continueNone
  for observation in continueNone do
    unless isIgnorableWfContinueNone observation.name do
      throwError "{label}: unsupported ignored continue-none observation {observation.name}"
  if requirePrelude then
    for declaration in #[`Lean.Elab.WF.paramProj, `Lean.Elab.WF.paramMatcher,
        `Lean.Elab.WF.paramLet] do
      unless continueNone.any fun observation => observation.name == declaration do
        throwError "{label}: missing WF prelude observation {declaration}"
  unless observations.any fun observation =>
      observation.executed && observation.name == `Fin.isValue &&
        observation.stepDisposition == .done do
    throwError "{label}: missing terminating Fin.isValue observation"

def semanticEvents (program : Simp.Engine.Program) : Array Simp.Engine.Event :=
  program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false

def checkBasic (label : String) (expression : Expr) (ordinary : Bool) :
    MetaM (Simp.Engine.Program × Simp.Context × Simp.Engine.ReplayConfig × Nat) := do
  let builtins ← Simp.getSimprocs
  let methods ← if ordinary then
    pure { Simp.Engine.mkDefaultMethodsCore #[builtins] with
      dpre := fun _ => pure .continue
      dpost := fun _ => pure .continue }
  else
    pure (Simp.Engine.mkDefaultMethodsCore #[builtins])
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  if ordinary then
    let (recorded, recordedState, recording) ←
      Simp.Engine.mainCoreRecording expression ctx (methods := methods)
    checkPreludeObservations label recording.simprocs.observations
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations
      recording.program recording.simprocs
    unless recording.deferred.isNone do
      throwError "{label}: recording deferred: {repr recording.deferred}"
    let semantics := semanticEvents recording.program
    unless semantics.size == 1 do
      throwError "{label}: expected one semantic fold, got {semantics.size}"
    let some event := semantics[0]? | unreachable!
    let .semanticSimproc fold := event.operation | unreachable!
    unless fold.phase == .post && fold.candidates.size == 1 &&
        fold.finalDisposition == .done && !fold.finalProofPresent &&
        fold.finalCache == some true && event.stepDisposition == .done do
      throwError "{label}: ordinary fold summary mismatch: {repr fold}"
    let candidate := fold.candidates[0]!
    unless candidate.declaration == `Fin.isValue && candidate.procedureKind == .dsimp &&
        candidate.setIndex == 0 && candidate.disposition == .done &&
        candidate.registryPost &&
        !candidate.proofPresent && candidate.cache == some true &&
        candidate.numExtraArgs == 0 && candidate.extraArgumentFingerprints.isEmpty do
      throwError "{label}: ordinary candidate mismatch: {repr candidate}"
    checkSemanticShape label candidate
    let config ← Simp.Engine.replayConfigOfContext ctx
    let (replayed, replayedState) ←
      Simp.Engine.mainCoreReplay expression ctx config recording.program
    unless Expr.equal recorded.expr replayed.expr do
      throwError "{label}: ordinary replay expression mismatch"
    let recordedSummary ← summarizeState recordedState
    let replayedSummary ← summarizeState replayedState
    unless recordedSummary == replayedSummary do
      throwError "{label}: ordinary replay state mismatch: {repr recordedSummary} != {repr replayedSummary}"
    let semanticMutations ← if label == "keep" then
      checkGuardMutations expression ctx config recording.program recording.simprocs
    else if label == "reduce" then
      checkModuloMutations expression ctx config recording.program recording.simprocs
    else
      pure 0
    let observationMutations ← if label == "keep" then
      checkObservationMutations recording.program recording.simprocs
    else
      pure 0
    return (recording.program, ctx, config, semanticMutations + observationMutations)
  else
    let (recorded, recordedState, recording) ←
      Simp.Engine.dsimpMainCoreRecording expression ctx (methods := methods)
    checkPreludeObservations label recording.simprocs.observations false
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations
      recording.program recording.simprocs
    unless recording.deferred.isNone do
      throwError "{label}: recording deferred: {repr recording.deferred}"
    let semantics := semanticEvents recording.program
    unless semantics.size == 1 do
      throwError "{label}: expected one semantic fold, got {semantics.size}"
    let some event := semantics[0]? | unreachable!
    let .semanticSimproc fold := event.operation | unreachable!
    unless fold.phase == .dpre && fold.candidates.size == 1 &&
        fold.finalDisposition == .done && !fold.finalProofPresent &&
        fold.finalCache.isNone && event.stepDisposition == .done do
      throwError "{label}: dphase fold summary mismatch: {repr fold}"
    let candidate := fold.candidates[0]!
    unless candidate.declaration == `Fin.isValue && candidate.procedureKind == .dsimp &&
        candidate.setIndex == 0 && candidate.disposition == .done &&
        candidate.registryPost &&
        !candidate.proofPresent && candidate.cache.isNone &&
        candidate.numExtraArgs == 0 && candidate.extraArgumentFingerprints.isEmpty do
      throwError "{label}: dphase candidate mismatch: {repr candidate}"
    checkSemanticShape label candidate
    let config ← Simp.Engine.replayConfigOfContext ctx
    let (replayed, replayedState) ←
      Simp.Engine.dsimpMainCoreReplay expression ctx config recording.program
    unless Expr.equal recorded replayed do
      throwError "{label}: dphase replay expression mismatch"
    let recordedSummary ← summarizeState recordedState
    let replayedSummary ← summarizeState replayedState
    unless recordedSummary == replayedSummary do
      throwError "{label}: dphase replay state mismatch: {repr recordedSummary} != {repr replayedSummary}"
    let mutations ← if label == "dkeep" then
      checkDSimpMutations expression ctx config recording.program recording.simprocs
    else
      pure 0
    return (recording.program, ctx, config, mutations)

def expectSemanticNone (label : String) (result? : Option SemanticSimproc) : MetaM Unit := do
  unless result?.isNone do
    throwError "{label}: expected no Fin semantic derivation"

def checkSemanticHelpers : MetaM Unit := do
  let keep := standardFinLiteral 5 2
  let reduce := standardFinLiteral 3 5
  let some keepSem ← deriveFinLiteral? `Fin.isValue keep keep
    | throwError "standard in-range Fin literal was not recognized"
  let some reduceSem ← deriveFinLiteral? `Fin.isValue reduce
      (standardFinLiteralOfNatModulus 3 2)
    | throwError "standard reducing Fin literal was not recognized"
  for (label, semantics) in [("keep", keepSem), ("reduce", reduceSem)] do
    let decoded : SemanticSimproc ←
      match Lean.fromJson? (Lean.toJson semantics) with
      | .ok decoded => pure decoded
      | .error message => throwError "{label} Fin semantic JSON roundtrip failed: {message}"
    unless decoded == semantics do
      throwError "{label} Fin semantic JSON roundtrip changed the payload"
  let keepOutput ← match keepSem with
    | .valueGuard (.finLiteralInRange derivation) =>
        interpretFinLiteralInRange keep derivation
    | _ => throwError "in-range Fin semantic has the wrong constructor"
  unless Expr.equal keepOutput keep do
    throwError "in-range Fin interpretation changed the input"
  let reduceOutput ← match reduceSem with
    | .canonicalValue (.finLiteralModulo derivation) =>
        interpretFinLiteralModulo reduce derivation
    | _ => throwError "reducing Fin semantic has the wrong constructor"
  unless Expr.equal reduceOutput (standardFinLiteralOfNatModulus 3 2) do
    throwError "reducing Fin interpretation did not build the canonical output"
  let some customKeepSem ← deriveFinLiteral? `Fin.isValue customKeepLiteral customKeepLiteral
    | throwError "custom in-range Fin instance was not accepted"
  unless customKeepSem matches .valueGuard (.finLiteralInRange _) do
    throwError "custom in-range Fin instance used the wrong semantic constructor"
  let raw := rawFinLiteral 5 2
  let some rawSem ← deriveFinLiteral? `Fin.isValue raw raw
    | throwError "raw modulus Fin literal was not recognized"
  unless rawSem matches .valueGuard (.finLiteralInRange { modulusView := .raw .., .. }) do
    throwError "raw modulus Fin literal did not record a raw Nat view"
  let ofNat := standardFinLiteralOfNatModulus 5 2
  let some ofNatSem ← deriveFinLiteral? `Fin.isValue ofNat ofNat
    | throwError "OfNat modulus Fin literal was not recognized"
  unless ofNatSem matches .valueGuard (.finLiteralInRange { modulusView := .ofNat .., .. }) do
    throwError "OfNat modulus Fin literal did not record an OfNat Nat view"
  let metadataModulus := finLiteral (mkMData {} (mkNatLit 5)) (mkRawNatLit 2)
    (standardFinInstance 5 2)
  let metadataSource := finLiteral (mkNatLit 5) (mkMData {} (mkRawNatLit 2))
    (standardFinInstance 5 2)
  let some metadataModulusSem ← deriveFinLiteral? `Fin.isValue metadataModulus metadataModulus
    | throwError "metadata modulus Fin literal was not recognized"
  let some metadataSourceSem ← deriveFinLiteral? `Fin.isValue metadataSource metadataSource
    | throwError "metadata source Fin literal was not recognized"
  unless metadataSourceSem matches
      .valueGuard (.finLiteralInRange { sourceView := .raw _ _ 1, .. }) do
    throwError "metadata source depth was not recorded"
  let _ := metadataModulusSem
  let _ := rawSem
  let _ := ofNatSem
  let _ := customKeepSem

def checkUnsupported : MetaM Unit := do
  let standardKeep := standardFinLiteral 5 2
  let metadataTop := mkMData {} standardKeep
  let metadataType := mkApp3 (mkConst ``OfNat.ofNat [.zero])
    (mkMData {} (mkApp (mkConst ``Fin) (mkNatLit 5))) (mkRawNatLit 2)
    (standardFinInstance 5 2)
  let sourceOfNat := finLiteral (mkNatLit 5) (standardNatOfNat 2)
    (standardFinInstance 5 2)
  let zeroModulus := finLiteral (mkNatLit 0) (mkRawNatLit 0)
    (standardFinInstance 0 0)
  let wrongType := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat)
    (mkRawNatLit 2) (mkInstOfNatNat (mkRawNatLit 2))
  let mvar ← mkFreshExprMVar (mkConst ``Nat)
  let openInput := finLiteral (mkNatLit 5) mvar (standardFinInstance 5 2)
  let aliasType := aliasTypeLiteral
  let changedOutput := mkNatLit 0
  let wrongArity := mkApp2 (mkConst ``OfNat.ofNat [.zero])
    (mkApp (mkConst ``Fin) (mkNatLit 5)) (mkRawNatLit 2)
  let wrongName := mkApp3 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
  for (label, expression) in #[
      ("metadata top", metadataTop),
      ("metadata type", metadataType),
      ("source OfNat", sourceOfNat),
      ("zero modulus", zeroModulus),
      ("wrong type", wrongType),
      ("open input", openInput),
      ("reducible type alias", aliasType),
      ("wrong arity", wrongArity),
      ("wrong name", wrongName)] do
    expectSemanticNone label (← deriveFinLiteral? `Fin.isValue expression expression)
  expectSemanticNone "changed output"
    (← deriveFinLiteral? `Fin.isValue standardKeep changedOutput)
  let customReducingOutput := standardFinLiteralOfNatModulus 3 2
  expectSemanticNone "custom reducing instance with canonical output"
    (← deriveFinLiteral? `Fin.isValue customReduceLiteral customReducingOutput)
  expectSemanticNone "nonstandard modulus"
    (← deriveFinLiteral? `Fin.isValue nonstandardModulusLiteral nonstandardModulusLiteral)

def checkDeferred (label : String) (expression : Expr) : MetaM Unit := do
  let builtins ← Simp.getSimprocs
  let methods := { Simp.Engine.mkDefaultMethodsCore #[builtins] with
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (_, _, recording) ← Simp.Engine.mainCoreRecording expression ctx (methods := methods)
  checkPreludeObservations label recording.simprocs.observations
  unless recording.deferred.isSome do
    throwError "{label}: unsupported Fin recording was not deferred"
  unless semanticEvents recording.program |>.isEmpty do
    throwError "{label}: unsupported Fin recording emitted a semantic fold"

elab "check_fin_literal_fold" : tactic => withMainContext do
  let keep := standardFinLiteral 5 2
  let reduce := standardFinLiteral 3 5
  checkPaths keep
  checkSemanticHelpers
  checkUnsupported
  checkDeferred "custom reducing instance" customReduceLiteral
  checkDeferred "nonstandard modulus" nonstandardModulusLiteral
  let (_, _, _, ordinaryKeepMutations) ← checkBasic "keep" keep true
  let (_, _, _, ordinaryReduceMutations) ← checkBasic "reduce" reduce true
  let (_, _, _, dphaseKeepMutations) ← checkBasic "dkeep" keep false
  let (_, _, _, dphaseReduceMutations) ← checkBasic "dreduce" reduce false
  let _ ← checkBasic "raw" (rawFinLiteral 5 2) true
  let _ ← checkBasic "ofNat" (standardFinLiteralOfNatModulus 5 2) true
  let _ ← checkBasic "custom keep" customKeepLiteral true
  let mutations := ordinaryKeepMutations + ordinaryReduceMutations +
    dphaseKeepMutations + dphaseReduceMutations
  logInfo m!"FIN_LITERAL_FOLD_MUTATIONS rejected={mutations}"
  logInfo "FIN_LITERAL_FOLD ordinary,dphase,raw,ofNat,custom,unsupported: ok"

example : True := by
  check_fin_literal_fold
  trivial

end FinLiteralFoldProbe
