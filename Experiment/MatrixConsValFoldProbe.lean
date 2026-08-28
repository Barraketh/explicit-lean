import Mathlib.Data.Fin.VecNotation
import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace MatrixConsValFoldProbe

open Lean.Meta.Simp.Engine

def finLiteral (modulus source : Nat) : Expr :=
  let modulusExpr := mkNatLit modulus
  let sourceExpr := mkRawNatLit source
  let inst := mkApp3 (mkConst ``Fin.instOfNat) modulusExpr
    (mkApp (mkConst ``Nat.instNeZeroSucc) (mkNatLit (modulus - 1))) sourceExpr
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkApp (mkConst ``Fin) modulusExpr)
    sourceExpr inst

def vecEmpty (α : Expr) : Expr := mkApp (mkConst ``Matrix.vecEmpty [.zero]) α

def vecCons (α : Expr) (n : Nat) (head tail index : Expr) : Expr :=
  mkApp5 (mkConst ``Matrix.vecCons [.zero]) α (mkNatLit n) head tail index

def finType (length : Expr) : Expr := mkApp (mkConst ``Fin) length

def finIndex (length : Expr) (value : Nat) : MetaM Expr := do
  let nonzero := mkApp (mkConst ``Nat.instNeZeroSucc) length.appArg!
  let literal := mkRawNatLit value
  let inst := mkApp3 (mkConst ``Fin.instOfNat) length nonzero literal
  pure <| mkApp3 (mkConst ``OfNat.ofNat [.zero]) (finType length) literal inst

def finIndexClosed (length value : Nat) : Expr :=
  let lengthExpr := mkNatLit length
  let literal := mkRawNatLit value
  let nonzero := mkApp (mkConst ``Nat.instNeZeroSucc) (mkNatLit (length - 1))
  let inst := mkApp3 (mkConst ``Fin.instOfNat) lengthExpr nonzero literal
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (finType lengthExpr) literal inst

def finNegativeClosed (length magnitude : Nat) : Expr :=
  let positive := finIndexClosed length magnitude
  mkApp3 (mkConst ``Neg.neg [.zero]) (finType (mkNatLit length))
    (mkConst ``Fin.neg) positive

def constantTail (length : Expr) (value : Nat) : Expr :=
  mkLambda `i BinderInfo.default (finType length) (mkRawNatLit value)

def constantTailExpression (length body : Expr) : Expr :=
  mkLambda `i BinderInfo.default (finType length) body

def natAddExpression (lhs rhs : Expr) : Expr :=
  mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHAdd lhs rhs

def vecConsWithTail (length : Expr) (head : Nat) (tailValue indexValue : Nat) : MetaM Expr := do
  let tail := constantTail length tailValue
  let index ← pure <| finIndexClosed 4 indexValue
  pure <| mkApp5 (mkConst ``Matrix.vecCons [.zero]) (mkConst ``Nat) length
    (mkRawNatLit head) tail index

@[reducible] def vectorRootAlias (v : Fin 5 → Nat) : Fin 5 → Nat := v

@[reducible] def vectorNestedAlias (v : Fin 4 → Nat) : Fin 4 → Nat := v

@[reducible] def vectorClosedLength : Nat := 3

@[reducible] def vectorOffsetLength (n : Nat) : Nat := Nat.succ n

def natSucc (expression : Expr) : Expr := mkApp (mkConst ``Nat.succ) expression

def vectorSpine (tailLength : Expr) (heads : Array Expr) (tail index : Expr) : Expr :=
  let rec go (length function : Expr) : List Expr → Expr
    | [] => mkApp function index
    | head :: rest =>
        go (natSucc length)
          (mkApp4 (mkConst ``Matrix.vecCons [.zero]) (mkConst ``Nat)
            length head function) rest
  go tailLength tail heads.reverse.toList

def vectorSpineClosed (tailLength : Nat) (heads : Array Expr)
    (tail index : Expr) : Expr :=
  let rec go (length : Nat) (function : Expr) : List Expr → Expr
    | [] => mkApp function index
    | head :: rest =>
        go (length + 1)
          (mkApp4 (mkConst ``Matrix.vecCons [.zero]) (mkConst ``Nat)
            (mkNatLit length) head function) rest
  go tailLength tail heads.reverse.toList

def vectorInputClosedWithIndex (heads : Array Nat) (tailLength : Nat)
    (tailValue : Nat) (index : Expr) : Expr :=
  let length := mkNatLit tailLength
  let tail := constantTail length tailValue
  vectorSpineClosed tailLength (heads.map mkRawNatLit) tail index

def vectorInputClosedExpression (heads : Array Nat) (tailLength : Nat)
    (tailBody index : Expr) : Expr :=
  let length := mkNatLit tailLength
  let tail := constantTailExpression length tailBody
  vectorSpineClosed tailLength (heads.map mkRawNatLit) tail index

def vectorInputClosedExpressions (heads : Array Expr) (tailLength : Nat)
    (tailBody index : Expr) : Expr :=
  let length := mkNatLit tailLength
  let tail := constantTailExpression length tailBody
  vectorSpineClosed tailLength heads tail index

def vectorInputClosed (heads : Array Nat) (tailLength : Nat)
    (tailValue indexValue : Nat) : Expr :=
  vectorInputClosedWithIndex heads tailLength tailValue
    (finIndexClosed 20 indexValue)

def vectorInputSymbolic (n : Expr) (heads : Array Nat)
    (tailValue indexValue : Nat) : Expr :=
  let tail := constantTail n tailValue
  vectorSpine n (heads.map mkRawNatLit) tail (finIndexClosed 20 indexValue)

def vectorInputAlias (tailValue indexValue : Nat) : Expr :=
  let length := mkNatLit 3
  let tail := constantTail length tailValue
  let base := vectorSpineClosed 3 #[mkRawNatLit 7, mkRawNatLit 8] tail
    (finIndexClosed 20 indexValue)
  mkApp (mkConst ``vectorRootAlias) base

def vectorInputNestedAlias (tailValue indexValue : Nat) : Expr :=
  let length := mkNatLit 3
  let tail := constantTail length tailValue
  let nested := mkApp4 (mkConst ``Matrix.vecCons [.zero]) (mkConst ``Nat)
      length (mkRawNatLit 8) tail
  let nestedAlias := mkApp (mkConst ``vectorNestedAlias) nested
  let root := mkApp4 (mkConst ``Matrix.vecCons [.zero]) (mkConst ``Nat)
      (mkNatLit 4) (mkRawNatLit 7) nestedAlias
  mkApp root (finIndexClosed 20 indexValue)

def vectorInputOffset (n : Expr) (heads : Array Nat)
    (tailValue indexValue : Nat) : Expr :=
  let length := mkApp (mkConst ``vectorOffsetLength) n
  let tail := constantTail length tailValue
  vectorSpine length (heads.map mkRawNatLit) tail (finIndexClosed 20 indexValue)

def resultShape (result : Simp.Result) : MetaM String := do
  let expr := result.expr
  let fingerprint ← exprFingerprintHash expr
  pure s!"{fingerprint}; {expr}"

def sortStrings (values : List String) : List String :=
  values.toArray.qsort (· < ·) |>.toList

def listFingerprint (values : List String) : String :=
  String.intercalate "," (sortStrings values)

def resultFingerprint (result : Simp.Result) : MetaM String := do
  let expression ← exprFingerprintHash result.expr
  let proof ← result.proof?.mapM exprFingerprintHash
  pure s!"{expression}|{proof}|{result.cache}"

def jsonRoundtrip {α : Type} [BEq α] [ToJson α] [FromJson α]
    (label : String) (value : α) : MetaM Unit := do
  let decoded ← match Lean.fromJson? (Lean.toJson value) with
    | .ok value => pure value
    | .error message => throwError "{label}: JSON decode failed: {message}"
  unless decoded == value do
    throwError "{label}: JSON roundtrip mismatch"

def cacheFingerprint (cache : Simp.Cache) : MetaM String := do
  let entries ← cache.toList.mapM fun (key, value) => do
    let keyFingerprint ← exprFingerprintHash key
    let valueFingerprint ← resultFingerprint value
    pure s!"{keyFingerprint}=>{valueFingerprint}"
  pure s!"stage₁={cache.stage₁};{listFingerprint entries}"

def dsimpCacheFingerprint (cache : ExprStructMap Expr) : MetaM String := do
  let entries ← cache.toList.mapM fun (key, value) => do
    let keyFingerprint ← exprFingerprintHash key.val
    let valueFingerprint ← exprFingerprintHash value
    pure s!"{keyFingerprint}=>{valueFingerprint}"
  pure (listFingerprint entries)

def congrExprFingerprint (expression : Expr) : String := toString expression

def congrTheoremFingerprint (theorem? : Option CongrTheorem) : String :=
  match theorem? with
  | none => "none"
  | some thm =>
      s!"{congrExprFingerprint thm.type}|{congrExprFingerprint thm.proof}|{reprStr thm.argKinds}"

def congrCacheFingerprint (cache : ExprMap (Option CongrTheorem)) : String :=
  let entries := cache.toList.map fun (key, value) =>
    s!"{congrExprFingerprint key}=>{congrTheoremFingerprint value}"
  listFingerprint entries

def theoremFingerprint (simpTheorem : SimpTheorem) : MetaM String := do
  let proof ← exprFingerprintHash simpTheorem.proof
  pure s!"keys={reprStr simpTheorem.keys}|levels={reprStr simpTheorem.levelParams}|proof={proof}|priority={simpTheorem.priority}|post={simpTheorem.post}|perm={simpTheorem.perm}|origin={reprStr simpTheorem.origin}|rfl={simpTheorem.rfl}|backwardRfl={simpTheorem.backwardRfl}"

def diagnosticsFingerprint (diagnostics : Simp.Diagnostics) : MetaM String := do
  let used := diagnostics.usedThmCounter.toList.map fun (origin, count) =>
    s!"{reprStr origin}=>{count}"
  let tried := diagnostics.triedThmCounter.toList.map fun (origin, count) =>
    s!"{reprStr origin}=>{count}"
  let congr := diagnostics.congrThmCounter.toList.map fun (name, count) =>
    s!"{name}=>{count}"
  let badKeys ← diagnostics.thmsWithBadKeys.toList.mapM theoremFingerprint
  pure <| s!"used={listFingerprint used};tried={listFingerprint tried};" ++
    s!"congr={listFingerprint congr};badKeys={listFingerprint badKeys}"

structure StateSummary where
  numSteps : Nat
  cache : String
  congrCache : String
  dsimpCache : String
  usedTheorems : String
  diagnostics : String
  deriving BEq, Repr

def summarizeState (state : Simp.State) : MetaM StateSummary := do
  pure {
    numSteps := state.numSteps
    cache := ← cacheFingerprint state.cache
    congrCache := congrCacheFingerprint state.congrCache
    dsimpCache := ← dsimpCacheFingerprint state.dsimpCache
    usedTheorems := listFingerprint (state.usedTheorems.toArray.toList.map reprStr)
    diagnostics := ← diagnosticsFingerprint state.diag
  }

def semanticEvents (program : Simp.Engine.Program) : Array Simp.Engine.Event :=
  program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false

def recordMatrix (expression : Expr) (ordinary : Bool) : MetaM
    (Simp.Result × Simp.State × Simp.Engine.Recording × Simp.Context × Simp.Engine.ReplayConfig) := do
  let builtins ← Simp.getSimprocs
  let methods ← if ordinary then
    pure { Simp.Engine.mkDefaultMethodsCore #[builtins] with
      dpre := fun _ => pure .continue
      dpost := fun _ => pure .continue }
  else
    pure (Simp.Engine.mkDefaultMethodsCore #[builtins])
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  if ordinary then
    let (result, state, recording) ←
      Simp.Engine.mainCoreRecording expression ctx (methods := methods)
    let config ← Simp.Engine.replayConfigOfContext ctx
    pure (result, state, recording, ctx, config)
  else
    let (result, state, recording) ←
      Simp.Engine.dsimpMainCoreRecording expression ctx (methods := methods)
    let config ← Simp.Engine.replayConfigOfContext ctx
    pure (({ expr := result } : Simp.Result), state, recording, ctx, config)

def referenceMatrix (expression : Expr) (ordinary : Bool) : MetaM
    (Simp.Result × Simp.State) := do
  let builtins ← Simp.getSimprocs
  let methods ← if ordinary then
    pure { Simp.Engine.mkDefaultMethodsCore #[builtins] with
      dpre := fun _ => pure .continue
      dpost := fun _ => pure .continue }
  else
    pure (Simp.Engine.mkDefaultMethodsCore #[builtins])
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  if ordinary then
    Simp.mainCore expression ctx (methods := methods.base)
  else
    let (result, state) ← Simp.dsimpMainCore expression ctx (methods := methods.base)
    pure (({ expr := result } : Simp.Result), state)

def recordMatrixWithSets (expression : Expr) (sets : Simp.SimprocsArray) : MetaM
    (Simp.Result × Simp.State × Simp.Engine.Recording × Simp.Context × Simp.Engine.ReplayConfig) := do
  let baseMethods := { Simp.mkDefaultMethodsCore #[] with
    pre := Simp.userPostSimprocs sets
    post := fun e => pure (.done { expr := e })
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }
  let methods := { Simp.Engine.mkDefaultMethodsCore #[] with
    pre := Simp.Engine.userPostSimprocsRecorded sets
    post := fun e => pure (.done { expr := e })
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue
    base := baseMethods }
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (result, state, recording) ←
    Simp.Engine.mainCoreRecording expression ctx (methods := methods)
  let config ← Simp.Engine.replayConfigOfContext ctx
  pure (result, state, recording, ctx, config)

def referenceMatrixWithSets (expression : Expr) (sets : Simp.SimprocsArray) : MetaM
    (Simp.Result × Simp.State) := do
  let methods := { Simp.mkDefaultMethodsCore #[] with
    pre := Simp.userPostSimprocs sets
    post := fun e => pure (.done { expr := e })
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  Simp.mainCore expression ctx (methods := methods)

def checkRecordedMatrix (label : String) (expression : Expr) (ordinary : Bool) : MetaM
    (Simp.Engine.Program × Simp.Context × Simp.Engine.ReplayConfig × Nat) := do
  let initialMeta ← Meta.saveState
  let (reference, referenceState) ← referenceMatrix expression ordinary
  initialMeta.restore
  let (recorded, recordedState, recording, ctx, config) ← recordMatrix expression ordinary
  unless Expr.equal reference.expr recorded.expr do
    throwError "{label}: reference/record result mismatch: {← resultShape reference} != {← resultShape recorded}"
  let referenceSummary ← summarizeState referenceState
  let recordedSummary ← summarizeState recordedState
  unless referenceSummary == recordedSummary do
    throwError "{label}: reference/record state mismatch: {repr referenceSummary} != {repr recordedSummary}"
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  let semantics := (semanticEvents recording.program).filter fun event =>
    match event.operation with
    | .semanticSimproc fold => fold.candidates.any fun candidate =>
        candidate.declaration == `Matrix.cons_val
    | _ => false
  unless semantics.size == 1 do
    throwError "{label}: expected exactly one Matrix semantic event, got {semantics.size}"
  let some event := semantics[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.candidates.size == 1 && fold.finalDisposition == .continueSome &&
      event.stepDisposition == .continueSome do
    throwError "{label}: wrong fold summary: {repr fold}"
  let candidate := fold.candidates[0]!
  match candidate.semantics with
  | .vectorLookup derivation =>
      jsonRoundtrip "{label}:vector-derivation-json" derivation
  | _ => throwError "{label}: Matrix candidate lacks vector semantics"
  jsonRoundtrip "{label}:simproc-trace-json" recording.simprocs
  unless candidate.declaration == `Matrix.cons_val && candidate.procedureKind == .dsimp &&
      candidate.setIndex == 0 && candidate.registryPost &&
      candidate.disposition == .continueSome && !candidate.proofPresent &&
      candidate.numExtraArgs == 0 && candidate.extraArgumentFingerprints.isEmpty do
    throwError "{label}: wrong candidate summary: {repr candidate}"
  if ordinary then
    unless candidate.cache == some true && fold.finalCache == some true do
      throwError "{label}: ordinary cache summary mismatch"
  else
    unless candidate.cache.isNone && fold.finalCache.isNone do
      throwError "{label}: dphase cache summary mismatch"
  let (replayed, replayedState) ← if ordinary then
    Simp.Engine.mainCoreReplay expression ctx config recording.program
  else
    let (result, state) ← Simp.Engine.dsimpMainCoreReplay expression ctx config recording.program
    pure (({ expr := result } : Simp.Result), state)
  unless Expr.equal recorded.expr replayed.expr do
    throwError "{label}: replay result mismatch: {← resultShape recorded} != {← resultShape replayed}"
  let recordedSummary ← summarizeState recordedState
  let replayedSummary ← summarizeState replayedState
  unless recordedSummary == replayedSummary do
    throwError "{label}: replay state mismatch: {repr recordedSummary} != {repr replayedSummary}"
  pure (recording.program, ctx, config, 0)

partial def matrixEventIndexFrom (events : Array Simp.Engine.Event) (index : Nat) :
    Option Nat :=
  if h : index < events.size then
    let event := events[index]'h
    match event.operation with
    | .semanticSimproc fold =>
        if fold.candidates.any fun candidate => candidate.declaration == `Matrix.cons_val then
          some index
        else
          matrixEventIndexFrom events (index + 1)
    | _ => matrixEventIndexFrom events (index + 1)
  else
    none

def matrixEventIndex (program : Simp.Engine.Program) : Option Nat :=
  matrixEventIndexFrom program.events 0

def mutateMatrixFold (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocFold → Simp.Engine.SimprocFold) :
    Simp.Engine.Program :=
  match matrixEventIndex program with
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

def mutateMatrixCandidate (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocCandidateEvent → Simp.Engine.SimprocCandidateEvent) :
    Simp.Engine.Program :=
  mutateMatrixFold program fun fold =>
    if h : fold.candidates.size > 0 then
      { fold with candidates := fold.candidates.set! 0 (mutate fold.candidates[0]!) }
    else
      fold

def mutateMatrixEvent (program : Simp.Engine.Program)
    (mutate : Simp.Engine.Event → Simp.Engine.Event) : Simp.Engine.Program :=
  match matrixEventIndex program with
  | none => program
  | some index =>
      if h : index < program.events.size then
        let event := program.events[index]'h
        { program with events := program.events.set index (mutate event) h }
      else
        program

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

def mutateObservation (trace : Simp.Engine.SimprocTrace)
    (mutate : SimprocObservation → SimprocObservation) :
    Simp.Engine.SimprocTrace :=
  { observations := trace.observations.map fun observation =>
      if observation.name == `Matrix.cons_val then mutate observation else observation }

def mutateWitnessInput (witness : VectorWhnfWitness) : VectorWhnfWitness :=
  { witness with inputFingerprint := "mutated" }

def mutateWitnessOutput (witness : VectorWhnfWitness) : VectorWhnfWitness :=
  { witness with outputFingerprint := "mutated" }

def mutateSpineRoot (spine : VectorSpine)
    (mutate : VectorWhnfWitness → VectorWhnfWitness) : VectorSpine :=
  { spine with root := { spine.root with whnf := mutate spine.root.whnf } }

def mutateSpineNested (spine : VectorSpine) : VectorSpine :=
  if h : spine.nested.size > 0 then
    let view := spine.nested[0]'h
    let updated := { view with whnf := mutateWitnessOutput view.whnf }
    { spine with nested := spine.nested.set 0 updated h }
  else
    { spine with root := { spine.root with arity := spine.root.arity + 1 } }

def mutateSpineStop (spine : VectorSpine) : VectorSpine :=
  { spine with stop := mutateWitnessOutput spine.stop }

def mutateIndexViewValue (view : VectorIndexView) : VectorIndexView :=
  { view with value := view.value + 1 }

def mutateIndexViewSign (view : VectorIndexView) : VectorIndexView :=
  { view with constructor := match view.constructor with
      | .positive => .negative
      | .negative => .positive }

def mutateIndexViewFingerprint (view : VectorIndexView) : VectorIndexView :=
  { view with wholeFingerprint := "mutated" }

def mutateTailLengthWhnf (length : VectorTailLength)
    (mutate : VectorWhnfWitness → VectorWhnfWitness) : VectorTailLength :=
  match length with
  | .closed witness value fingerprint => .closed (mutate witness) value fingerprint
  | .offset witness trace offset fingerprint => .offset (mutate witness) trace offset fingerprint
  | .symbolic witness original fingerprint =>
      .symbolic (mutate witness) original fingerprint

def mutateTailLengthBranch : VectorTailLength → VectorTailLength
  | .closed witness value _ =>
      .symbolic witness default "mutated"
  | .offset witness trace offset fingerprint =>
      .symbolic witness default fingerprint
  | .symbolic witness original fingerprint =>
      .closed witness 1 fingerprint

def mutateTailLengthValue : VectorTailLength → VectorTailLength
  | .closed witness value fingerprint => .closed witness (value + 1) fingerprint
  | .offset witness trace offset fingerprint => .offset witness trace (offset + 1) fingerprint
  | .symbolic witness original fingerprint => .symbolic witness original fingerprint

def mutateTailLengthFingerprint : VectorTailLength → VectorTailLength
  | .closed witness value _ => .closed witness value "mutated"
  | .offset witness trace offset _ => .offset witness trace offset "mutated"
  | .symbolic witness original _ => .symbolic witness original "mutated"

partial def mutateOffsetBaseFingerprint : NatOffsetTrace → NatOffsetTrace
  | .base reference => .base { reference with fingerprint := "mutated" }
  | .succ trace => .succ (mutateOffsetBaseFingerprint trace)
  | .add operator instance? lhs rhs =>
      .add operator instance? (mutateOffsetBaseFingerprint lhs) rhs

def mutateOffsetStructure : NatOffsetTrace → NatOffsetTrace
  | .base reference => .succ (.base reference)
  | .succ trace => trace
  | trace@(.add ..) => .succ trace

def mutateTailLengthOffsetTrace
    (mutate : NatOffsetTrace → NatOffsetTrace) : VectorTailLength → VectorTailLength
  | .offset witness trace offset fingerprint =>
      .offset witness (mutate trace) offset fingerprint
  | length => length

def mutateSelectionPrefix : VectorSelection → VectorSelection
  | .prefix index => .prefix (index + 1)
  | selection => selection

def mutateSelectionTail : VectorSelection → VectorSelection
  | .tail residual index typeFingerprint => .tail (residual + 1) index typeFingerprint
  | selection => selection

def mutateSelectionDependency : VectorSelection → VectorSelection
  | .tail residual index typeFingerprint =>
      .tail residual (.literal (.nat 0)) typeFingerprint
  | selection => selection

def mutateSelectionType : VectorSelection → VectorSelection
  | .tail residual index _ => .tail residual index "mutated"
  | selection => selection

def mutateDerivation (mutate : VectorLookupDerivation → VectorLookupDerivation)
    (program : Simp.Engine.Program) : Simp.Engine.Program :=
  mutateMatrixCandidate program fun candidate =>
    match candidate.semantics with
    | .vectorLookup derivation =>
        { candidate with semantics := .vectorLookup (mutate derivation) }
    | _ => candidate

def mutateVectorSpine (mutate : VectorSpine → VectorSpine)
    (program : Simp.Engine.Program) : Simp.Engine.Program :=
  mutateDerivation (fun derivation =>
    { derivation with spine := mutate derivation.spine }) program

def mutateVectorIndex (mutate : VectorIndexView → VectorIndexView)
    (program : Simp.Engine.Program) : Simp.Engine.Program :=
  mutateDerivation (fun derivation =>
    { derivation with indexView := mutate derivation.indexView }) program

def mutateVectorLength (mutate : VectorTailLength → VectorTailLength)
    (program : Simp.Engine.Program) : Simp.Engine.Program :=
  mutateDerivation (fun derivation =>
    { derivation with tailLength := mutate derivation.tailLength }) program

def mutateVectorSelection (mutate : VectorSelection → VectorSelection)
    (program : Simp.Engine.Program) : Simp.Engine.Program :=
  mutateDerivation (fun derivation =>
    { derivation with selection := mutate derivation.selection }) program

def checkReplayMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let candidateMutations : Array (String × Simp.Engine.Program) := #[
    ("spine root input witness", mutateVectorSpine (fun spine =>
      mutateSpineRoot spine mutateWitnessInput) program),
    ("spine root output witness", mutateVectorSpine (fun spine =>
      mutateSpineRoot spine mutateWitnessOutput) program),
    ("spine root arity", mutateVectorSpine (fun spine =>
      { spine with root := { spine.root with arity := spine.root.arity + 1 } }) program),
    ("spine nested witness", mutateVectorSpine mutateSpineNested program),
    ("spine stop witness", mutateVectorSpine mutateSpineStop program),
    ("index syntax value", mutateVectorIndex mutateIndexViewValue program),
    ("index syntax sign", mutateVectorIndex mutateIndexViewSign program),
    ("index syntax fingerprint", mutateVectorIndex mutateIndexViewFingerprint program),
    ("tail length witness", mutateVectorLength
      (fun length => mutateTailLengthWhnf length mutateWitnessOutput) program),
    ("tail length branch", mutateVectorLength mutateTailLengthBranch program),
    ("tail length value", mutateVectorLength mutateTailLengthValue program),
    ("tail length canonical fingerprint", mutateVectorLength mutateTailLengthFingerprint program),
    ("wrapped arithmetic", mutateDerivation (fun derivation =>
      { derivation with wrappedIndex := derivation.wrappedIndex + 1 }) program),
    ("prefix selection", mutateVectorSelection mutateSelectionPrefix program),
    ("candidate declaration", mutateMatrixCandidate program fun candidate =>
      { candidate with declaration := `Matrix.vecCons }),
    ("candidate procedure kind", mutateMatrixCandidate program fun candidate =>
      { candidate with procedureKind := .simp }),
    ("candidate set index", mutateMatrixCandidate program fun candidate =>
      { candidate with setIndex := candidate.setIndex + 1 }),
    ("candidate registry provenance", mutateMatrixCandidate program fun candidate =>
      { candidate with registryPost := false }),
    ("candidate input fingerprint", mutateMatrixCandidate program fun candidate =>
      { candidate with inputFingerprint := "mutated" }),
    ("candidate peeled input fingerprint", mutateMatrixCandidate program fun candidate =>
      { candidate with peeledInputFingerprint := "mutated" }),
    ("candidate procedure output fingerprint", mutateMatrixCandidate program fun candidate =>
      { candidate with procedureOutputFingerprint := "mutated" }),
    ("candidate output fingerprint", mutateMatrixCandidate program fun candidate =>
      { candidate with outputFingerprint := "mutated" }),
    ("candidate extra argument count", mutateMatrixCandidate program fun candidate =>
      { candidate with numExtraArgs := 1 }),
    ("candidate extra argument fingerprints", mutateMatrixCandidate program fun candidate =>
      { candidate with extraArgumentFingerprints := #["mutated"] }),
    ("candidate disposition", mutateMatrixCandidate program fun candidate =>
      { candidate with disposition := .done }),
    ("candidate proof fact", mutateMatrixCandidate program fun candidate =>
      { candidate with proofPresent := true }),
    ("candidate cache fact", mutateMatrixCandidate program fun candidate =>
      { candidate with cache := none }),
    ("fold phase", mutateMatrixFold program fun fold => { fold with phase := .pre }),
    ("fold candidates empty", mutateMatrixFold program fun fold =>
      { fold with candidates := #[] }),
    ("fold candidate duplication", mutateMatrixFold program fun fold => {
      fold with candidates := #[fold.candidates[0]!, fold.candidates[0]!] }),
    ("fold output fingerprint", mutateMatrixFold program fun fold =>
      { fold with finalOutputFingerprint := "mutated" }),
    ("fold disposition", mutateMatrixFold program fun fold =>
      { fold with finalDisposition := .done }),
    ("fold proof fact", mutateMatrixFold program fun fold =>
      { fold with finalProofPresent := true }),
    ("fold cache fact", mutateMatrixFold program fun fold =>
      { fold with finalCache := none }),
    ("outer input fingerprint", mutateMatrixEvent program fun event =>
      { event with inputFingerprint := "mutated" }),
    ("outer output fingerprint", mutateMatrixEvent program fun event =>
      { event with outputFingerprint := "mutated" }),
    ("outer disposition", mutateMatrixEvent program fun event =>
      { event with stepDisposition := .done }),
    ("outer phase", mutateMatrixEvent program fun event =>
      { event with phase := .pre }),
    ("outer invocation ordinal", mutateMatrixEvent program fun event =>
      { event with invocationOrdinal := event.invocationOrdinal + 1 }),
    ("outer operation", mutateMatrixEvent program fun event =>
      { event with operation := .builtin .decideTrue })]
  let mut rejected := 0
  for (label, mutation) in candidateMutations do
    rejected := rejected + (← expectReplayReject label expression ctx config mutation trace)
  pure rejected

def checkTailReplayMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("tail residual", mutateVectorSelection mutateSelectionTail program),
    ("tail dependency", mutateVectorSelection mutateSelectionDependency program),
    ("tail dependency type", mutateVectorSelection mutateSelectionType program)]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayReject label expression ctx config mutation trace)
  pure rejected

def checkOffsetReplayMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("offset base reference", mutateVectorLength
      (mutateTailLengthOffsetTrace mutateOffsetBaseFingerprint) program),
    ("offset trace structure", mutateVectorLength
      (mutateTailLengthOffsetTrace mutateOffsetStructure) program)]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayReject label expression ctx config mutation trace)
  pure rejected

def checkObservationMutations (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.SimprocTrace) := #[
    ("observation ordinal", mutateObservation trace fun observation =>
      { observation with phaseInvocationOrdinal := observation.phaseInvocationOrdinal + 1 }),
    ("observation set index", mutateObservation trace fun observation =>
      { observation with setIndex := observation.setIndex + 1 }),
    ("observation input fingerprint", mutateObservation trace fun observation =>
      { observation with inputFingerprint := "mutated" }),
    ("observation output fingerprint", mutateObservation trace fun observation =>
      { observation with outputFingerprint := "mutated" }),
    ("observation output size", mutateObservation trace fun observation =>
      { observation with outputSize := none }),
    ("observation disposition", mutateObservation trace fun observation =>
      { observation with stepDisposition := .done }),
    ("observation cache", mutateObservation trace fun observation =>
      { observation with cache := some false }),
    ("observation removed", {
      observations := trace.observations.filter fun observation =>
        observation.name != `Matrix.cons_val }),
    ("observation duplicated", {
      observations := trace.observations ++
        (trace.observations.filter fun observation => observation.name == `Matrix.cons_val) })]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectValidationReject label program mutation)
  pure rejected

def matrixNatAddPostSets : MetaM Simp.SimprocsArray := do
  let matrix ← ({} : Simp.Simprocs).add `Matrix.cons_val true
  let natAdd ← ({} : Simp.Simprocs).add `Nat.reduceAdd true
  pure #[matrix, natAdd]

def checkMultiCandidateBoundary : MetaM Nat := do
  let sets ← matrixNatAddPostSets
  let add := natAddExpression (mkRawNatLit 3) (mkRawNatLit 4)
  let input := vectorInputClosedExpressions #[add, mkRawNatLit 8] 3
    (mkRawNatLit 42) (finIndexClosed 20 0)
  let initialMeta ← Meta.saveState
  let (reference, referenceState) ← referenceMatrixWithSets input sets
  initialMeta.restore
  let (recorded, recordedState, recording, ctx, config) ←
    recordMatrixWithSets input sets
  unless Expr.equal reference.expr recorded.expr do
    throwError "multi-candidate: reference/record result mismatch"
  unless (← summarizeState referenceState) == (← summarizeState recordedState) do
    throwError "multi-candidate: reference/record state mismatch"
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  unless recording.deferred.isNone do
    throwError "multi-candidate: recording deferred: {repr recording.deferred}"
  let events := semanticEvents recording.program
  unless events.size == 1 do
    throwError "multi-candidate: expected one semantic event, got {events.size}"
  let some event := events[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == .pre && fold.candidates.size == 2 &&
      fold.finalDisposition == .done && event.stepDisposition == .done do
    throwError "multi-candidate: wrong fold summary: {repr fold}"
  let matrix := fold.candidates[0]!
  let natAdd := fold.candidates[1]!
  unless matrix.declaration == `Matrix.cons_val && matrix.setIndex == 0 &&
      matrix.registryPost && matrix.disposition == .continueSome &&
      natAdd.declaration == `Nat.reduceAdd && natAdd.setIndex == 1 &&
      natAdd.registryPost && natAdd.disposition == .done &&
      matrix.outputFingerprint == natAdd.inputFingerprint do
    throwError "multi-candidate: wrong ordered candidates: {repr fold.candidates}"
  match matrix.semantics, natAdd.semantics with
  | .vectorLookup _, .canonicalValue (.natBinary derivation) =>
      unless derivation.operator == .add do
        throwError "multi-candidate: terminal operation is not Nat addition"
  | _, _ => throwError "multi-candidate: wrong semantic operations"
  jsonRoundtrip "multi-candidate:fold-json" fold
  jsonRoundtrip "multi-candidate:trace-json" recording.simprocs
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay input ctx config recording.program
  unless Expr.equal replayed.expr recorded.expr do
    throwError "multi-candidate: replay result mismatch"
  unless (← summarizeState replayedState) == (← summarizeState recordedState) do
    throwError "multi-candidate: replay state mismatch"
  let swappedCandidates := mutateMatrixFold recording.program fun fold =>
    { fold with candidates := #[fold.candidates[1]!, fold.candidates[0]!] }
  let secondSetZero := mutateMatrixFold recording.program fun fold =>
    let candidate := { fold.candidates[1]! with setIndex := 0 }
    { fold with candidates := fold.candidates.set! 1 candidate }
  let reversedTrace : Simp.Engine.SimprocTrace := {
    observations := recording.simprocs.observations.reverse }
  let mut rejected ← expectReplayReject "multi-candidate order" input ctx config
    swappedCandidates recording.simprocs
  rejected := rejected + (← expectReplayReject "multi-candidate second set" input ctx config
    secondSetZero recording.simprocs)
  rejected := rejected + (← expectValidationReject "multi-candidate observation order"
    recording.program reversedTrace)
  pure rejected

def expectVectorDerivationNone (label : String) (input output : Expr) : MetaM Unit := do
  let derivation? ← deriveVectorLookup `Matrix.cons_val input output
  unless derivation?.isNone do
    throwError "{label}: unsupported Matrix.cons_val shape was recognized"

def assertDeferredMatrixContinue (label : String) (expression : Expr) : MetaM Unit := do
  let (_result, _state, recording, _ctx, _config) ← recordMatrix expression true
  let matrixObservations := recording.simprocs.observations.filter fun observation =>
    observation.name == `Matrix.cons_val
  unless !matrixObservations.isEmpty do
    throwError "{label}: expected a Matrix.cons_val observation"
  for observation in matrixObservations do
    unless observation.executed && observation.stepDisposition == .continueNone &&
        !observation.outputChanged && observation.outputSize.isNone do
      throwError "{label}: Matrix.cons_val did not commit continue-none: {repr observation}"
  match recording.deferred with
  | some (.simproc name .post) =>
      unless name == `Matrix.cons_val do
        throwError "{label}: deferred for unexpected simproc {name}: {repr recording.deferred}"
  | some reason => throwError "{label}: unexpected deferred reason {repr reason}"
  | none => throwError "{label}: unsupported Matrix.cons_val call was not deferred"
  unless !(semanticEvents recording.program).any fun event =>
      match event.operation with
      | .semanticSimproc fold => fold.candidates.any fun candidate =>
          candidate.declaration == `Matrix.cons_val
      | _ => false do
    throwError "{label}: unsupported Matrix.cons_val call emitted a semantic event"

def sourceMatrixProcedureOutput (expression : Expr) : MetaM Expr := do
  let builtins ← Simp.getSimprocs
  let candidates ← builtins.post.getMatchWithExtra expression
  let some (entry, numExtraArgs) := candidates.find? fun (entry, _) =>
      entry.declName == `Matrix.cons_val
    | throwError "source Matrix procedure is not registered for fixture"
  unless numExtraArgs == 0 do
    throwError "source Matrix fixture unexpectedly has extra arguments"
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (step, _state) ← Lean.Meta.Simp.SimpM.run ctx {} {} <| entry.tryD numExtraArgs expression
  match step with
  | .continue (some output) => pure output
  | step => throwError "source Matrix procedure did not return continue-some: {repr step}"

def checkUnsupportedVectorShapes : MetaM Unit := do
  let rawInput := mkRawNatLit 0
  expectVectorDerivationNone "unsupported root shape" rawInput rawInput
  withLocalDeclD `i (finType (mkNatLit 20)) fun i => do
    let wrongSyntax := vectorInputClosedWithIndex #[7, 8] 3 42 i
    assertDeferredMatrixContinue "wrong index syntax" wrongSyntax
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let symbolicOutOfBounds := vectorInputSymbolic n #[7, 8] 42 3
    assertDeferredMatrixContinue "symbolic out-of-known-prefix index" symbolicOutOfBounds
    let offsetOutOfBounds := vectorInputOffset n #[7, 8] 42 3
    assertDeferredMatrixContinue "offset out-of-known-prefix index" offsetOutOfBounds
    let length := mkApp (mkConst ``vectorOffsetLength) n
    let tail := constantTail length 42
    let input := vectorSpine length #[mkRawNatLit 7, mkRawNatLit 8] tail
      (finIndexClosed 20 2)
    let sourceOutput ← sourceMatrixProcedureOutput input
    let unrepresentable := mkLambda `i BinderInfo.default (finType length) (mkRawNatLit 0)
    let .app actualTail _actualIndex := sourceOutput
      | throwError "source Matrix representation-boundary fixture did not select tail"
    let malformedOutput := mkApp actualTail unrepresentable
    expectVectorDerivationNone "malformed unrepresentable tail dependency descriptor"
      input malformedOutput
    let saved ← Meta.saveState
    let openIndex ← mkFreshExprMVar (finType length)
    expectVectorDerivationNone "open tail dependency" input (mkApp actualTail openIndex)
    saved.restore

elab "check_matrix_cons_val_shape" : tactic => withMainContext do
  checkUnsupportedVectorShapes
  let prefixInput := vectorInputClosed #[7, 8] 3 42 6
  let (prefixProgram, prefixCtx, prefixConfig, _) ←
    checkRecordedMatrix "closed-positive-wrap" prefixInput true
  let (_, _, prefixRecording, _, _) ← recordMatrix prefixInput true
  let mut rejected ← checkReplayMutations prefixInput prefixCtx prefixConfig prefixProgram
    prefixRecording.simprocs
  rejected := rejected + (← checkObservationMutations prefixProgram prefixRecording.simprocs)
  let _ ← checkRecordedMatrix "closed-dphase" prefixInput false
  let negativeInput := vectorInputClosedWithIndex #[7, 8] 3 42 (finNegativeClosed 20 1)
  let _ ← checkRecordedMatrix "closed-negative-wrap" negativeInput true
  let _ ← checkRecordedMatrix "closed-root-alias" (vectorInputAlias 42 1) true
  let _ ← checkRecordedMatrix "closed-nested-alias" (vectorInputNestedAlias 42 2) true
  let closedTail := vectorInputClosed #[7, 8] 3 42 2
  let (closedTailProgram, closedTailCtx, closedTailConfig, _) ←
    checkRecordedMatrix "closed-tail-selection" closedTail true
  let (_, _, closedTailRecording, _, _) ← recordMatrix closedTail true
  rejected := rejected + (← checkTailReplayMutations closedTail closedTailCtx
    closedTailConfig closedTailProgram closedTailRecording.simprocs)
  let offsetRejected ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    let mut localRejected := 0
    let _ ← checkRecordedMatrix "symbolic-variadic-prefix" (vectorInputSymbolic n #[7, 8] 42 1) true
    let _ ← checkRecordedMatrix "offset-variadic-prefix" (vectorInputOffset n #[7, 8] 42 1) true
    let offsetTail := vectorInputOffset n #[7, 8] 42 2
    let (offsetTailProgram, offsetTailCtx, offsetTailConfig, _) ←
      checkRecordedMatrix "offset-variadic-tail" offsetTail true
    let (_, _, offsetTailRecording, _, _) ← recordMatrix offsetTail true
    localRejected := localRejected + (← checkTailReplayMutations offsetTail offsetTailCtx
      offsetTailConfig offsetTailProgram offsetTailRecording.simprocs)
    localRejected := localRejected + (← checkOffsetReplayMutations offsetTail offsetTailCtx
      offsetTailConfig offsetTailProgram offsetTailRecording.simprocs)
    pure localRejected
  rejected := rejected + offsetRejected
  rejected := rejected + (← checkMultiCandidateBoundary)
  unless rejected == 60 do
    throwError "unexpected Matrix.cons_val mutation count: {rejected}"
  logInfo m!"SIMP_ENGINE_MATRIX_CONS_VAL_MUTATIONS rejected={rejected}"
  logInfo "SIMP_ENGINE_MATRIX_CONS_VAL ordinary,dphase,aliases,closed,offset,symbolic: ok"

example : True := by
  check_matrix_cons_val_shape
  trivial

end MatrixConsValFoldProbe
