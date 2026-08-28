import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace CtorEqFoldProbe

open Lean.Meta.Simp.Engine

inductive IndexedPair (n : Nat) : Type where
  | left (value : Nat) : IndexedPair n
  | right (value : Nat) : IndexedPair n

inductive IndexedFamily : Nat → Type where
  | left (n : Nat) : IndexedFamily (n + 1)
  | right (n : Nat) : IndexedFamily (n + 1)

@[reducible] def natAliasZero : Nat := 0

@[reducible] def intAliasZero : Int := Int.ofNat 0

def natTypeAlias : Type := Nat

@[reducible] def badNatOfNatOne : OfNat Nat 1 := ⟨3⟩

def natRaw (value : Nat) : Expr := mkRawNatLit value

def natOfNat (value : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (natRaw value)
    (mkInstOfNatNat (natRaw value))

def intOfNatSyntax (value : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Int) (natRaw value)
    (mkApp (mkConst ``instOfNat) (natRaw value))

def badNatOfNat (value : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (natRaw value)
    (mkConst ``badNatOfNatOne)

def natAdd (lhs rhs : Expr) : Expr := mkApp2 (mkConst ``Nat.add) lhs rhs

def natAddClass (lhs rhs : Expr) : Expr :=
  mkApp4 (mkConst ``Add.add [.zero]) (mkConst ``Nat) Nat.mkInstAdd lhs rhs

def natHAddClass (lhs rhs : Expr) : Expr :=
  mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHAdd lhs rhs

def eqExpr (lhs rhs : Expr) : MetaM Expr := mkEq lhs rhs

def expectNoDerivation (label : String) (input : Expr) : MetaM Unit := do
  let some witness ← deriveConstructorDisjoint? `reduceCtorEq input (mkConst ``False)
    | pure ()
  throwError "{label}: unexpected constructor-disjoint derivation: {repr witness}"

def expectNoOutputDerivation (label : String) (input output : Expr) : MetaM Unit := do
  let some witness ← deriveConstructorDisjoint? `reduceCtorEq input output
    | pure ()
  throwError "{label}: unexpected constructor-disjoint derivation: {repr witness}"

def expectDerivation (label : String) (input : Expr) : MetaM ConstructorDisjointWitness := do
  let some witness ← deriveConstructorDisjoint? `reduceCtorEq input (mkConst ``False)
    | throwError "{label}: constructor-disjoint derivation was not recognized"
  let result ← interpretConstructorDisjoint input witness
  unless Expr.equal result.expr (mkConst ``False) && result.cache && result.proof?.isSome do
    throwError "{label}: interpreted result lacks False/proof/cache"
  let some proof := result.proof? | unreachable!
  let expectedType ← mkEq input (mkConst ``False)
  let actualType ← inferType proof
  unless ← isDefEq actualType expectedType do
    throwError "{label}: interpreted proof has wrong type: {actualType} != {expectedType}"
  pure witness

def optionNone : Expr := mkApp (mkConst ``Option.none [.zero]) (mkConst ``Nat)

def optionSome (value : Nat) : Expr :=
  mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Nat) (natRaw value)

def listNil : Expr := mkApp (mkConst ``List.nil [.zero]) (mkConst ``Nat)

def listCons (value : Nat) : Expr :=
  mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Nat) (natRaw value) listNil

def sumInl (value : Nat) : Expr :=
  mkApp3 (mkConst ``Sum.inl [.zero, .zero]) (mkConst ``Nat) (mkConst ``Bool) (natRaw value)

def sumInr (value : Bool) : Expr :=
  mkApp3 (mkConst ``Sum.inr [.zero, .zero]) (mkConst ``Nat) (mkConst ``Bool)
    (mkConst (if value then ``Bool.true else ``Bool.false))

def indexedLeft : Expr :=
  mkApp2 (mkConst ``IndexedPair.left) (natRaw 3) (natRaw 7)

def indexedRight : Expr :=
  mkApp2 (mkConst ``IndexedPair.right) (natRaw 3) (natRaw 7)

def indexedFamilyLeft : Expr :=
  mkApp (mkConst ``IndexedFamily.left) (natRaw 3)

def indexedFamilyRight : Expr :=
  mkApp (mkConst ``IndexedFamily.right) (natRaw 3)

def intOfNat (value : Nat) : Expr := mkApp (mkConst ``Int.ofNat) (natRaw value)

def intNegSucc (value : Nat) : Expr := mkApp (mkConst ``Int.negSucc) (natRaw value)

def finMk (modulus value : Nat) : MetaM Expr := do
  let partialApplication := mkApp2 (mkConst ``Fin.mk) (natRaw modulus) (natRaw value)
  let type ← inferType partialApplication
  let .forallE _ proofType _ _ := type
    | throwError "Fin.mk did not expose its proof argument"
  let proof ← mkSorry proofType true
  pure (mkApp partialApplication proof)

def finLiteral (modulus value : Nat) : Expr :=
  let modulusExpr := natOfNat modulus
  let inst := mkApp3 (mkConst ``Fin.instOfNat) modulusExpr
    (mkApp (mkConst ``Nat.instNeZeroSucc) (natOfNat (modulus - 1))) (natRaw value)
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkApp (mkConst ``Fin) modulusExpr)
    (natRaw value) inst

def checkDirectViews : MetaM Unit := do
  let _ ← expectDerivation "Bool.false/true" (← eqExpr (mkConst ``Bool.false) (mkConst ``Bool.true))
  let _ ← expectDerivation "Option.none/some" (← eqExpr optionNone (optionSome 1))
  let _ ← expectDerivation "List.nil/cons" (← eqExpr listNil (listCons 1))
  let _ ← expectDerivation "Sum.inl/inr" (← eqExpr (sumInl 1) (sumInr true))
  let _ ← expectDerivation "indexed parameterized constructors"
    (← eqExpr indexedLeft indexedRight)
  let _ ← expectDerivation "indexed constructors"
    (← eqExpr indexedFamilyLeft indexedFamilyRight)
  let _ ← expectDerivation "Int.ofNat/negSucc"
    (← eqExpr (intOfNat 0) (intNegSucc 0))
  let _ ← expectDerivation "Nat.zero/successor" (← eqExpr (mkConst ``Nat.zero) (mkApp (mkConst ``Nat.succ) (natRaw 0)))
  let _ ← expectDerivation "Nat.zero/OfNat positive" (← eqExpr (mkConst ``Nat.zero) (natOfNat 1))
  let rawNatWitness ← expectDerivation "Nat raw zero/positive" (← eqExpr (natRaw 0) (natRaw 1))
  unless rawNatWitness.lhs.origin matches .natLiteral (.raw _ 0 _) do
    throwError "raw Nat zero was not recorded as a Nat literal view"
  let metadataNatWitness ← expectDerivation "Nat metadata literal/positive"
    (← eqExpr (mkMData {} (natRaw 0)) (natRaw 1))
  unless metadataNatWitness.lhs.origin matches .natLiteral (.raw _ 0 1) do
    throwError "top-level metadata Nat literal was not recorded with depth 1"
  let _ ← expectDerivation "Nat.zero/succ offset" (← eqExpr (mkConst ``Nat.zero)
    (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)))
  let succWitness ← expectDerivation "Nat.succ offset origin" (← eqExpr (mkConst ``Nat.zero)
    (mkApp (mkConst ``Nat.succ) (natRaw 0)))
  unless succWitness.rhs.origin matches .natOffset (.succ (.base _)) 1 do
    throwError "direct Nat.succ was not encoded as a positive offset"
  let _ ← expectDerivation "Nat.zero/direct add offset" (← eqExpr (mkConst ``Nat.zero)
    (natAdd (mkConst ``Nat.zero) (natRaw 1)))
  let _ ← expectDerivation "Nat.zero/Add.add offset" (← eqExpr (mkConst ``Nat.zero)
    (natAddClass (mkConst ``Nat.zero) (natRaw 1)))
  let _ ← expectDerivation "Nat.zero/HAdd.hAdd offset" (← eqExpr (mkConst ``Nat.zero)
    (natHAddClass (mkConst ``Nat.zero) (natRaw 1)))
  let nested := natAdd (mkConst ``Nat.zero) (natAdd (natRaw 1) (natRaw 1))
  let witness ← expectDerivation "Nat offset >1 with NatEvalTrace rhs" (← eqExpr (mkConst ``Nat.zero) nested)
  match witness.rhs.origin with
  | .natOffset trace offset =>
      unless offset == 2 do throwError "nested Nat offset did not record offset 2"
      unless trace matches .add .natAdd none (.base _) (.binary .natAdd none (.raw 1) (.raw 1) 2) do
        throwError "nested Nat offset trace did not retain rhs NatEvalTrace"
  | origin => throwError "nested Nat offset has unexpected origin: {repr origin}"
  expectNoDerivation "same constructor" (← eqExpr (optionSome 1) (optionSome 2))
  expectNoDerivation "Nat offset zero" (← eqExpr (mkConst ``Nat.zero)
    (natAdd (mkConst ``Nat.zero) (natRaw 0)))
  expectNoDerivation "Nat reducible alias" (← eqExpr (mkConst ``natAliasZero)
    (mkApp (mkConst ``Nat.succ) (natRaw 0)))
  expectNoDerivation "Int reducible alias" (← eqExpr (mkConst ``intAliasZero)
    (intNegSucc 0))
  expectNoDerivation "metadata generic constructor" (← eqExpr (mkMData {} optionNone)
    (optionSome 1))
  expectNoDerivation "Nat unsupported OfNat instance" (← eqExpr (mkConst ``Nat.zero)
    (badNatOfNat 1))
  expectNoDerivation "Int OfNat syntax" (← eqExpr (intOfNatSyntax 0) (intNegSucc 0))
  expectNoDerivation "Fin OfNat syntax" (← eqExpr (finLiteral 5 0) (finLiteral 5 1))
  let directFinA ← finMk 5 0
  let directFinB ← finMk 5 1
  expectNoDerivation "same direct Fin.mk constructor" (← eqExpr directFinA directFinB)
  let aliasedTypeEq := mkApp3 (mkConst ``Eq [.zero]) (mkConst ``natTypeAlias)
    (mkConst ``Nat.zero) (mkApp (mkConst ``Nat.succ) (natRaw 0))
  expectNoDerivation "non-direct type alias" aliasedTypeEq
  let metadataEq := mkMData {} (← eqExpr (mkConst ``Bool.false) (mkConst ``Bool.true))
  expectNoDerivation "outer metadata" metadataEq
  let openOperand ← mkFreshExprMVar (mkConst ``Nat)
  expectNoDerivation "open operand" (← eqExpr openOperand (mkConst ``Nat.zero))
  let optionType ← inferType optionNone
  let assignedOperand ← mkFreshExprMVar optionType
  assignedOperand.mvarId!.assign optionNone
  expectNoDerivation "assigned constructor operand" (← eqExpr assignedOperand (optionSome 1))
  expectNoOutputDerivation "wrong procedure output"
    (← eqExpr (mkConst ``Bool.false) (mkConst ``Bool.true)) (mkConst ``True)
  let malformedEq := mkApp2 (mkConst ``Eq [.zero]) (mkConst ``Nat) (mkConst ``Nat.zero)
  expectNoDerivation "malformed Eq arity" malformedEq
  pure ()

def semanticEvents (program : Simp.Engine.Program) : Array Simp.Engine.Event :=
  program.events.filter fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false

def sortStrings (values : List String) : List String :=
  values.toArray.qsort (· < ·) |>.toList

def listFingerprint (values : List String) : String :=
  String.intercalate "," (sortStrings values)

def resultFingerprint (result : Simp.Result) : MetaM String := do
  let expression ← exprFingerprintHash result.expr
  let proof ← result.proof?.mapM exprFingerprintHash
  pure s!"{expression}|{proof}|{result.cache}"

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
  pure s!"used={listFingerprint used};tried={listFingerprint tried};congr={listFingerprint congr};badKeys={listFingerprint badKeys}"

structure StateSummary where
  numSteps : Nat
  cache : String
  dsimpCache : String
  usedTheorems : String
  diagnostics : String
  deriving BEq, Repr

def summarizeState (state : Simp.State) : MetaM StateSummary := do
  pure {
    numSteps := state.numSteps
    cache := ← cacheFingerprint state.cache
    dsimpCache := ← dsimpCacheFingerprint state.dsimpCache
    usedTheorems := listFingerprint (state.usedTheorems.toArray.toList.map reprStr)
    diagnostics := ← diagnosticsFingerprint state.diag
  }

def checkStateParity (label : String) (recorded replayed : Simp.State) : MetaM Unit := do
  let recordedSummary ← summarizeState recorded
  let replayedSummary ← summarizeState replayed
  unless recordedSummary == replayedSummary do
    throwError "{label}: replay state summary mismatch: {repr recordedSummary} != {repr replayedSummary}"

def checkProgramJson (label : String) (program : Simp.Engine.Program) : MetaM Unit := do
  let decoded : Simp.Engine.Program ←
    match Lean.fromJson? (Lean.toJson program) with
    | .ok decoded => pure decoded
    | .error message => throwError "{label}: program JSON roundtrip failed: {message}"
  unless decoded == program do
    throwError "{label}: program JSON roundtrip changed the payload"

def checkRecorded (label : String) (expression : Expr) : MetaM
    (Simp.Engine.Program × Simp.Context × Simp.Engine.ReplayConfig ×
      Simp.Engine.SimprocTrace) := do
  let builtins ← Simp.getSimprocs
  let methods := { Simp.Engine.mkDefaultMethodsCore #[builtins] with
    dpre := fun _ => pure .continue
    dpost := fun _ => pure .continue }
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (recorded, recordedState, recording) ←
    Simp.Engine.mainCoreRecording expression ctx (methods := methods)
  unless recording.deferred.isNone do
    throwError "{label}: recording deferred: {repr recording.deferred}"
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  let events := semanticEvents recording.program
  unless events.size == 1 do
    throwError "{label}: expected one semantic fold, got {events.size}"
  let some event := events[0]? | unreachable!
  let .semanticSimproc fold := event.operation | unreachable!
  unless fold.phase == .post && fold.candidates.size == 1 &&
      fold.finalDisposition == .done && fold.finalProofPresent &&
      fold.finalCache == some true && event.stepDisposition == .done do
    throwError "{label}: fold summary mismatch"
  let candidate := fold.candidates[0]!
  unless candidate.declaration == `reduceCtorEq && candidate.procedureKind == .simp &&
      candidate.setIndex == 0 && candidate.registryPost && candidate.disposition == .done &&
      candidate.proofPresent && candidate.cache == some true &&
      candidate.numExtraArgs == 0 && candidate.extraArgumentFingerprints.isEmpty do
    throwError "{label}: candidate protocol mismatch"
  unless candidate.semantics matches .constructorDisjoint _ do
    throwError "{label}: candidate does not contain constructor semantics"
  unless recorded.expr.isFalse && recorded.proof?.isSome && recorded.cache do
    throwError "{label}: recording did not return False with proof/cache"
  let some recordedProof := recorded.proof? | unreachable!
  let proofType ← inferType recordedProof
  let expectedProofType ← mkEq expression (mkConst ``False)
  unless ← isDefEq proofType expectedProofType do
    throwError "{label}: recorded proof has wrong type"
  checkProgramJson label recording.program
  let config ← Simp.Engine.replayConfigOfContext ctx
  let (replayed, replayedState) ←
    Simp.Engine.mainCoreReplay expression ctx config recording.program
  unless Expr.equal recorded.expr replayed.expr && recorded.cache == replayed.cache do
    throwError "{label}: replay result expression/cache mismatch"
  let some replayedProof := replayed.proof? | throwError "{label}: replay proof missing"
  unless Expr.equal recordedProof replayedProof do
    throwError "{label}: replay proof expression mismatch"
  checkStateParity label recordedState replayedState
  pure (recording.program, ctx, config, recording.simprocs)

def checkRecordedOrigins (label : String) (program : Simp.Engine.Program)
    (check : ConstructorDisjointWitness → Bool) : MetaM Unit := do
  let events := semanticEvents program
  let some event := events[0]? | throwError "{label}: missing semantic fold"
  let .semanticSimproc fold := event.operation | unreachable!
  let some candidate := fold.candidates[0]? | throwError "{label}: missing semantic candidate"
  let .constructorDisjoint witness := candidate.semantics
    | throwError "{label}: semantic candidate is not constructor-disjoint"
  unless check witness do
    throwError "{label}: recorded constructor origins do not match"

def checkDPhaseNoConstructor (expression : Expr) : MetaM Unit := do
  let builtins ← Simp.getSimprocs
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let (recorded, recordedState, recording) ←
    Simp.Engine.dsimpMainCoreRecording expression ctx
      (methods := Simp.Engine.mkDefaultMethodsCore #[builtins])
  unless semanticEvents recording.program |>.isEmpty do
    throwError "dphase unexpectedly recorded constructor semantics"
  ExplicitLean.SimpEngine.Replay.validateSimprocObservations
    recording.program recording.simprocs
  let config ← Simp.Engine.replayConfigOfContext ctx
  let (replayed, replayedState) ←
    Simp.Engine.dsimpMainCoreReplay expression ctx config recording.program
  unless Expr.equal recorded replayed do
    throwError "dphase replay changed constructor test expression"
  checkStateParity "dphase constructor-free replay" recordedState replayedState

def checkOffsetRecordingDeferred : MetaM Unit := do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let expression ← eqExpr (mkConst ``Nat.zero)
      (mkApp (mkConst ``Nat.succ) (mkApp (mkConst ``Nat.succ) n))
    let builtins ← Simp.getSimprocs
    let methods := { Simp.Engine.mkDefaultMethodsCore #[builtins] with
      dpre := fun _ => pure .continue
      dpost := fun _ => pure .continue }
    let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
    let (_, _, recording) ←
      Simp.Engine.mainCoreRecording expression ctx (methods := methods)
    unless recording.deferred == some (.simproc `Nat.reduceSucc .post) do
      throwError "symbolic Nat offset: unexpected recording boundary {repr recording.deferred}"

def mutateInstancePath (witness : InstanceWitness) : InstanceWitness :=
  match witness.term with
  | .input reference =>
      { witness with term := .input { reference with path := #[] } }
  | _ => { witness with term := .literal (.nat 0) }

def mutateInstanceFingerprint (witness : InstanceWitness) : InstanceWitness :=
  match witness.term with
  | .input reference =>
      { witness with term := .input { reference with fingerprint := "mutated" } }
  | _ => { witness with typeFingerprint := "mutated" }

def mutateInstanceTypeFingerprint (witness : InstanceWitness) : InstanceWitness :=
  { witness with typeFingerprint := "mutated" }

def mutateInstanceTerm (witness : InstanceWitness) : InstanceWitness :=
  { witness with term := .literal (.nat 0) }

def mutateEvalTraceRaw : NatEvalTrace → NatEvalTrace
  | .raw value => .raw (value + 1)
  | .metadata body => .metadata (mutateEvalTraceRaw body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceRaw body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceRaw body) result
  | .succ body result => .succ (mutateEvalTraceRaw body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateEvalTraceRaw lhs) (mutateEvalTraceRaw rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceRaw base) (mutateEvalTraceRaw exponent)
        threshold result

def mutateEvalTraceMetadata : NatEvalTrace → NatEvalTrace
  | .metadata _ => .metadata (.raw 0)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceMetadata body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceMetadata body) result
  | .succ body result => .succ (mutateEvalTraceMetadata body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateEvalTraceMetadata lhs) (mutateEvalTraceMetadata rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceMetadata base) (mutateEvalTraceMetadata exponent)
        threshold result
  | trace => trace

def mutateEvalTraceOfNat : NatEvalTrace → NatEvalTrace
  | .ofNat witness body result => .ofNat witness body (result + 1)
  | .metadata body => .metadata (mutateEvalTraceOfNat body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceOfNat body)
  | .succ body result => .succ (mutateEvalTraceOfNat body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateEvalTraceOfNat lhs) (mutateEvalTraceOfNat rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceOfNat base) (mutateEvalTraceOfNat exponent)
        threshold result
  | trace => trace

def mutateEvalTraceSucc : NatEvalTrace → NatEvalTrace
  | .succ body result => .succ (.raw 0) result
  | .metadata body => .metadata (mutateEvalTraceSucc body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceSucc body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceSucc body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateEvalTraceSucc lhs) (mutateEvalTraceSucc rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceSucc base) (mutateEvalTraceSucc exponent)
        threshold result
  | trace => trace

def mutateEvalTraceBinaryOperator : NatEvalTrace → NatEvalTrace
  | .binary _ witness lhs rhs result => .binary .natSub witness lhs rhs result
  | .metadata body => .metadata (mutateEvalTraceBinaryOperator body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceBinaryOperator body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceBinaryOperator body) result
  | .succ body result => .succ (mutateEvalTraceBinaryOperator body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceBinaryOperator base)
        (mutateEvalTraceBinaryOperator exponent) threshold result
  | trace => trace

def mutateEvalTraceBinaryWitness : NatEvalTrace → NatEvalTrace
  | .binary operator none lhs rhs result => .binary operator (some default) lhs rhs result
  | .binary operator (some witness) lhs rhs result => .binary operator none lhs rhs result
  | .metadata body => .metadata (mutateEvalTraceBinaryWitness body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceBinaryWitness body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceBinaryWitness body) result
  | .succ body result => .succ (mutateEvalTraceBinaryWitness body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceBinaryWitness base)
        (mutateEvalTraceBinaryWitness exponent) threshold result
  | trace => trace

def mutateEvalTraceBinaryWitnessPath : NatEvalTrace → NatEvalTrace
  | .binary operator (some witness) lhs rhs result =>
      .binary operator (some (mutateInstancePath witness)) lhs rhs result
  | .binary operator none lhs rhs result =>
      .binary operator (some (mutateInstancePath default)) lhs rhs result
  | .metadata body => .metadata (mutateEvalTraceBinaryWitnessPath body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceBinaryWitnessPath body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceBinaryWitnessPath body) result
  | .succ body result => .succ (mutateEvalTraceBinaryWitnessPath body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceBinaryWitnessPath base)
        (mutateEvalTraceBinaryWitnessPath exponent) threshold result
  | trace => trace

def mutateEvalTraceBinaryWitnessFingerprint : NatEvalTrace → NatEvalTrace
  | .binary operator (some witness) lhs rhs result =>
      .binary operator (some (mutateInstanceFingerprint witness)) lhs rhs result
  | .binary operator none lhs rhs result =>
      .binary operator (some (mutateInstanceFingerprint default)) lhs rhs result
  | .metadata body => .metadata (mutateEvalTraceBinaryWitnessFingerprint body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceBinaryWitnessFingerprint body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceBinaryWitnessFingerprint body) result
  | .succ body result => .succ (mutateEvalTraceBinaryWitnessFingerprint body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceBinaryWitnessFingerprint base)
        (mutateEvalTraceBinaryWitnessFingerprint exponent) threshold result
  | trace => trace

def mutateEvalTraceBinaryWitnessType : NatEvalTrace → NatEvalTrace
  | .binary operator (some witness) lhs rhs result =>
      .binary operator (some (mutateInstanceTypeFingerprint witness)) lhs rhs result
  | .binary operator none lhs rhs result =>
      .binary operator (some (mutateInstanceTypeFingerprint default)) lhs rhs result
  | .metadata body => .metadata (mutateEvalTraceBinaryWitnessType body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceBinaryWitnessType body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceBinaryWitnessType body) result
  | .succ body result => .succ (mutateEvalTraceBinaryWitnessType body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceBinaryWitnessType base)
        (mutateEvalTraceBinaryWitnessType exponent) threshold result
  | trace => trace

def mutateEvalTraceBinaryWitnessTerm : NatEvalTrace → NatEvalTrace
  | .binary operator (some witness) lhs rhs result =>
      .binary operator (some (mutateInstanceTerm witness)) lhs rhs result
  | .binary operator none lhs rhs result =>
      .binary operator (some (mutateInstanceTerm default)) lhs rhs result
  | .metadata body => .metadata (mutateEvalTraceBinaryWitnessTerm body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceBinaryWitnessTerm body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceBinaryWitnessTerm body) result
  | .succ body result => .succ (mutateEvalTraceBinaryWitnessTerm body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceBinaryWitnessTerm base)
        (mutateEvalTraceBinaryWitnessTerm exponent) threshold result
  | trace => trace

def mutateEvalTraceBinaryOperands : NatEvalTrace → NatEvalTrace
  | .binary operator witness lhs rhs result => .binary operator witness rhs lhs result
  | .metadata body => .metadata (mutateEvalTraceBinaryOperands body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceBinaryOperands body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceBinaryOperands body) result
  | .succ body result => .succ (mutateEvalTraceBinaryOperands body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceBinaryOperands base)
        (mutateEvalTraceBinaryOperands exponent) threshold result
  | trace => trace

def mutateEvalTraceBinaryResult : NatEvalTrace → NatEvalTrace
  | .binary operator witness lhs rhs result => .binary operator witness lhs rhs (result + 1)
  | .metadata body => .metadata (mutateEvalTraceBinaryResult body)
  | .zero => .zero
  | .assigned fingerprint value body => .assigned fingerprint value (mutateEvalTraceBinaryResult body)
  | .ofNat witness body result => .ofNat witness (mutateEvalTraceBinaryResult body) result
  | .succ body result => .succ (mutateEvalTraceBinaryResult body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateEvalTraceBinaryResult base)
        (mutateEvalTraceBinaryResult exponent) threshold result
  | trace => trace

def mutateOffsetBasePath : NatOffsetTrace → NatOffsetTrace
  | .base reference => .base { reference with path := #[] }
  | .succ trace => .succ (mutateOffsetBasePath trace)
  | .add operator instance? lhs rhs =>
      .add operator instance? (mutateOffsetBasePath lhs) (mutateEvalTraceRaw rhs)

def mutateOffsetBaseFingerprint : NatOffsetTrace → NatOffsetTrace
  | .base reference => .base { reference with fingerprint := "mutated" }
  | .succ trace => .succ (mutateOffsetBaseFingerprint trace)
  | .add operator instance? lhs rhs =>
      .add operator instance? (mutateOffsetBaseFingerprint lhs) rhs

def mutateOffsetOperator : NatOffsetTrace → NatOffsetTrace
  | .add _ instance? lhs rhs => .add .natAdd instance? lhs rhs
  | .succ trace => .succ (mutateOffsetOperator trace)
  | trace => trace

def mutateOffsetInstance : NatOffsetTrace → NatOffsetTrace
  | .add operator (some witness) lhs rhs =>
      .add operator (some (mutateInstancePath witness)) lhs rhs
  | .add operator none lhs rhs => .add operator (some (mutateInstancePath default)) lhs rhs
  | .succ trace => .succ (mutateOffsetInstance trace)
  | trace => trace

def mutateOffsetLhs : NatOffsetTrace → NatOffsetTrace
  | .add operator instance? lhs rhs => .add operator instance? (.succ lhs) rhs
  | .succ trace => .succ (mutateOffsetLhs trace)
  | trace => trace

def mutateOffsetRhs : NatOffsetTrace → NatOffsetTrace
  | .add operator instance? lhs rhs => .add operator instance? lhs (mutateEvalTraceRaw rhs)
  | .succ trace => .succ (mutateOffsetRhs trace)
  | trace => trace

def mutateOffsetEvalTrace (mutate : NatEvalTrace → NatEvalTrace) : NatOffsetTrace → NatOffsetTrace
  | .add operator instance? lhs rhs => .add operator instance? lhs (mutate rhs)
  | .succ trace => .succ (mutateOffsetEvalTrace mutate trace)
  | trace => trace

def mutateOffsetSucc : NatOffsetTrace → NatOffsetTrace
  | .succ _ => .succ (.base default)
  | .add operator instance? lhs rhs => .add operator instance? (mutateOffsetSucc lhs) rhs
  | trace => trace

def mutateOffsetTraceShape : NatOffsetTrace → NatOffsetTrace
  | .add operator instance? lhs rhs => .succ (.base default)
  | .succ _ => .base default
  | trace => trace

def mutateViewOperandPath (view : ConstructorView) : ConstructorView :=
  { view with operand := { view.operand with path := #[] } }

def mutateViewOperandFingerprint (view : ConstructorView) : ConstructorView :=
  { view with operand := { view.operand with fingerprint := "mutated" } }

def mutateViewConstructor (view : ConstructorView) : ConstructorView :=
  { view with constructor := `Bool.false }

def mutateViewInductive (view : ConstructorView) : ConstructorView :=
  { view with inductiveName := `Bool }

def mutateViewIndex (view : ConstructorView) : ConstructorView :=
  { view with constructorIndex := view.constructorIndex + 1 }

def mutateImmediateArgumentPath (view : ConstructorView) : ConstructorView :=
  match view.origin with
  | .immediate arguments =>
      { view with origin := .immediate (arguments.map fun reference =>
          { reference with path := #[] }) }
  | origin => { view with origin := origin }

def mutateImmediateArgumentFingerprint (view : ConstructorView) : ConstructorView :=
  match view.origin with
  | .immediate arguments =>
      { view with origin := .immediate (arguments.map fun reference =>
          { reference with fingerprint := "mutated" }) }
  | origin => { view with origin := origin }

def mutateViewOrigin (view : ConstructorView) : ConstructorView :=
  match view.origin with
  | .immediate _ => { view with origin := .natOffset (.base view.operand) 1 }
  | .natLiteral value => { view with origin := .immediate #[] }
  | .natOffset trace offset => { view with origin := .natLiteral default }

def mutateConstructorWitness (witness : ConstructorDisjointWitness)
    (mutate : ConstructorDisjointWitness → ConstructorDisjointWitness) :
    ConstructorDisjointWitness := mutate witness

def expectInterpretFailure (label : String) (input : Expr)
    (witness : ConstructorDisjointWitness) : MetaM Nat := do
  let saved ← Meta.saveState
  let succeeded ← try
    let _ ← interpretConstructorDisjoint input witness
    pure true
  catch _ => pure false
  saved.restore
  unless !succeeded do
    throwError "{label}: witness mutation was accepted"
  pure 1

def mutateNatValueReferencePath : NatValueView → NatValueView
  | .raw reference value depth => .raw { reference with path := #[] } value depth
  | .ofNat reference value depth witness =>
      .ofNat { reference with path := #[] } value depth witness

def mutateNatValueReferenceFingerprint : NatValueView → NatValueView
  | .raw reference value depth => .raw { reference with fingerprint := "mutated" } value depth
  | .ofNat reference value depth witness =>
      .ofNat { reference with fingerprint := "mutated" } value depth witness

def mutateNatValueValue : NatValueView → NatValueView
  | .raw reference value depth => .raw reference (value + 1) depth
  | .ofNat reference value depth witness => .ofNat reference (value + 1) depth witness

def mutateNatValueMetadata : NatValueView → NatValueView
  | .raw reference value depth => .raw reference value (depth + 1)
  | .ofNat reference value depth witness => .ofNat reference value (depth + 1) witness

def mutateNatValueInstancePath : NatValueView → NatValueView
  | .raw reference value depth => .ofNat reference value depth default
  | .ofNat reference value depth witness =>
      .ofNat reference value depth (mutateInstancePath witness)

def mutateNatValueInstanceFingerprint : NatValueView → NatValueView
  | .raw reference value depth => .ofNat reference value depth default
  | .ofNat reference value depth witness =>
      .ofNat reference value depth (mutateInstanceFingerprint witness)

def mutateNatValueInstanceType : NatValueView → NatValueView
  | .raw reference value depth => .ofNat reference value depth default
  | .ofNat reference value depth witness =>
      .ofNat reference value depth (mutateInstanceTypeFingerprint witness)

def mutateNatValueInstanceTerm : NatValueView → NatValueView
  | .raw reference value depth => .ofNat reference value depth default
  | .ofNat reference value depth witness =>
      .ofNat reference value depth (mutateInstanceTerm witness)

def mutateOffsetView (view : ConstructorView)
    (mutate : NatOffsetTrace → NatOffsetTrace) : ConstructorView :=
  match view.origin with
  | .natOffset trace offset => { view with origin := .natOffset (mutate trace) offset }
  | origin => { view with origin := origin }

def mutateOffsetViewValue (view : ConstructorView) : ConstructorView :=
  match view.origin with
  | .natOffset trace offset => { view with origin := .natOffset trace (offset + 1) }
  | origin => { view with origin := origin }

def mutateLiteralView (view : ConstructorView)
    (mutate : NatValueView → NatValueView) : ConstructorView :=
  match view.origin with
  | .natLiteral value => { view with origin := .natLiteral (mutate value) }
  | origin => { view with origin := origin }

def mutateCandidate (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocCandidateEvent → Simp.Engine.SimprocCandidateEvent) :
    Simp.Engine.Program :=
  match Array.findIdx? (fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false) program.events with
  | none => program
  | some eventIndex =>
      match program.events[eventIndex]? with
      | some event =>
          match event.operation with
          | .semanticSimproc fold =>
              let fold := { fold with candidates := fold.candidates.set! 0 (mutate fold.candidates[0]!) }
              { program with events := program.events.set! eventIndex {
                  event with operation := .semanticSimproc fold } }
          | _ => program
      | none => program

def mutateFold (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocFold → Simp.Engine.SimprocFold) :
    Simp.Engine.Program :=
  match Array.findIdx? (fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false) program.events with
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

def mutateOuterEvent (program : Simp.Engine.Program)
    (mutate : Simp.Engine.Event → Simp.Engine.Event) : Simp.Engine.Program :=
  match Array.findIdx? (fun event =>
    match event.operation with
    | .semanticSimproc _ => true
    | _ => false) program.events with
  | none => program
  | some eventIndex =>
      match program.events[eventIndex]? with
      | some event => { program with events := program.events.set! eventIndex (mutate event) }
      | none => program

def mutateConstructorCandidate (program : Simp.Engine.Program)
    (mutate : ConstructorDisjointWitness → ConstructorDisjointWitness) :
    Simp.Engine.Program :=
  mutateCandidate program fun candidate =>
    match candidate.semantics with
    | .constructorDisjoint witness =>
        { candidate with semantics := .constructorDisjoint (mutate witness) }
    | _ => candidate

def expectReplayFailure (label : String) (expression : Expr) (ctx : Simp.Context)
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

def checkReplayMutations (expression : Expr) (ctx : Simp.Context)
    (config : Simp.Engine.ReplayConfig) (program : Simp.Engine.Program)
    (trace : Simp.Engine.SimprocTrace) : MetaM Nat := do
  let mutations : Array (String × Simp.Engine.Program) := #[
    ("candidate declaration", mutateCandidate program fun candidate =>
      { candidate with declaration := `Nat.reduceAdd }),
    ("candidate procedure kind", mutateCandidate program fun candidate =>
      { candidate with procedureKind := .dsimp }),
    ("candidate set index", mutateCandidate program fun candidate =>
      { candidate with setIndex := 1 }),
    ("candidate registry provenance", mutateCandidate program fun candidate =>
      { candidate with registryPost := false }),
    ("candidate input fingerprint", mutateCandidate program fun candidate =>
      { candidate with inputFingerprint := "mutated" }),
    ("candidate peeled input fingerprint", mutateCandidate program fun candidate =>
      { candidate with peeledInputFingerprint := "mutated" }),
    ("candidate extra argument fingerprint", mutateCandidate program fun candidate =>
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
      { candidate with proofPresent := false }),
    ("candidate cache fact", mutateCandidate program fun candidate =>
      { candidate with cache := none }),
    ("candidate semantic witness", mutateConstructorCandidate program fun witness =>
      { witness with inductiveName := `Nat }),
    ("fold phase", mutateFold program fun fold => { fold with phase := .pre }),
    ("fold candidates empty", mutateFold program fun fold => { fold with candidates := #[] }),
    ("fold candidates duplicated", mutateFold program fun fold => {
      fold with candidates := #[fold.candidates[0]!, fold.candidates[0]!] }),
    ("fold output fingerprint", mutateFold program fun fold =>
      { fold with finalOutputFingerprint := "mutated" }),
    ("fold disposition", mutateFold program fun fold =>
      { fold with finalDisposition := .visit }),
    ("fold proof fact", mutateFold program fun fold =>
      { fold with finalProofPresent := false }),
    ("fold cache fact", mutateFold program fun fold =>
      { fold with finalCache := none }),
    ("outer phase", mutateOuterEvent program fun event => { event with phase := .pre }),
    ("outer input fingerprint", mutateOuterEvent program fun event =>
      { event with inputFingerprint := "mutated" }),
    ("outer output fingerprint", mutateOuterEvent program fun event =>
      { event with outputFingerprint := "mutated" }),
    ("outer path", mutateOuterEvent program fun event =>
      { event with path := { steps := #[] } }),
    ("outer disposition", mutateOuterEvent program fun event =>
      { event with stepDisposition := .visit }),
    ("outer invocation ordinal", mutateOuterEvent program fun event =>
      { event with invocationOrdinal := event.invocationOrdinal + 1 }),
    ("outer operation", mutateOuterEvent program fun event =>
      { event with operation := .builtin .decideTrue })
  ]
  let mut rejected := 0
  for (label, mutation) in mutations do
    rejected := rejected + (← expectReplayFailure label expression ctx config mutation trace)
  pure rejected

def checkWitnessMutations : MetaM Nat := do
  let directInput ← eqExpr optionNone (optionSome 1)
  let directWitness ← expectDerivation "mutation direct witness" directInput
  let literalInput ← eqExpr (mkConst ``Nat.zero) (natOfNat 1)
  let literalWitness ← expectDerivation "mutation literal witness" literalInput
  let succInput ← eqExpr (mkConst ``Nat.zero)
    (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero))
  let succWitness ← expectDerivation "mutation successor offset witness" succInput
  let inner := natAddClass (natRaw 0) (natRaw 2)
  let nested := natHAddClass (mkConst ``Nat.zero) inner
  let nestedInput ← eqExpr (mkConst ``Nat.zero) nested
  let nestedWitness ← expectDerivation "mutation nested offset witness" nestedInput
  match nestedWitness.rhs.origin with
  | .natOffset trace offset =>
      unless offset == 2 && trace matches
          .add .hAdd (some _) (.base _) (.binary .add (some _) (.raw 0) (.raw 2) 2) do
        throwError "nested offset witness did not retain overloaded recursive trace"
  | origin => throwError "nested offset witness has unexpected origin: {repr origin}"
  let metadataInput ← eqExpr (mkConst ``Nat.zero)
    (natAdd (mkConst ``Nat.zero) (mkMData {} (natRaw 1)))
  let metadataWitness ← expectDerivation "metadata rhs offset witness" metadataInput
  let ofNatInput ← eqExpr (mkConst ``Nat.zero)
    (natAdd (mkConst ``Nat.zero) (natOfNat 1))
  let ofNatWitness ← expectDerivation "OfNat rhs offset witness" ofNatInput
  let mut rejected := 0
  let directMutations : Array (String × ConstructorDisjointWitness) := #[
    ("type reference path", { directWitness with typeReference :=
      { directWitness.typeReference with path := #[] } }),
    ("type reference fingerprint", { directWitness with typeReference :=
      { directWitness.typeReference with fingerprint := "mutated" } }),
    ("witness inductive", { directWitness with inductiveName := `Bool }),
    ("lhs operand path", { directWitness with lhs := mutateViewOperandPath directWitness.lhs }),
    ("lhs operand fingerprint", { directWitness with lhs := mutateViewOperandFingerprint directWitness.lhs }),
    ("lhs constructor", { directWitness with lhs := mutateViewConstructor directWitness.lhs }),
    ("lhs inductive", { directWitness with lhs := mutateViewInductive directWitness.lhs }),
    ("lhs index", { directWitness with lhs := mutateViewIndex directWitness.lhs }),
    ("lhs origin", { directWitness with lhs := mutateViewOrigin directWitness.lhs }),
    ("rhs operand path", { directWitness with rhs := mutateViewOperandPath directWitness.rhs }),
    ("rhs operand fingerprint", { directWitness with rhs := mutateViewOperandFingerprint directWitness.rhs }),
    ("rhs constructor", { directWitness with rhs := mutateViewConstructor directWitness.rhs }),
    ("rhs inductive", { directWitness with rhs := mutateViewInductive directWitness.rhs }),
    ("rhs index", { directWitness with rhs := mutateViewIndex directWitness.rhs }),
    ("rhs origin", { directWitness with rhs := mutateViewOrigin directWitness.rhs }),
    ("rhs immediate argument path", { directWitness with rhs := mutateImmediateArgumentPath directWitness.rhs }),
    ("rhs immediate argument fingerprint", { directWitness with rhs := mutateImmediateArgumentFingerprint directWitness.rhs }),
    ("same constructor name", { directWitness with rhs :=
      { directWitness.rhs with constructor := directWitness.lhs.constructor } }),
    ("same constructor index", { directWitness with rhs :=
      { directWitness.rhs with constructorIndex := directWitness.lhs.constructorIndex } }),
    ("ctorIdx dependency", { directWitness with ctorIdxDeclaration := `Bool.ctorIdx }),
    ("noConfusion dependency", { directWitness with noConfusionDeclaration := `Bool.noConfusion }),
    ("eqFalse dependency", { directWitness with eqFalseDeclaration := `Bool.eq_false' })
  ]
  for (label, witness) in directMutations do
    rejected := rejected + (← expectInterpretFailure label directInput witness)
  let literalMutations : Array (String × ConstructorDisjointWitness) := #[
    ("literal reference path", { literalWitness with rhs := mutateLiteralView literalWitness.rhs mutateNatValueReferencePath }),
    ("literal reference fingerprint", { literalWitness with rhs := mutateLiteralView literalWitness.rhs mutateNatValueReferenceFingerprint }),
    ("literal value", { literalWitness with rhs := mutateLiteralView literalWitness.rhs mutateNatValueValue }),
    ("literal metadata depth", { literalWitness with rhs := mutateLiteralView literalWitness.rhs mutateNatValueMetadata }),
    ("literal instance path", { literalWitness with rhs := mutateLiteralView literalWitness.rhs mutateNatValueInstancePath }),
    ("literal instance fingerprint", { literalWitness with rhs := mutateLiteralView literalWitness.rhs mutateNatValueInstanceFingerprint }),
    ("literal instance type", { literalWitness with rhs := mutateLiteralView literalWitness.rhs mutateNatValueInstanceType }),
    ("literal instance term", { literalWitness with rhs := mutateLiteralView literalWitness.rhs mutateNatValueInstanceTerm })
  ]
  for (label, witness) in literalMutations do
    rejected := rejected + (← expectInterpretFailure label literalInput witness)
  let nestedMutations : Array (String × ConstructorDisjointWitness) := #[
    ("offset operator", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs mutateOffsetOperator }),
    ("offset instance", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs mutateOffsetInstance }),
    ("offset lhs trace", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs mutateOffsetLhs }),
    ("offset rhs trace", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs mutateOffsetRhs }),
    ("offset base path", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs mutateOffsetBasePath }),
    ("offset base fingerprint", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs mutateOffsetBaseFingerprint }),
    ("offset result", { nestedWitness with rhs := mutateOffsetViewValue nestedWitness.rhs }),
    ("offset origin", { nestedWitness with rhs := mutateViewOrigin nestedWitness.rhs }),
    ("offset binary operator", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceBinaryOperator) }),
    ("offset binary witness presence", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceBinaryWitness) }),
    ("offset binary witness path", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceBinaryWitnessPath) }),
    ("offset binary witness fingerprint", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceBinaryWitnessFingerprint) }),
    ("offset binary witness type", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceBinaryWitnessType) }),
    ("offset binary witness term", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceBinaryWitnessTerm) }),
    ("offset binary operands", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceBinaryOperands) }),
    ("offset binary result", { nestedWitness with rhs := mutateOffsetView nestedWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceBinaryResult) })
  ]
  for (label, witness) in nestedMutations do
    rejected := rejected + (← expectInterpretFailure label nestedInput witness)
  let succMutations : Array (String × ConstructorDisjointWitness) := #[
    ("offset successor trace", { succWitness with rhs := mutateOffsetView succWitness.rhs mutateOffsetSucc }),
    ("offset successor shape", { succWitness with rhs := mutateOffsetView succWitness.rhs mutateOffsetTraceShape })
  ]
  for (label, witness) in succMutations do
    rejected := rejected + (← expectInterpretFailure label succInput witness)
  let metadataMutations : Array (String × ConstructorDisjointWitness) := #[
    ("offset metadata trace", { metadataWitness with rhs := mutateOffsetView metadataWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceMetadata) })
  ]
  for (label, witness) in metadataMutations do
    rejected := rejected + (← expectInterpretFailure label metadataInput witness)
  let ofNatMutations : Array (String × ConstructorDisjointWitness) := #[
    ("offset OfNat trace", { ofNatWitness with rhs := mutateOffsetView ofNatWitness.rhs (mutateOffsetEvalTrace mutateEvalTraceOfNat) })
  ]
  for (label, witness) in ofNatMutations do
    rejected := rejected + (← expectInterpretFailure label ofNatInput witness)
  pure rejected

elab "check_ctor_eq" : tactic => withMainContext do
  checkDirectViews
  let witnessMutations ← checkWitnessMutations
  let boolExpression ← eqExpr (mkConst ``Bool.false) (mkConst ``Bool.true)
  let (program, ctx, config, trace) ← checkRecorded "ordinary Bool" boolExpression
  checkDPhaseNoConstructor boolExpression
  let literalExpression ← eqExpr (natRaw 0) (natRaw 1)
  let (literalProgram, _, _, _) ← checkRecorded "ordinary Nat literal" literalExpression
  checkRecordedOrigins "ordinary Nat literal" literalProgram fun witness =>
    witness.lhs.origin matches .natLiteral _ && witness.rhs.origin matches .natLiteral _
  checkOffsetRecordingDeferred
  let replayMutations ← checkReplayMutations boolExpression ctx config program trace
  logInfo m!"CTOR_EQ_DIRECT_MUTATIONS rejected={witnessMutations + replayMutations}"
  logInfo "CTOR_EQ_DIRECT ordinary,replay,proof,JSON: ok"

example : True := by
  check_ctor_eq
  trivial

end CtorEqFoldProbe
