import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

namespace FinMkCanonicalFoldProbe

open Lean.Meta.Simp.Engine

theorem twoLtFive : (2 : Nat) < 5 := by decide

theorem twoLtThree : (2 : Nat) < 3 := by decide

@[reducible] def badNatOfNatFive : OfNat Nat 5 := ⟨7⟩

@[reducible] def badNatOfNatTwo : OfNat Nat 2 := ⟨7⟩

@[reducible] def badNatAdd : Add Nat := ⟨fun a b => a + b + 1⟩

@[reducible] def badNatHAdd : HAdd Nat Nat Nat := ⟨fun a b => a + b + 1⟩

@[reducible] def badNatPow : NatPow Nat := ⟨fun _ _ => 0⟩

@[reducible] def badNatHPow : HPow Nat Nat Nat := ⟨fun _ _ => 0⟩

def natAliasFive : Nat := 5

def finMkAlias : {n : Nat} → (v : Nat) → v < n → Fin n := Fin.mk

def natRaw (value : Nat) : Expr := mkRawNatLit value

def natOfNat (value : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit value)
    (mkInstOfNatNat (mkRawNatLit value))

def finLiteral (modulus source : Nat) : Expr :=
  let modulusExpr := natOfNat modulus
  let sourceExpr := mkRawNatLit source
  let inst := mkApp3 (mkConst ``Fin.instOfNat) modulusExpr
    (mkApp (mkConst ``Nat.instNeZeroSucc) (natOfNat (modulus - 1))) sourceExpr
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkApp (mkConst ``Fin) modulusExpr)
    sourceExpr inst

def finMkExpression (modulus value : Expr) : MetaM Expr := do
  let partialApplication := mkApp2 (mkConst ``Fin.mk) modulus value
  let partialType ← inferType partialApplication
  let .forallE _ proofType _ _ := partialType
    | throwError "Fin.mk partial application did not expose a proof argument"
  let proof ← mkSorry proofType true
  pure <| mkApp partialApplication proof

def finMkExpressionWithProofMVar (modulus value : Expr) : MetaM Expr := do
  let partialApplication := mkApp2 (mkConst ``Fin.mk) modulus value
  let partialType ← inferType partialApplication
  let .forallE _ proofType _ _ := partialType
    | throwError "Fin.mk partial application did not expose a proof argument"
  let proof ← mkFreshExprMVar proofType
  pure <| mkApp partialApplication proof

def natBinaryExpression (operator : NatEvalBinaryOperator) (lhs rhs : Expr) : Expr :=
  match operator with
  | .natAdd => mkApp2 (mkConst ``Nat.add) lhs rhs
  | .add => mkApp4 (mkConst ``Add.add [.zero]) (mkConst ``Nat) Nat.mkInstAdd lhs rhs
  | .hAdd => mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHAdd lhs rhs
  | .natSub => mkApp2 (mkConst ``Nat.sub) lhs rhs
  | .sub => mkApp4 (mkConst ``Sub.sub [.zero]) (mkConst ``Nat) Nat.mkInstSub lhs rhs
  | .hSub => mkApp6 (mkConst ``HSub.hSub [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHSub lhs rhs
  | .natMul => mkApp2 (mkConst ``Nat.mul) lhs rhs
  | .mul => mkApp4 (mkConst ``Mul.mul [.zero]) (mkConst ``Nat) Nat.mkInstMul lhs rhs
  | .hMul => mkApp6 (mkConst ``HMul.hMul [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHMul lhs rhs
  | .natDiv => mkApp2 (mkConst ``Nat.div) lhs rhs
  | .div => mkApp4 (mkConst ``Div.div [.zero]) (mkConst ``Nat) Nat.mkInstDiv lhs rhs
  | .hDiv => mkApp6 (mkConst ``HDiv.hDiv [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHDiv lhs rhs
  | .natMod => mkApp2 (mkConst ``Nat.mod) lhs rhs
  | .mod => mkApp4 (mkConst ``Mod.mod [.zero]) (mkConst ``Nat) Nat.mkInstMod lhs rhs
  | .hMod => mkApp6 (mkConst ``HMod.hMod [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHMod lhs rhs

def natPowerExpression (operator : NatEvalPowerOperator) (base exponent : Expr) : Expr :=
  match operator with
  | .natPow => mkApp2 (mkConst ``Nat.pow) base exponent
  | .natPowClass => mkApp4 (mkConst ``NatPow.pow [.zero])
      (mkConst ``Nat) Nat.mkInstNatPow base exponent
  | .pow => mkApp5 (mkConst ``Pow.pow [.zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstPow base exponent
  | .hPow => mkApp6 (mkConst ``HPow.hPow [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHPow base exponent

def overloadedBinaryExpression (operator : NatEvalBinaryOperator) (witnessExpr lhs rhs : Expr) : Expr :=
  match operator with
  | .add => mkApp4 (mkConst ``Add.add [.zero]) (mkConst ``Nat) witnessExpr lhs rhs
  | .hAdd => mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) witnessExpr lhs rhs
  | .sub => mkApp4 (mkConst ``Sub.sub [.zero]) (mkConst ``Nat) witnessExpr lhs rhs
  | .hSub => mkApp6 (mkConst ``HSub.hSub [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) witnessExpr lhs rhs
  | .mul => mkApp4 (mkConst ``Mul.mul [.zero]) (mkConst ``Nat) witnessExpr lhs rhs
  | .hMul => mkApp6 (mkConst ``HMul.hMul [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) witnessExpr lhs rhs
  | .div => mkApp4 (mkConst ``Div.div [.zero]) (mkConst ``Nat) witnessExpr lhs rhs
  | .hDiv => mkApp6 (mkConst ``HDiv.hDiv [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) witnessExpr lhs rhs
  | .mod => mkApp4 (mkConst ``Mod.mod [.zero]) (mkConst ``Nat) witnessExpr lhs rhs
  | .hMod => mkApp6 (mkConst ``HMod.hMod [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) witnessExpr lhs rhs
  | .natAdd | .natSub | .natMul | .natDiv | .natMod =>
      natBinaryExpression operator lhs rhs

def overloadedPowerExpression (operator : NatEvalPowerOperator) (witnessExpr base exponent : Expr) : Expr :=
  match operator with
  | .natPow => mkApp2 (mkConst ``Nat.pow) base exponent
  | .natPowClass => mkApp4 (mkConst ``NatPow.pow [.zero])
      (mkConst ``Nat) witnessExpr base exponent
  | .pow => mkApp5 (mkConst ``Pow.pow [.zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) witnessExpr base exponent
  | .hPow => mkApp6 (mkConst ``HPow.hPow [.zero, .zero, .zero])
      (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) witnessExpr base exponent

def natEvalBinaryValue (operator : NatEvalBinaryOperator) (lhs rhs : Nat) : Nat :=
  match operator with
  | .natAdd | .add | .hAdd => lhs + rhs
  | .natSub | .sub | .hSub => lhs - rhs
  | .natMul | .mul | .hMul => lhs * rhs
  | .natDiv | .div | .hDiv => lhs / rhs
  | .natMod | .mod | .hMod => lhs % rhs

def natEvalPowerValue (base exponent : Nat) : Nat := base ^ exponent

def expectedFinLiteral (modulus normalized : Nat) : Expr := finLiteral modulus normalized

def expectNoDerivation (label : String) (input output : Expr) : MetaM Unit := do
  let result? ← deriveFinMkCanonical? `Fin.reduceFinMk input output
  unless result?.isNone do
    throwError "{label}: expected no Fin.mk semantic derivation, got {repr result?}"

def expectDerivation (label : String) (modulusExpression : Expr)
    (modulus value : Nat) : MetaM (Expr × FinMkCanonicalDerivation) := do
  let input ← finMkExpression modulusExpression (natRaw value)
  let expected := expectedFinLiteral modulus (value % modulus)
  let some derivation ← deriveFinMkCanonical? `Fin.reduceFinMk input expected
    | throwError "{label}: Fin.mk semantic derivation was not recognized"
  unless derivation.modulus == modulus && derivation.value == value &&
      derivation.normalized == value % modulus do
    throwError "{label}: scalar derivation mismatch: {repr derivation}"
  let interpreted ← interpretFinMkCanonical input derivation
  unless Expr.equal interpreted expected do
    throwError "{label}: direct interpretation did not build expected literal"
  pure (input, derivation)

def traceOperator (trace : NatEvalTrace) : Option NatEvalBinaryOperator :=
  match trace with
  | .binary operator .. => some operator
  | _ => none

def tracePowerOperator (trace : NatEvalTrace) : Option NatEvalPowerOperator :=
  match trace with
  | .power operator .. => some operator
  | _ => none

def traceHasAssigned (trace : NatEvalTrace) : Bool :=
  match trace with
  | .assigned .. => true
  | .metadata body => traceHasAssigned body
  | .ofNat _ body _ => traceHasAssigned body
  | .succ body _ => traceHasAssigned body
  | .binary _ _ lhs rhs _ => traceHasAssigned lhs || traceHasAssigned rhs
  | .power _ _ base exponent _ _ => traceHasAssigned base || traceHasAssigned exponent
  | _ => false

def traceHasMetadata (trace : NatEvalTrace) : Bool :=
  match trace with
  | .metadata _ => true
  | .assigned _ _ body => traceHasMetadata body
  | .ofNat _ body _ => traceHasMetadata body
  | .succ body _ => traceHasMetadata body
  | .binary _ _ lhs rhs _ => traceHasMetadata lhs || traceHasMetadata rhs
  | .power _ _ base exponent _ _ => traceHasMetadata base || traceHasMetadata exponent
  | _ => false

def checkBinaryTrace (operator : NatEvalBinaryOperator) : MetaM Unit := do
  let lhs := natRaw 5
  let rhs := natRaw 2
  let modulusExpression := natBinaryExpression operator lhs rhs
  let modulus := natEvalBinaryValue operator 5 2
  let (_, derivation) ← expectDerivation s!"binary {repr operator}" modulusExpression modulus 0
  let .binary actualOperator instance? actualLhs actualRhs result := derivation.modulusTrace
    | throwError "binary {repr operator}: root trace is not binary"
  unless actualOperator == operator && result == modulus do
    throwError "binary {repr operator}: operator/result mismatch"
  unless actualLhs == .raw 5 && actualRhs == .raw 2 do
    throwError "binary {repr operator}: operand trace mismatch"
  let direct := match operator with
    | .natAdd | .natSub | .natMul | .natDiv | .natMod => true
    | _ => false
  unless instance?.isNone == direct do
    throwError "binary {repr operator}: instance presence mismatch"
  if !direct then
    unless instance?.isSome do
      throwError "binary {repr operator}: overloaded operator lost its witness"

def checkNatEvalBinaryForms : MetaM Unit := do
  for operator in #[
      NatEvalBinaryOperator.natAdd, .add, .hAdd,
      .natSub, .sub, .hSub,
      .natMul, .mul, .hMul,
      .natDiv, .div, .hDiv,
      .natMod, .mod, .hMod] do
    checkBinaryTrace operator
  let divisorZero := natBinaryExpression .natDiv (natRaw 5) (natRaw 0)
  let nestedDivZero := natBinaryExpression .natAdd divisorZero (natRaw 1)
  let (_, nestedDivDerivation) ← expectDerivation "binary divisor zero" nestedDivZero 1 0
  unless nestedDivDerivation.modulusTrace matches
      .binary .natAdd none (.binary .natDiv none (.raw 5) (.raw 0) 0) (.raw 1) 1 do
    throwError "Nat.div by zero trace/scalar mismatch"
  let moduloZero := natBinaryExpression .natMod (natRaw 5) (natRaw 0)
  let nestedModZero := natBinaryExpression .natAdd moduloZero (natRaw 1)
  let (_, nestedModDerivation) ← expectDerivation "binary modulus zero" nestedModZero 6 0
  unless nestedModDerivation.modulusTrace matches
      .binary .natAdd none (.binary .natMod none (.raw 5) (.raw 0) 5) (.raw 1) 6 do
    throwError "Nat.mod by zero trace/scalar mismatch"
  let underflow := natBinaryExpression .natSub (natRaw 2) (natRaw 5)
  let nestedUnderflow := natBinaryExpression .natAdd underflow (natRaw 1)
  let (_, underflowDerivation) ← expectDerivation "binary subtraction underflow" nestedUnderflow 1 0
  unless underflowDerivation.modulusTrace matches
      .binary .natAdd none (.binary .natSub none (.raw 2) (.raw 5) 0) (.raw 1) 1 do
    throwError "Nat.sub total-underflow trace/scalar mismatch"
  expectNoDerivation "final zero modulus" (← finMkExpression (natRaw 0) (natRaw 0))
    (expectedFinLiteral 0 0)

def checkPowerTrace (operator : NatEvalPowerOperator) : MetaM Unit := do
  let modulusExpression := natPowerExpression operator (natRaw 2) (natRaw 3)
  let (_, derivation) ← expectDerivation s!"power {repr operator}" modulusExpression 8 0
  let .power actualOperator instance? baseTrace exponentTrace threshold result :=
      derivation.modulusTrace
    | throwError "power {repr operator}: root trace is not power"
  unless actualOperator == operator && baseTrace == .raw 2 && exponentTrace == .raw 3 &&
      result == 8 do
    throwError "power {repr operator}: trace/scalar mismatch"
  let expectedThreshold := exponentiation.threshold.get (← getOptions)
  unless threshold == expectedThreshold do
    throwError "power {repr operator}: threshold was not recorded from the active options"
  let direct := operator == .natPow
  unless instance?.isNone == direct do
    throwError "power {repr operator}: instance presence mismatch"
  if !direct then
    unless instance?.isSome do
      throwError "power {repr operator}: overloaded power lost its witness"

def checkNatEvalPowerForms : MetaM Unit := do
  for operator in #[NatEvalPowerOperator.natPow, .natPowClass, .pow, .hPow] do
    checkPowerTrace operator
  withOptions (·.set exponentiation.threshold.name 2) do
    let input ← finMkExpression (natPowerExpression .natPow (natRaw 2) (natRaw 3)) (natRaw 0)
    expectNoDerivation "power threshold rejection" input (expectedFinLiteral 8 0)

def checkUnsupportedShapes : MetaM Unit := do
  let validInput ← finMkExpression (natRaw 5) (natRaw 2)
  expectNoDerivation "wrong procedure output" validInput (natRaw 0)
  expectNoDerivation "top metadata" (mkMData {} validInput) (expectedFinLiteral 5 2)
  let aliasInput ←
    pure <| mkApp3 (mkConst ``finMkAlias) (natRaw 5) (natRaw 2) (mkConst ``twoLtFive)
  expectNoDerivation "Fin.mk declaration alias" aliasInput (expectedFinLiteral 5 2)
  expectNoDerivation "modulus definition alias" (← finMkExpression (mkConst ``natAliasFive) (natRaw 0))
    (expectedFinLiteral 5 0)
  let badModulus ← pure <| mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat)
    (natRaw 5) (mkConst ``badNatOfNatFive)
  expectNoDerivation "nonstandard modulus OfNat instance"
    (← finMkExpression badModulus (natRaw 0)) (expectedFinLiteral 5 0)
  let badValue ← pure <| mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat)
    (natRaw 2) (mkConst ``badNatOfNatTwo)
  expectNoDerivation "nonstandard value OfNat instance"
    (← finMkExpression (natRaw 5) badValue) (expectedFinLiteral 5 2)
  let badAdd := overloadedBinaryExpression .add (mkConst ``badNatAdd) (natRaw 2) (natRaw 3)
  expectNoDerivation "nonstandard overloaded Add instance"
    (← finMkExpression badAdd (natRaw 0)) (expectedFinLiteral 5 0)
  let badHAdd := overloadedBinaryExpression .hAdd (mkConst ``badNatHAdd) (natRaw 2) (natRaw 3)
  expectNoDerivation "nonstandard overloaded HAdd instance"
    (← finMkExpression badHAdd (natRaw 0)) (expectedFinLiteral 5 0)
  let badPow := overloadedPowerExpression .natPowClass (mkConst ``badNatPow)
    (natRaw 2) (natRaw 3)
  expectNoDerivation "nonstandard overloaded NatPow instance"
    (← finMkExpression badPow (natRaw 0)) (expectedFinLiteral 8 0)
  let badHPow := overloadedPowerExpression .hPow (mkConst ``badNatHPow)
    (natRaw 2) (natRaw 3)
  expectNoDerivation "nonstandard overloaded HPow instance"
    (← finMkExpression badHPow (natRaw 0)) (expectedFinLiteral 8 0)
  let openModulus ← mkFreshExprMVar (mkConst ``Nat)
  expectNoDerivation "open modulus" (← finMkExpression openModulus (natRaw 0))
    (expectedFinLiteral 5 0)
  let openValue ← mkFreshExprMVar (mkConst ``Nat)
  expectNoDerivation "open value" (← finMkExpression (natRaw 5) openValue)
    (expectedFinLiteral 5 0)
  let malformed ← pure <| mkApp2 (mkConst ``Fin.mk) (natRaw 5) (natRaw 0)
  expectNoDerivation "Fin.mk wrong arity" malformed (expectedFinLiteral 5 0)

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
  pure <| listFingerprint entries

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
    throwError "{label}: replay state mismatch: {repr recordedSummary} != {repr replayedSummary}"

def checkProgramJson (label : String) (program : Simp.Engine.Program) : MetaM Unit := do
  let decoded : Simp.Engine.Program ←
    match Lean.fromJson? (Lean.toJson program) with
    | .ok decoded => pure decoded
    | .error message => throwError "{label}: program JSON roundtrip failed: {message}"
  unless decoded == program do
    throwError "{label}: program JSON roundtrip changed the payload"

def checkRecordedFold (label : String) (expression : Expr) (ordinary : Bool) :
    MetaM (Simp.Engine.Program × Simp.Context × Simp.Engine.ReplayConfig ×
      Simp.Engine.SimprocTrace) := do
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
        fold.finalDisposition == .done && !fold.finalProofPresent &&
        fold.finalCache == some true && event.stepDisposition == .done do
      throwError "{label}: ordinary fold summary mismatch: {repr fold}"
    let candidate := fold.candidates[0]!
    unless candidate.declaration == `Fin.reduceFinMk &&
        candidate.procedureKind == .dsimp && candidate.setIndex == 0 &&
        candidate.registryPost && candidate.disposition == .done &&
        !candidate.proofPresent && candidate.cache == some true &&
        candidate.numExtraArgs == 0 && candidate.extraArgumentFingerprints.isEmpty do
      throwError "{label}: ordinary candidate summary mismatch: {repr candidate}"
    let .canonicalValue (.finMkCanonical derivation) := candidate.semantics
      | throwError "{label}: ordinary fold has wrong semantic constructor"
    unless derivation.modulus == 5 && derivation.value == 2 && derivation.normalized == 2 do
      throwError "{label}: ordinary Fin.mk semantic scalar mismatch"
    checkProgramJson label recording.program
    let config ← Simp.Engine.replayConfigOfContext ctx
    let (replayed, replayedState) ←
      Simp.Engine.mainCoreReplay expression ctx config recording.program
    unless Expr.equal recorded.expr replayed.expr do
      throwError "{label}: ordinary replay expression mismatch"
    checkStateParity label recordedState replayedState
    pure (recording.program, ctx, config, recording.simprocs)

  else
    let (recorded, recordedState, recording) ←
      Simp.Engine.dsimpMainCoreRecording expression ctx (methods := methods)
    unless recording.deferred.isNone do
      throwError "{label}: dsimp recording deferred: {repr recording.deferred}"
    ExplicitLean.SimpEngine.Replay.validateSimprocObservations
      recording.program recording.simprocs
    let events := semanticEvents recording.program
    unless events.size == 1 do
      throwError "{label}: expected one dsimp semantic fold, got {events.size}"
    let some event := events[0]? | unreachable!
    let .semanticSimproc fold := event.operation | unreachable!
    unless fold.phase == .dpost && fold.candidates.size == 1 &&
        fold.finalDisposition == .done && !fold.finalProofPresent &&
        fold.finalCache.isNone && event.stepDisposition == .done do
      throwError "{label}: dsimp fold summary mismatch: {repr fold}"
    let candidate := fold.candidates[0]!
    unless candidate.declaration == `Fin.reduceFinMk &&
        candidate.procedureKind == .dsimp && candidate.setIndex == 0 &&
        candidate.registryPost && candidate.disposition == .done &&
        !candidate.proofPresent && candidate.cache.isNone &&
        candidate.numExtraArgs == 0 && candidate.extraArgumentFingerprints.isEmpty do
      throwError "{label}: dsimp candidate summary mismatch: {repr candidate}"
    let .canonicalValue (.finMkCanonical derivation) := candidate.semantics
      | throwError "{label}: dsimp fold has wrong semantic constructor"
    unless derivation.modulus == 5 && derivation.value == 2 && derivation.normalized == 2 do
      throwError "{label}: dsimp Fin.mk semantic scalar mismatch"
    checkProgramJson label recording.program
    let config ← Simp.Engine.replayConfigOfContext ctx
    let (replayed, replayedState) ←
      Simp.Engine.dsimpMainCoreReplay expression ctx config recording.program
    unless Expr.equal recorded replayed do
      throwError "{label}: dsimp replay expression mismatch"
    checkStateParity label recordedState replayedState
    pure (recording.program, ctx, config, recording.simprocs)

def checkNatEvalLeaves : MetaM Unit := do
  let (_, rawDerivation) ← expectDerivation "raw modulus" (natRaw 5) 5 0
  unless rawDerivation.modulusTrace == .raw 5 do
    throwError "raw modulus did not record NatEvalTrace.raw"
  let (_, metadataDerivation) ←
    expectDerivation "metadata modulus" (mkMData {} (natRaw 5)) 5 0
  unless metadataDerivation.modulusTrace == .metadata (.raw 5) do
    throwError "metadata modulus did not record NatEvalTrace.metadata"
  let (_, zeroDerivation) ←
    expectDerivation "successor of zero modulus" (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)) 1 0
  unless zeroDerivation.modulusTrace == .succ .zero 1 do
    throwError "Nat.succ/Nat.zero trace mismatch: {repr zeroDerivation.modulusTrace}"
  let (_, ofNatDerivation) ← expectDerivation "OfNat modulus" (natOfNat 5) 5 0
  unless ofNatDerivation.modulusTrace matches .ofNat _ (.raw 5) 5 do
    throwError "OfNat modulus did not record NatEvalTrace.ofNat"
  let (_, metadataOfNatDerivation) ←
    expectDerivation "metadata OfNat modulus" (mkMData {} (natOfNat 5)) 5 0
  unless metadataOfNatDerivation.modulusTrace matches .metadata (.ofNat _ (.raw 5) 5) do
    throwError "metadata OfNat modulus trace mismatch"
  let modulusMVar ← mkFreshExprMVar (mkConst ``Nat)
  modulusMVar.mvarId!.assign (natRaw 5)
  let assignedInput ← finMkExpression modulusMVar (natRaw 0)
  let assignedExpected := expectedFinLiteral 5 0
  let some assignedDerivation ←
    deriveFinMkCanonical? `Fin.reduceFinMk assignedInput assignedExpected
    | throwError "assigned raw modulus was not recognized"
  unless assignedDerivation.modulusTrace matches .assigned _ 5 (.raw 5) do
    throwError "assigned raw modulus trace mismatch: {repr assignedDerivation.modulusTrace}"
  let assignedOutput ← interpretFinMkCanonical assignedInput assignedDerivation
  unless Expr.equal assignedOutput assignedExpected do
    throwError "assigned raw modulus interpretation mismatch"
  let assignedMetadataMVar ← mkFreshExprMVar (mkConst ``Nat)
  assignedMetadataMVar.mvarId!.assign (mkMData {} (natRaw 5))
  let assignedMetadataInput ← finMkExpression assignedMetadataMVar (natRaw 0)
  let some assignedMetadataDerivation ←
    deriveFinMkCanonical? `Fin.reduceFinMk assignedMetadataInput assignedExpected
    | throwError "assigned metadata modulus was not recognized"
  unless assignedMetadataDerivation.modulusTrace matches
      .assigned _ 5 (.metadata (.raw 5)) do
    throwError "assigned metadata modulus trace mismatch: {repr assignedMetadataDerivation.modulusTrace}"
  let proofMVarInput ← finMkExpressionWithProofMVar (natRaw 5) (natRaw 0)
  let proofMVarExpected := expectedFinLiteral 5 0
  let some _ ← deriveFinMkCanonical? `Fin.reduceFinMk proofMVarInput proofMVarExpected
    | throwError "ignored proof metavariable was not accepted"
  let valueOfNatInput ← finMkExpression (natRaw 5) (natOfNat 2)
  let valueOfNatExpected := expectedFinLiteral 5 2
  let some valueOfNatDerivation ←
    deriveFinMkCanonical? `Fin.reduceFinMk valueOfNatInput valueOfNatExpected
    | throwError "OfNat value was not recognized"
  unless valueOfNatDerivation.valueView matches .ofNat _ 2 0 _ do
    throwError "OfNat value view was not recorded"
  let metadataOfNatValueInput ← finMkExpression (natRaw 5) (mkMData {} (natOfNat 2))
  let some metadataOfNatValueDerivation ←
    deriveFinMkCanonical? `Fin.reduceFinMk metadataOfNatValueInput valueOfNatExpected
    | throwError "metadata OfNat value was not recognized"
  unless metadataOfNatValueDerivation.valueView matches .ofNat _ 2 1 _ do
    throwError "metadata OfNat value view depth was not recorded"
  let metadataValueInput ← finMkExpression (natRaw 5) (mkMData {} (natRaw 2))
  let metadataValueExpected := expectedFinLiteral 5 2
  let some metadataValueDerivation ←
    deriveFinMkCanonical? `Fin.reduceFinMk metadataValueInput metadataValueExpected
    | throwError "metadata value was not recognized"
  unless metadataValueDerivation.valueView matches .raw _ 2 1 do
    throwError "metadata value view depth was not recorded"
  let unassigned ← mkFreshExprMVar (mkConst ``Nat)
  let unassignedInput ← finMkExpression unassigned (natRaw 0)
  expectNoDerivation "unassigned modulus" unassignedInput (expectedFinLiteral 5 0)

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

def mutateInstanceTypeFingerprint (witness : InstanceWitness) : InstanceWitness :=
  { witness with typeFingerprint := "mutated" }

def mutateInstanceTerm (witness : InstanceWitness) : InstanceWitness :=
  { witness with term := .literal (.nat 0) }

def mutateTraceAtRaw : NatEvalTrace → NatEvalTrace
  | .raw value => .raw (value + 1)
  | .metadata body => .metadata (mutateTraceAtRaw body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtRaw body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtRaw body) result
  | .succ body result => .succ (mutateTraceAtRaw body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtRaw lhs) (mutateTraceAtRaw rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtRaw base) (mutateTraceAtRaw exponent)
        threshold result
  | trace => trace

def mutateTraceAtMetadata : NatEvalTrace → NatEvalTrace
  | .metadata _ => .metadata (.raw 0)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtMetadata body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtMetadata body) result
  | .succ body result => .succ (mutateTraceAtMetadata body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtMetadata lhs) (mutateTraceAtMetadata rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtMetadata base) (mutateTraceAtMetadata exponent)
        threshold result
  | trace => trace

def mutateTraceAtAssignedFingerprint : NatEvalTrace → NatEvalTrace
  | .assigned _ value body => .assigned "mutated" value body
  | .metadata body => .metadata (mutateTraceAtAssignedFingerprint body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtAssignedFingerprint body) result
  | .succ body result => .succ (mutateTraceAtAssignedFingerprint body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtAssignedFingerprint lhs)
        (mutateTraceAtAssignedFingerprint rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtAssignedFingerprint base)
        (mutateTraceAtAssignedFingerprint exponent) threshold result
  | trace => trace

def mutateTraceAtAssignedValue : NatEvalTrace → NatEvalTrace
  | .assigned fingerprint value body => .assigned fingerprint (value + 1) body
  | .metadata body => .metadata (mutateTraceAtAssignedValue body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtAssignedValue body) result
  | .succ body result => .succ (mutateTraceAtAssignedValue body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtAssignedValue lhs)
        (mutateTraceAtAssignedValue rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtAssignedValue base)
        (mutateTraceAtAssignedValue exponent) threshold result
  | trace => trace

def mutateTraceAtOfNatWitness : NatEvalTrace → NatEvalTrace
  | .ofNat witness body result => .ofNat (mutateInstancePath witness) body result
  | .metadata body => .metadata (mutateTraceAtOfNatWitness body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtOfNatWitness body)
  | .succ body result => .succ (mutateTraceAtOfNatWitness body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtOfNatWitness lhs) (mutateTraceAtOfNatWitness rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtOfNatWitness base)
        (mutateTraceAtOfNatWitness exponent) threshold result
  | trace => trace

def mutateTraceAtOfNatFingerprint : NatEvalTrace → NatEvalTrace
  | .ofNat witness body result => .ofNat (mutateInstanceFingerprint witness) body result
  | .metadata body => .metadata (mutateTraceAtOfNatFingerprint body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtOfNatFingerprint body)
  | .succ body result => .succ (mutateTraceAtOfNatFingerprint body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtOfNatFingerprint lhs)
        (mutateTraceAtOfNatFingerprint rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtOfNatFingerprint base)
        (mutateTraceAtOfNatFingerprint exponent) threshold result
  | trace => trace

def mutateTraceAtOfNatType : NatEvalTrace → NatEvalTrace
  | .ofNat witness body result => .ofNat (mutateInstanceTypeFingerprint witness) body result
  | .metadata body => .metadata (mutateTraceAtOfNatType body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtOfNatType body)
  | .succ body result => .succ (mutateTraceAtOfNatType body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtOfNatType lhs) (mutateTraceAtOfNatType rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtOfNatType base)
        (mutateTraceAtOfNatType exponent) threshold result
  | trace => trace

def mutateTraceAtOfNatTerm : NatEvalTrace → NatEvalTrace
  | .ofNat witness body result => .ofNat (mutateInstanceTerm witness) body result
  | .metadata body => .metadata (mutateTraceAtOfNatTerm body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtOfNatTerm body)
  | .succ body result => .succ (mutateTraceAtOfNatTerm body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtOfNatTerm lhs) (mutateTraceAtOfNatTerm rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtOfNatTerm base)
        (mutateTraceAtOfNatTerm exponent) threshold result
  | trace => trace

def mutateTraceAtOfNatNumeral : NatEvalTrace → NatEvalTrace
  | .ofNat witness _ result => .ofNat witness (.raw 0) result
  | .metadata body => .metadata (mutateTraceAtOfNatNumeral body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtOfNatNumeral body)
  | .succ body result => .succ (mutateTraceAtOfNatNumeral body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtOfNatNumeral lhs) (mutateTraceAtOfNatNumeral rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtOfNatNumeral base)
        (mutateTraceAtOfNatNumeral exponent) threshold result
  | trace => trace

def mutateTraceAtOfNatResult : NatEvalTrace → NatEvalTrace
  | .ofNat witness body result => .ofNat witness body (result + 1)
  | .metadata body => .metadata (mutateTraceAtOfNatResult body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtOfNatResult body)
  | .succ body result => .succ (mutateTraceAtOfNatResult body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtOfNatResult lhs) (mutateTraceAtOfNatResult rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtOfNatResult base)
        (mutateTraceAtOfNatResult exponent) threshold result
  | trace => trace

def mutateTraceAtSuccArgument : NatEvalTrace → NatEvalTrace
  | .succ _ result => .succ (.raw 0) result
  | .metadata body => .metadata (mutateTraceAtSuccArgument body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtSuccArgument body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtSuccArgument body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtSuccArgument lhs) (mutateTraceAtSuccArgument rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtSuccArgument base)
        (mutateTraceAtSuccArgument exponent) threshold result
  | trace => trace

def mutateTraceAtSuccResult : NatEvalTrace → NatEvalTrace
  | .succ body result => .succ body (result + 1)
  | .metadata body => .metadata (mutateTraceAtSuccResult body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtSuccResult body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtSuccResult body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtSuccResult lhs) (mutateTraceAtSuccResult rhs) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtSuccResult base)
        (mutateTraceAtSuccResult exponent) threshold result
  | trace => trace

def mutateTraceAtBinaryOperator : NatEvalTrace → NatEvalTrace
  | .binary _ witness lhs rhs result => .binary .natSub witness lhs rhs result
  | .metadata body => .metadata (mutateTraceAtBinaryOperator body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtBinaryOperator body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtBinaryOperator body) result
  | .succ body result => .succ (mutateTraceAtBinaryOperator body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtBinaryOperator base)
        (mutateTraceAtBinaryOperator exponent) threshold result
  | trace => trace

def mutateTraceAtBinaryWitness : NatEvalTrace → NatEvalTrace
  | .binary operator none lhs rhs result => .binary operator (some default) lhs rhs result
  | .binary operator (some witness) lhs rhs result => .binary operator none lhs rhs result
  | .metadata body => .metadata (mutateTraceAtBinaryWitness body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtBinaryWitness body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtBinaryWitness body) result
  | .succ body result => .succ (mutateTraceAtBinaryWitness body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtBinaryWitness base)
        (mutateTraceAtBinaryWitness exponent) threshold result
  | trace => trace

def mutateTraceAtBinaryWitnessPath : NatEvalTrace → NatEvalTrace
  | .binary operator (some witness) lhs rhs result =>
      .binary operator (some (mutateInstancePath witness)) lhs rhs result
  | .binary operator none lhs rhs result =>
      .binary operator (some (mutateInstancePath default)) lhs rhs result
  | .metadata body => .metadata (mutateTraceAtBinaryWitnessPath body)
  | .assigned fingerprint value body =>
      .assigned fingerprint value (mutateTraceAtBinaryWitnessPath body)
  | .ofNat witness body result =>
      .ofNat witness (mutateTraceAtBinaryWitnessPath body) result
  | .succ body result => .succ (mutateTraceAtBinaryWitnessPath body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtBinaryWitnessPath base)
        (mutateTraceAtBinaryWitnessPath exponent) threshold result
  | trace => trace

def mutateTraceAtBinaryWitnessFingerprint : NatEvalTrace → NatEvalTrace
  | .binary operator (some witness) lhs rhs result =>
      .binary operator (some (mutateInstanceFingerprint witness)) lhs rhs result
  | .binary operator none lhs rhs result =>
      .binary operator (some (mutateInstanceFingerprint default)) lhs rhs result
  | .metadata body => .metadata (mutateTraceAtBinaryWitnessFingerprint body)
  | .assigned fingerprint value body =>
      .assigned fingerprint value (mutateTraceAtBinaryWitnessFingerprint body)
  | .ofNat witness body result =>
      .ofNat witness (mutateTraceAtBinaryWitnessFingerprint body) result
  | .succ body result => .succ (mutateTraceAtBinaryWitnessFingerprint body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtBinaryWitnessFingerprint base)
        (mutateTraceAtBinaryWitnessFingerprint exponent) threshold result
  | trace => trace

def mutateTraceAtBinaryWitnessType : NatEvalTrace → NatEvalTrace
  | .binary operator (some witness) lhs rhs result =>
      .binary operator (some (mutateInstanceTypeFingerprint witness)) lhs rhs result
  | .binary operator none lhs rhs result =>
      .binary operator (some (mutateInstanceTypeFingerprint default)) lhs rhs result
  | .metadata body => .metadata (mutateTraceAtBinaryWitnessType body)
  | .assigned fingerprint value body =>
      .assigned fingerprint value (mutateTraceAtBinaryWitnessType body)
  | .ofNat witness body result =>
      .ofNat witness (mutateTraceAtBinaryWitnessType body) result
  | .succ body result => .succ (mutateTraceAtBinaryWitnessType body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtBinaryWitnessType base)
        (mutateTraceAtBinaryWitnessType exponent) threshold result
  | trace => trace

def mutateTraceAtBinaryOperands : NatEvalTrace → NatEvalTrace
  | .binary operator witness lhs rhs result => .binary operator witness rhs lhs result
  | .metadata body => .metadata (mutateTraceAtBinaryOperands body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtBinaryOperands body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtBinaryOperands body) result
  | .succ body result => .succ (mutateTraceAtBinaryOperands body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtBinaryOperands base)
        (mutateTraceAtBinaryOperands exponent) threshold result
  | trace => trace

def mutateTraceAtBinaryResult : NatEvalTrace → NatEvalTrace
  | .binary operator witness lhs rhs result => .binary operator witness lhs rhs (result + 1)
  | .metadata body => .metadata (mutateTraceAtBinaryResult body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtBinaryResult body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtBinaryResult body) result
  | .succ body result => .succ (mutateTraceAtBinaryResult body) result
  | .power operator witness base exponent threshold result =>
      .power operator witness (mutateTraceAtBinaryResult base)
        (mutateTraceAtBinaryResult exponent) threshold result
  | trace => trace

def mutateTraceAtPowerOperator : NatEvalTrace → NatEvalTrace
  | .power _ witness base exponent threshold result =>
      .power .pow witness base exponent threshold result
  | .metadata body => .metadata (mutateTraceAtPowerOperator body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtPowerOperator body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtPowerOperator body) result
  | .succ body result => .succ (mutateTraceAtPowerOperator body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtPowerOperator lhs) (mutateTraceAtPowerOperator rhs) result
  | trace => trace

def mutateTraceAtPowerWitness : NatEvalTrace → NatEvalTrace
  | .power operator none base exponent threshold result =>
      .power operator (some default) base exponent threshold result
  | .power operator (some witness) base exponent threshold result =>
      .power operator none base exponent threshold result
  | .metadata body => .metadata (mutateTraceAtPowerWitness body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtPowerWitness body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtPowerWitness body) result
  | .succ body result => .succ (mutateTraceAtPowerWitness body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtPowerWitness lhs) (mutateTraceAtPowerWitness rhs) result
  | trace => trace

def mutateTraceAtPowerWitnessPath : NatEvalTrace → NatEvalTrace
  | .power operator (some witness) base exponent threshold result =>
      .power operator (some (mutateInstancePath witness)) base exponent threshold result
  | .power operator none base exponent threshold result =>
      .power operator (some (mutateInstancePath default)) base exponent threshold result
  | .metadata body => .metadata (mutateTraceAtPowerWitnessPath body)
  | .assigned fingerprint value body =>
      .assigned fingerprint value (mutateTraceAtPowerWitnessPath body)
  | .ofNat witness body result =>
      .ofNat witness (mutateTraceAtPowerWitnessPath body) result
  | .succ body result => .succ (mutateTraceAtPowerWitnessPath body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtPowerWitnessPath lhs)
        (mutateTraceAtPowerWitnessPath rhs) result
  | trace => trace

def mutateTraceAtPowerWitnessFingerprint : NatEvalTrace → NatEvalTrace
  | .power operator (some witness) base exponent threshold result =>
      .power operator (some (mutateInstanceFingerprint witness)) base exponent threshold result
  | .power operator none base exponent threshold result =>
      .power operator (some (mutateInstanceFingerprint default)) base exponent threshold result
  | .metadata body => .metadata (mutateTraceAtPowerWitnessFingerprint body)
  | .assigned fingerprint value body =>
      .assigned fingerprint value (mutateTraceAtPowerWitnessFingerprint body)
  | .ofNat witness body result =>
      .ofNat witness (mutateTraceAtPowerWitnessFingerprint body) result
  | .succ body result => .succ (mutateTraceAtPowerWitnessFingerprint body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtPowerWitnessFingerprint lhs)
        (mutateTraceAtPowerWitnessFingerprint rhs) result
  | trace => trace

def mutateTraceAtPowerWitnessType : NatEvalTrace → NatEvalTrace
  | .power operator (some witness) base exponent threshold result =>
      .power operator (some (mutateInstanceTypeFingerprint witness)) base exponent threshold result
  | .power operator none base exponent threshold result =>
      .power operator (some (mutateInstanceTypeFingerprint default)) base exponent threshold result
  | .metadata body => .metadata (mutateTraceAtPowerWitnessType body)
  | .assigned fingerprint value body =>
      .assigned fingerprint value (mutateTraceAtPowerWitnessType body)
  | .ofNat witness body result =>
      .ofNat witness (mutateTraceAtPowerWitnessType body) result
  | .succ body result => .succ (mutateTraceAtPowerWitnessType body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtPowerWitnessType lhs)
        (mutateTraceAtPowerWitnessType rhs) result
  | trace => trace

def mutateTraceAtPowerOperands : NatEvalTrace → NatEvalTrace
  | .power operator witness base exponent threshold result =>
      .power operator witness exponent base threshold result
  | .metadata body => .metadata (mutateTraceAtPowerOperands body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtPowerOperands body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtPowerOperands body) result
  | .succ body result => .succ (mutateTraceAtPowerOperands body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtPowerOperands lhs) (mutateTraceAtPowerOperands rhs) result
  | trace => trace

def mutateTraceAtPowerThreshold : NatEvalTrace → NatEvalTrace
  | .power operator witness base exponent threshold result =>
      .power operator witness base exponent 0 result
  | .metadata body => .metadata (mutateTraceAtPowerThreshold body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtPowerThreshold body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtPowerThreshold body) result
  | .succ body result => .succ (mutateTraceAtPowerThreshold body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtPowerThreshold lhs)
        (mutateTraceAtPowerThreshold rhs) result
  | trace => trace

def mutateTraceAtPowerResult : NatEvalTrace → NatEvalTrace
  | .power operator witness base exponent threshold result =>
      .power operator witness base exponent threshold (result + 1)
  | .metadata body => .metadata (mutateTraceAtPowerResult body)
  | .assigned fingerprint value body => .assigned fingerprint value (mutateTraceAtPowerResult body)
  | .ofNat witness body result => .ofNat witness (mutateTraceAtPowerResult body) result
  | .succ body result => .succ (mutateTraceAtPowerResult body) result
  | .binary operator witness lhs rhs result =>
      .binary operator witness (mutateTraceAtPowerResult lhs) (mutateTraceAtPowerResult rhs) result
  | trace => trace

def expectInterpretFailure (label : String) (input : Expr)
    (derivation : FinMkCanonicalDerivation) : MetaM Nat := do
  let saved ← Meta.saveState
  let succeeded ← try
    let _ ← interpretFinMkCanonical input derivation
    pure true
  catch _ => pure false
  saved.restore
  unless !succeeded do
    throwError "{label}: mutation was accepted"
  pure 1

def mutateDerivationTrace (derivation : FinMkCanonicalDerivation)
    (mutate : NatEvalTrace → NatEvalTrace) : FinMkCanonicalDerivation :=
  { derivation with modulusTrace := mutate derivation.modulusTrace }

def checkTraceMutations : MetaM Nat := do
  let (rawInput, rawDerivation) ← expectDerivation "mutation raw" (natRaw 5) 5 0
  let (metadataInput, metadataDerivation) ←
    expectDerivation "mutation metadata" (mkMData {} (natRaw 5)) 5 0
  let assignedMVar ← mkFreshExprMVar (mkConst ``Nat)
  assignedMVar.mvarId!.assign (natRaw 5)
  let assignedInput ← finMkExpression assignedMVar (natRaw 0)
  let some assignedDerivation ← deriveFinMkCanonical? `Fin.reduceFinMk assignedInput
      (expectedFinLiteral 5 0)
    | throwError "mutation assigned fixture was not recognized"
  let (ofNatInput, ofNatDerivation) ← expectDerivation "mutation OfNat" (natOfNat 5) 5 0
  let (overloadedBinaryInput, overloadedBinaryDerivation) ← expectDerivation
    "mutation overloaded binary" (natBinaryExpression .add (natRaw 2) (natRaw 3)) 5 0
  let (succInput, succDerivation) ← expectDerivation "mutation succ"
    (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)) 1 0
  let (binaryInput, binaryDerivation) ← expectDerivation "mutation binary"
    (natBinaryExpression .natAdd (natRaw 2) (natRaw 3)) 5 0
  let (powerInput, powerDerivation) ← expectDerivation "mutation power"
    (natPowerExpression .natPow (natRaw 2) (natRaw 3)) 8 0
  let (overloadedPowerInput, overloadedPowerDerivation) ← expectDerivation
    "mutation overloaded power" (natPowerExpression .natPowClass (natRaw 2) (natRaw 3)) 8 0
  let .raw valueReference .. := rawDerivation.valueView
    | throwError "mutation raw fixture did not use a raw value view"
  let changedValuePath := { valueReference with path := #[] }
  let changedValueFingerprint := { valueReference with fingerprint := "mutated" }
  let mut rejected := 0
  rejected := rejected + (← expectInterpretFailure "derivation modulus"
    rawInput { rawDerivation with modulus := 6 })
  rejected := rejected + (← expectInterpretFailure "derivation value"
    rawInput { rawDerivation with value := 1 })
  rejected := rejected + (← expectInterpretFailure "derivation normalized"
    rawInput { rawDerivation with normalized := 1 })
  rejected := rejected + (← expectInterpretFailure "derivation modulus path"
    rawInput { rawDerivation with modulusReference :=
      { rawDerivation.modulusReference with path := #[] } })
  rejected := rejected + (← expectInterpretFailure "derivation modulus fingerprint"
    rawInput { rawDerivation with modulusReference :=
      { rawDerivation.modulusReference with fingerprint := "mutated" } })
  rejected := rejected + (← expectInterpretFailure "derivation value view value"
    rawInput { rawDerivation with valueView := .raw valueReference 1 0 })
  rejected := rejected + (← expectInterpretFailure "derivation value view path"
    rawInput { rawDerivation with valueView := .raw changedValuePath 0 0 })
  rejected := rejected + (← expectInterpretFailure "derivation value view fingerprint"
    rawInput { rawDerivation with valueView := .raw changedValueFingerprint 0 0 })
  rejected := rejected + (← expectInterpretFailure "derivation value view metadata"
    rawInput { rawDerivation with valueView := .raw valueReference 0 1 })
  rejected := rejected + (← expectInterpretFailure "derivation value view constructor"
    rawInput { rawDerivation with valueView := .ofNat valueReference 0 0 default })
  rejected := rejected + (← expectInterpretFailure "raw trace value"
    rawInput (mutateDerivationTrace rawDerivation mutateTraceAtRaw))
  rejected := rejected + (← expectInterpretFailure "metadata trace body"
    metadataInput (mutateDerivationTrace metadataDerivation mutateTraceAtMetadata))
  rejected := rejected + (← expectInterpretFailure "assigned trace fingerprint"
    assignedInput (mutateDerivationTrace assignedDerivation mutateTraceAtAssignedFingerprint))
  rejected := rejected + (← expectInterpretFailure "assigned trace value"
    assignedInput (mutateDerivationTrace assignedDerivation mutateTraceAtAssignedValue))
  rejected := rejected + (← expectInterpretFailure "OfNat trace witness term"
    ofNatInput (mutateDerivationTrace ofNatDerivation mutateTraceAtOfNatTerm))
  rejected := rejected + (← expectInterpretFailure "OfNat trace witness path"
    ofNatInput (mutateDerivationTrace ofNatDerivation mutateTraceAtOfNatWitness))
  rejected := rejected + (← expectInterpretFailure "OfNat trace witness fingerprint"
    ofNatInput (mutateDerivationTrace ofNatDerivation mutateTraceAtOfNatFingerprint))
  rejected := rejected + (← expectInterpretFailure "OfNat trace witness type"
    ofNatInput (mutateDerivationTrace ofNatDerivation mutateTraceAtOfNatType))
  rejected := rejected + (← expectInterpretFailure "OfNat trace numeral"
    ofNatInput (mutateDerivationTrace ofNatDerivation mutateTraceAtOfNatNumeral))
  rejected := rejected + (← expectInterpretFailure "OfNat trace result"
    ofNatInput (mutateDerivationTrace ofNatDerivation mutateTraceAtOfNatResult))
  rejected := rejected + (← expectInterpretFailure "successor trace argument"
    succInput (mutateDerivationTrace succDerivation mutateTraceAtSuccArgument))
  rejected := rejected + (← expectInterpretFailure "successor trace result"
    succInput (mutateDerivationTrace succDerivation mutateTraceAtSuccResult))
  rejected := rejected + (← expectInterpretFailure "binary trace operator"
    binaryInput (mutateDerivationTrace binaryDerivation mutateTraceAtBinaryOperator))
  rejected := rejected + (← expectInterpretFailure "binary trace witness"
    binaryInput (mutateDerivationTrace binaryDerivation mutateTraceAtBinaryWitness))
  rejected := rejected + (← expectInterpretFailure "binary trace witness term"
    overloadedBinaryInput (mutateDerivationTrace overloadedBinaryDerivation
      (fun trace => match trace with
        | .binary operator (some witness) lhs rhs result =>
            .binary operator (some (mutateInstanceTerm witness)) lhs rhs result
        | trace => trace)))
  rejected := rejected + (← expectInterpretFailure "binary trace witness path"
    overloadedBinaryInput (mutateDerivationTrace overloadedBinaryDerivation
      mutateTraceAtBinaryWitnessPath))
  rejected := rejected + (← expectInterpretFailure "binary trace witness fingerprint"
    overloadedBinaryInput (mutateDerivationTrace overloadedBinaryDerivation
      mutateTraceAtBinaryWitnessFingerprint))
  rejected := rejected + (← expectInterpretFailure "binary trace witness type"
    overloadedBinaryInput (mutateDerivationTrace overloadedBinaryDerivation
      mutateTraceAtBinaryWitnessType))
  rejected := rejected + (← expectInterpretFailure "binary trace operands"
    binaryInput (mutateDerivationTrace binaryDerivation mutateTraceAtBinaryOperands))
  rejected := rejected + (← expectInterpretFailure "binary trace result"
    binaryInput (mutateDerivationTrace binaryDerivation mutateTraceAtBinaryResult))
  rejected := rejected + (← expectInterpretFailure "power trace operator"
    powerInput (mutateDerivationTrace powerDerivation mutateTraceAtPowerOperator))
  rejected := rejected + (← expectInterpretFailure "power trace witness"
    powerInput (mutateDerivationTrace powerDerivation mutateTraceAtPowerWitness))
  rejected := rejected + (← expectInterpretFailure "power trace witness term"
    overloadedPowerInput (mutateDerivationTrace overloadedPowerDerivation
      (fun trace => match trace with
        | .power operator (some witness) base exponent threshold result =>
            .power operator (some (mutateInstanceTerm witness)) base exponent threshold result
        | trace => trace)))
  rejected := rejected + (← expectInterpretFailure "power trace witness path"
    overloadedPowerInput (mutateDerivationTrace overloadedPowerDerivation
      mutateTraceAtPowerWitnessPath))
  rejected := rejected + (← expectInterpretFailure "power trace witness fingerprint"
    overloadedPowerInput (mutateDerivationTrace overloadedPowerDerivation
      mutateTraceAtPowerWitnessFingerprint))
  rejected := rejected + (← expectInterpretFailure "power trace witness type"
    overloadedPowerInput (mutateDerivationTrace overloadedPowerDerivation
      mutateTraceAtPowerWitnessType))
  rejected := rejected + (← expectInterpretFailure "power trace operands"
    powerInput (mutateDerivationTrace powerDerivation mutateTraceAtPowerOperands))
  rejected := rejected + (← expectInterpretFailure "power trace threshold"
    powerInput (mutateDerivationTrace powerDerivation mutateTraceAtPowerThreshold))
  rejected := rejected + (← expectInterpretFailure "power trace result"
    powerInput (mutateDerivationTrace powerDerivation mutateTraceAtPowerResult))
  pure rejected

def isSemanticEvent (event : Simp.Engine.Event) : Bool :=
  match event.operation with
  | .semanticSimproc _ => true
  | _ => false

def mutateSemanticCandidate (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocCandidateEvent → Simp.Engine.SimprocCandidateEvent) :
    Simp.Engine.Program :=
  match Array.findIdx? isSemanticEvent program.events with
  | none => program
  | some eventIndex =>
      match program.events[eventIndex]? with
      | none => program
      | some event =>
          match event.operation with
          | .semanticSimproc fold =>
              let fold := { fold with candidates := fold.candidates.set! 0 (mutate fold.candidates[0]!) }
              { program with events := program.events.set! eventIndex {
                  event with operation := .semanticSimproc fold } }
          | _ => program

def mutateSemanticFold (program : Simp.Engine.Program)
    (mutate : Simp.Engine.SimprocFold → Simp.Engine.SimprocFold) :
    Simp.Engine.Program :=
  match Array.findIdx? isSemanticEvent program.events with
  | none => program
  | some eventIndex =>
      match program.events[eventIndex]? with
      | none => program
      | some event =>
          match event.operation with
          | .semanticSimproc fold =>
              { program with events := program.events.set! eventIndex {
                  event with operation := .semanticSimproc (mutate fold) } }
          | _ => program

def mutateSemanticOuterEvent (program : Simp.Engine.Program)
    (mutate : Simp.Engine.Event → Simp.Engine.Event) : Simp.Engine.Program :=
  match Array.findIdx? isSemanticEvent program.events with
  | none => program
  | some eventIndex =>
      match program.events[eventIndex]? with
      | none => program
      | some event =>
          { program with events := program.events.set! eventIndex (mutate event) }

def mutateFinMkCandidate (program : Simp.Engine.Program)
    (mutate : FinMkCanonicalDerivation → FinMkCanonicalDerivation) :
    Simp.Engine.Program :=
  mutateSemanticCandidate program fun candidate =>
    match candidate.semantics with
    | .canonicalValue (.finMkCanonical derivation) =>
        { candidate with semantics :=
            .canonicalValue (.finMkCanonical (mutate derivation)) }
    | _ => candidate

def mutateFinMkTraceCandidate (program : Simp.Engine.Program)
    (mutate : NatEvalTrace → NatEvalTrace) : Simp.Engine.Program :=
  mutateFinMkCandidate program fun derivation =>
    { derivation with modulusTrace := mutate derivation.modulusTrace }

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
  let candidateMutations : Array (String × Simp.Engine.Program) := #[
    ("candidate declaration", mutateSemanticCandidate program fun candidate =>
      { candidate with declaration := `Nat.reduceAdd }),
    ("candidate procedure kind", mutateSemanticCandidate program fun candidate =>
      { candidate with procedureKind := .simp }),
    ("candidate set index", mutateSemanticCandidate program fun candidate =>
      { candidate with setIndex := 1 }),
    ("candidate registry provenance", mutateSemanticCandidate program fun candidate =>
      { candidate with registryPost := false }),
    ("candidate input fingerprint", mutateSemanticCandidate program fun candidate =>
      { candidate with inputFingerprint := "mutated" }),
    ("candidate peeled input fingerprint", mutateSemanticCandidate program fun candidate =>
      { candidate with peeledInputFingerprint := "mutated" }),
    ("candidate extra arguments", mutateSemanticCandidate program fun candidate =>
      { candidate with extraArgumentFingerprints := #["mutated"] }),
    ("candidate procedure output fingerprint", mutateSemanticCandidate program fun candidate =>
      { candidate with procedureOutputFingerprint := "mutated" }),
    ("candidate output fingerprint", mutateSemanticCandidate program fun candidate =>
      { candidate with outputFingerprint := "mutated" }),
    ("candidate extra argument count", mutateSemanticCandidate program fun candidate =>
      { candidate with numExtraArgs := candidate.numExtraArgs + 1 }),
    ("candidate disposition", mutateSemanticCandidate program fun candidate =>
      { candidate with disposition := .visit }),
    ("candidate proof fact", mutateSemanticCandidate program fun candidate =>
      { candidate with proofPresent := true }),
    ("candidate cache fact", mutateSemanticCandidate program fun candidate =>
      { candidate with cache := none }),
    ("candidate modulus", mutateFinMkCandidate program fun derivation =>
      { derivation with modulus := derivation.modulus + 1 }),
    ("candidate value", mutateFinMkCandidate program fun derivation =>
      { derivation with value := derivation.value + 1 }),
    ("candidate normalized", mutateFinMkCandidate program fun derivation =>
      { derivation with normalized := derivation.normalized + 1 }),
    ("candidate modulus path", mutateFinMkCandidate program fun derivation =>
      { derivation with modulusReference :=
          { derivation.modulusReference with path := #[] } }),
    ("candidate modulus fingerprint", mutateFinMkCandidate program fun derivation =>
      { derivation with modulusReference :=
          { derivation.modulusReference with fingerprint := "mutated" } }),
    ("candidate value view value", mutateFinMkCandidate program fun derivation =>
      { derivation with valueView := match derivation.valueView with
        | .raw reference value depth => .raw reference (value + 1) depth
        | .ofNat reference value depth witness => .ofNat reference (value + 1) depth witness }),
    ("candidate value view path", mutateFinMkCandidate program fun derivation =>
      { derivation with valueView := match derivation.valueView with
        | .raw reference value depth => .raw { reference with path := #[] } value depth
        | .ofNat reference value depth witness =>
            .ofNat { reference with path := #[] } value depth witness }),
    ("candidate value view fingerprint", mutateFinMkCandidate program fun derivation =>
      { derivation with valueView := match derivation.valueView with
        | .raw reference value depth => .raw { reference with fingerprint := "mutated" } value depth
        | .ofNat reference value depth witness =>
            .ofNat { reference with fingerprint := "mutated" } value depth witness }),
    ("candidate value view metadata", mutateFinMkCandidate program fun derivation =>
      { derivation with valueView := match derivation.valueView with
        | .raw reference value depth => .raw reference value (depth + 1)
        | .ofNat reference value depth witness => .ofNat reference value (depth + 1) witness }),
    ("candidate value view constructor", mutateFinMkCandidate program fun derivation =>
      { derivation with valueView := match derivation.valueView with
        | .raw reference value depth => .ofNat reference value depth default
        | .ofNat reference value depth _ => .raw reference value depth }),
    ("candidate trace raw field", mutateFinMkTraceCandidate program mutateTraceAtRaw),
    ("candidate trace OfNat field", mutateFinMkTraceCandidate program mutateTraceAtOfNatResult),
    ("fold phase", mutateSemanticFold program fun fold => { fold with phase := .pre }),
    ("fold candidates empty", mutateSemanticFold program fun fold =>
      { fold with candidates := #[] }),
    ("fold candidates duplicated", mutateSemanticFold program fun fold =>
      { fold with candidates := #[fold.candidates[0]!, fold.candidates[0]!] }),
    ("fold output fingerprint", mutateSemanticFold program fun fold =>
      { fold with finalOutputFingerprint := "mutated" }),
    ("fold disposition", mutateSemanticFold program fun fold =>
      { fold with finalDisposition := .visit }),
    ("fold proof fact", mutateSemanticFold program fun fold =>
      { fold with finalProofPresent := true }),
    ("fold cache fact", mutateSemanticFold program fun fold =>
      { fold with finalCache := none }),
    ("outer phase", mutateSemanticOuterEvent program fun event =>
      { event with phase := .pre }),
    ("outer input fingerprint", mutateSemanticOuterEvent program fun event =>
      { event with inputFingerprint := "mutated" }),
    ("outer output fingerprint", mutateSemanticOuterEvent program fun event =>
      { event with outputFingerprint := "mutated" }),
    ("outer disposition", mutateSemanticOuterEvent program fun event =>
      { event with stepDisposition := .visit }),
    ("outer invocation ordinal", mutateSemanticOuterEvent program fun event =>
      { event with invocationOrdinal := event.invocationOrdinal + 1 }),
    ("outer operation", mutateSemanticOuterEvent program fun event =>
      { event with operation := .builtin .decideTrue })]
  let mut rejected := 0
  for (label, mutation) in candidateMutations do
    rejected := rejected + (← expectReplayFailure label expression ctx config mutation trace)
  pure rejected

def checkFinMk : MetaM Unit := do
  checkNatEvalLeaves
  checkNatEvalBinaryForms
  checkNatEvalPowerForms
  checkUnsupportedShapes
  let expression ← finMkExpression (mkRawNatLit 5) (mkRawNatLit 2)
  let expected := finLiteral 5 2
  let some derivation ← deriveFinMkCanonical? `Fin.reduceFinMk expression expected
    | throwError "direct Fin.mk semantic derivation was not recognized"
  unless derivation.modulus == 5 && derivation.value == 2 && derivation.normalized == 2 do
    throwError "direct Fin.mk semantic scalar mismatch: {repr derivation}"
  let decoded : FinMkCanonicalDerivation ←
    match Lean.fromJson? (Lean.toJson derivation) with
    | .ok decoded => pure decoded
    | .error message => throwError "Fin.mk derivation JSON roundtrip failed: {message}"
  unless decoded == derivation do
    throwError "Fin.mk derivation JSON roundtrip changed the payload"
  let interpreted ← interpretFinMkCanonical expression derivation
  unless Expr.equal interpreted expected do
    throwError "direct Fin.mk interpretation did not build the expected literal"
  let (ordinaryProgram, ctx, config, ordinaryTrace) ←
    checkRecordedFold "ordinary" expression true
  let (_, _, _, _) ← checkRecordedFold "dsimp" expression false
  let traceMutations ← checkTraceMutations
  let replayMutations ← checkReplayMutations expression ctx config ordinaryProgram ordinaryTrace
  logInfo m!"FIN_MK_MUTATIONS rejected={traceMutations + replayMutations}"
  logInfo "FIN_MK_CANONICAL ordinary,dphase,trace,unsupported: ok"

elab "check_fin_mk" : tactic => withMainContext do
  checkFinMk

example : True := by
  check_fin_mk
  trivial

end FinMkCanonicalFoldProbe
