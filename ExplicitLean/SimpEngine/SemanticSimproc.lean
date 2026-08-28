module
prelude

public import ExplicitLean.SimpEngine.Fingerprint
import Lean.Meta.Offset
import Lean.Util.SafeExponentiation

public section

namespace Lean.Meta.Simp.Engine

/-!
  Small, deliberately syntactic semantic helpers used by the schema-27
  simproc payloads.  This module does not invoke a simproc and does not do
  elaboration or instance search.  In particular, all expression terms that
  are needed by a certificate are reconstructed from the restricted
  `DependencyTerm` grammar below.
-/

private def semanticError {α : Type} (message : String) : MetaM α :=
  throwError s!"semantic_simproc: {message}"

private def withRestoredMetaState (action : MetaM α) : MetaM α := do
  withRestoredFullMetaState action

/-- Structural expression equality modulo binder display names.

Binder names are annotations: bound-variable identity is represented by de Bruijn
indices, and the kernel ignores these names.  Qq may retain a hygienic source name
or emit the corresponding plain name depending on how an existential predicate
was produced.  Semantic proof validation therefore compares every constructor,
binder kind, type, body, level, identifier, literal, projection, and metadata
exactly while deliberately ignoring only `lam`, `forallE`, and `letE` names. -/
private def levelsEqualNormalized (lhs rhs : List Level) : Bool :=
  lhs.length == rhs.length &&
    (lhs.zip rhs).all fun (lhs, rhs) => lhs.normalize == rhs.normalize

partial def exprEqualIgnoringBinderNames (lhs rhs : Expr) : Bool :=
  match lhs, rhs with
  | .app lhsFn lhsArg, .app rhsFn rhsArg =>
      exprEqualIgnoringBinderNames lhsFn rhsFn &&
        exprEqualIgnoringBinderNames lhsArg rhsArg
  | .lam _ lhsType lhsBody lhsInfo, .lam _ rhsType rhsBody rhsInfo
  | .forallE _ lhsType lhsBody lhsInfo, .forallE _ rhsType rhsBody rhsInfo =>
      lhsInfo == rhsInfo &&
        exprEqualIgnoringBinderNames lhsType rhsType &&
        exprEqualIgnoringBinderNames lhsBody rhsBody
  | .letE _ lhsType lhsValue lhsBody lhsNondep,
      .letE _ rhsType rhsValue rhsBody rhsNondep =>
      lhsNondep == rhsNondep &&
        exprEqualIgnoringBinderNames lhsType rhsType &&
        exprEqualIgnoringBinderNames lhsValue rhsValue &&
        exprEqualIgnoringBinderNames lhsBody rhsBody
  | .mdata lhsData lhsBody, .mdata rhsData rhsBody =>
      lhsData == rhsData && exprEqualIgnoringBinderNames lhsBody rhsBody
  | .proj lhsName lhsIndex lhsBody, .proj rhsName rhsIndex rhsBody =>
      lhsName == rhsName && lhsIndex == rhsIndex &&
        exprEqualIgnoringBinderNames lhsBody rhsBody
  | .const lhsName lhsLevels, .const rhsName rhsLevels =>
      lhsName == rhsName && levelsEqualNormalized lhsLevels rhsLevels
  | .sort lhsLevel, .sort rhsLevel =>
      lhsLevel.normalize == rhsLevel.normalize
  | _, _ => Expr.equal lhs rhs

private def requireEqual (label : String) (expected actual : Expr) : MetaM Unit := do
  unless Expr.equal expected actual do
    semanticError s!"{label} expression mismatch"

private def requireStringEqual (label expected actual : String) : MetaM Unit := do
  unless expected == actual do
    semanticError s!"{label} fingerprint mismatch"

/-- Resolve one restricted path directly from an input expression.

  Every path step is checked against the expression constructor it consumes;
  no annotation cleanup, reduction, or elaboration is performed.  The final
  node is checked against the fingerprint carried by the reference. -/
def resolveInputSubterm (root : Expr) (reference : InputSubtermRef) : MetaM Expr := do
  let mut current := root
  let mut stepIndex := 0
  for step in reference.path do
    current ← match step, current with
      | .appFunction, .app function _ => pure function
      | .appArgument, .app _ argument => pure argument
      | .metadataBody, .mdata _ body => pure body
      | .lambdaType, .lam _ type _ _ => pure type
      | .lambdaBody, .lam _ _ body _ => pure body
      | .forallType, .forallE _ type _ _ => pure type
      | .forallBody, .forallE _ _ body _ => pure body
      | .letType, .letE _ type _ _ _ => pure type
      | .letValue, .letE _ _ value _ _ => pure value
      | .letBody, .letE _ _ _ body _ => pure body
      | _, expression =>
        semanticError s!"path step {stepIndex} ({repr step}) does not match {expression.ctorName}"
    stepIndex := stepIndex + 1
  let actualFingerprint ← exprFingerprintHash current
  requireStringEqual "input subterm" reference.fingerprint actualFingerprint
  return current

private def reconstructLevel : LevelDescriptor → Level
  | .zero => .zero
  | .succ level => .succ (reconstructLevel level)
  | .max lhs rhs => .max (reconstructLevel lhs) (reconstructLevel rhs)
  | .imax lhs rhs => .imax (reconstructLevel lhs) (reconstructLevel rhs)
  | .param name => .param name

private def reconstructLiteral : LiteralValue → Expr
  | .nat value => mkRawNatLit value
  | .int value => mkIntLit value
  | .bool value => mkConst (if value then ``Bool.true else ``Bool.false)
  | .string value => mkStrLit value

private def reconstructLocal (reference : LocalRef) : MetaM Expr := do
  let lctx ← getLCtx
  unless reference.binderDepth == lctx.numIndices do
    semanticError s!"local context depth mismatch for index {reference.contextIndex}"
  let some localDecl := lctx.getAt? reference.contextIndex
    | semanticError s!"local context index {reference.contextIndex} is not present"
  unless localDecl.index == reference.contextIndex do
    semanticError s!"local context index {reference.contextIndex} does not identify the stored declaration"
  let typeFingerprint ← exprFingerprintHash localDecl.type
  requireStringEqual "local type" reference.typeFingerprint typeFingerprint
  let valueFingerprint ← localDecl.value?.mapM exprFingerprintHash
  unless reference.valueFingerprint == valueFingerprint do
    semanticError s!"local value fingerprint mismatch for index {reference.contextIndex}"
  return mkFVar localDecl.fvarId

private partial def reconstructDependencyTermCore (root : Expr) : DependencyTerm → MetaM Expr
  | .input reference => resolveInputSubterm root reference
  | .local reference => reconstructLocal reference
  | .literal value => pure (reconstructLiteral value)
  | .application declaration levels arguments => do
      let info ←
        try getConstInfo declaration
        catch _ => semanticError s!"dependency declaration {declaration} is not present"
      unless levels.size == info.numLevelParams do
        semanticError s!"dependency declaration {declaration} has {info.numLevelParams} universe levels, got {levels.size}"
      let function := mkConst declaration (levels.toList.map reconstructLevel)
      let mut reconstructed := #[]
      for argument in arguments do
        reconstructed := reconstructed.push (← reconstructDependencyTermCore root argument)
      return mkAppN function reconstructed

/-- Reconstruct one restricted dependency term without elaboration or instance
  search.  The recursive implementation is intentionally private so callers
  cannot bypass the descriptor grammar. -/
def reconstructDependencyTerm (root : Expr) (term : DependencyTerm) : MetaM Expr :=
  reconstructDependencyTermCore root term

private def resolveAndValidateInstance (root : Expr) (witness : InstanceWitness) : MetaM Expr :=
  withRestoredMetaState do
    let instanceExpr ← reconstructDependencyTerm root witness.term
    let instanceType ←
      try inferType instanceExpr
      catch _ => semanticError "instance witness term has no inferable type"
    let typeFingerprint ← exprFingerprintHash instanceType
    requireStringEqual "instance type" witness.typeFingerprint typeFingerprint
    return instanceExpr

private def defEqRestored (lhs rhs : Expr) : MetaM Bool :=
  withRestoredMetaState do
    withReducibleAndInstances <| isDefEq lhs rhs

private def defEqCanonicalRestored (lhs rhs : Expr) : MetaM Bool :=
  withRestoredMetaState do
    withReducible <| isDefEq lhs rhs

private def defEqFinLiteralRestored (lhs rhs : Expr) : MetaM Bool :=
  withRestoredMetaState do
    withTransparency .all <| isDefEq lhs rhs

private def defEqIntLiteralRestored (lhs rhs : Expr) : MetaM Bool :=
  withRestoredMetaState do
    withTransparency .all <| isDefEq lhs rhs

private def stripMetadataExact (expression : Expr) (depth : Nat) : MetaM Expr :=
  match depth, expression with
  | 0, expression => pure expression
  | _ + 1, .mdata _ body => stripMetadataExact body (depth - 1)
  | _ + 1, expression =>
      semanticError s!"expected metadata while peeling Nat value, got {expression.ctorName}"

private def peelMetadata : Expr → Nat × Expr
  | .mdata _ body =>
      let (depth, expression) := peelMetadata body
      (depth + 1, expression)
  | expression => (0, expression)

private def requireNatType (label : String) (expression : Expr) : MetaM Unit := do
  requireEqual label Nat.mkType expression

private def requireConstLevels (label : String) (expression : Expr)
    (name : Name) (levels : List Level) : MetaM Unit := do
  let some actualName := expression.constName?
    | semanticError s!"{label} is not a constant"
  unless actualName == name do
    semanticError s!"{label} has declaration {actualName}, expected {name}"
  let actualLevels := expression.constLevels!
  unless actualLevels == levels do
    semanticError s!"{label} has unexpected universe levels"

private def strictOfNatParts (expression : Expr) : MetaM (Expr × Expr × Expr) := do
  unless expression.isAppOfArity ``OfNat.ofNat 3 do
    semanticError "Nat value is not a direct three-argument OfNat.ofNat application"
  let function := expression.getAppFn
  requireConstLevels "OfNat.ofNat" function ``OfNat.ofNat [.zero]
  let arguments := expression.getAppArgs
  unless arguments.size == 3 do
    semanticError "OfNat.ofNat does not have exactly three arguments"
  return (arguments[0]!, arguments[1]!, arguments[2]!)

private def strictNatBinaryParts (expression : Expr) (operator : NatBinaryOperator) :
    MetaM (Expr × Expr × Expr) := do
  if expression.hasMVar then
    semanticError "open or unassigned metavariable in Nat binary expression"
  unless expression.getAppNumArgs == 6 do
    semanticError "Nat binary expression does not have exactly six arguments"
  let function := expression.getAppFn
  let expectedName := match operator with
    | .add => ``HAdd.hAdd
    | .div => ``HDiv.hDiv
  requireConstLevels "Nat binary operator" function expectedName [.zero, .zero, .zero]
  let arguments := expression.getAppArgs
  unless arguments.size == 6 do
    semanticError "Nat binary expression does not have exactly six arguments"
  requireNatType "Nat binary lhs type" arguments[0]!
  requireNatType "Nat binary rhs type" arguments[1]!
  requireNatType "Nat binary result type" arguments[2]!
  return (arguments[3]!, arguments[4]!, arguments[5]!)

private def strictIntNegArgument (expression : Expr) : MetaM Expr := do
  if expression.hasMVar then
    semanticError "open or unassigned metavariable in Int negative expression"
  unless expression.isAppOfArity ``Neg.neg 3 do
    semanticError "Int negative expression does not have exactly three Neg.neg arguments"
  let function := expression.getAppFn
  requireConstLevels "Int negative operator" function ``Neg.neg [.zero]
  let arguments := expression.getAppArgs
  unless arguments.size == 3 do
    semanticError "Neg.neg does not have exactly three arguments"
  return arguments[2]!

private def strictIntNegParts (expression : Expr) : MetaM (Expr × Expr) := do
  let argument ← strictIntNegArgument expression
  let arguments := expression.getAppArgs
  requireEqual "Int negative type" (mkConst ``Int) arguments[0]!
  return (arguments[1]!, argument)

private def strictFinLiteralParts (expression : Expr) :
    MetaM (Expr × Expr × Expr × Expr) := do
  if expression.hasMVar then
    semanticError "open or unassigned metavariable in Fin literal"
  let (type, source, literalInstance) ← strictOfNatParts expression
  unless type.isAppOfArity ``Fin 1 do
    semanticError "Fin literal type is not a direct one-argument Fin application"
  let function := type.getAppFn
  requireConstLevels "Fin literal type" function ``Fin []
  let arguments := type.getAppArgs
  unless arguments.size == 1 do
    semanticError "Fin type does not have exactly one modulus argument"
  return (type, arguments[0]!, source, literalInstance)

private def metadataPath (depth : Nat) : Array ExprPathStep :=
  Array.replicate depth .metadataBody

private def arity3ArgumentPath (index : Nat) : Array ExprPathStep :=
  let functions : Array ExprPathStep := match index with
    | 0 => #[.appFunction, .appFunction]
    | 1 => #[.appFunction]
    | 2 => #[]
    | _ => #[]
  functions.push .appArgument

private def conditionalArgumentPath (index : Nat) : Array ExprPathStep :=
  let functions : Array ExprPathStep := match index with
    | 0 => #[.appFunction, .appFunction, .appFunction, .appFunction]
    | 1 => #[.appFunction, .appFunction, .appFunction]
    | 2 => #[.appFunction, .appFunction]
    | 3 => #[.appFunction]
    | 4 => #[]
    | _ => #[]
  functions.push .appArgument

private def binaryArgumentPath (index : Nat) : Array ExprPathStep :=
  let functions : Array ExprPathStep := match index with
    | 0 => #[.appFunction, .appFunction, .appFunction, .appFunction, .appFunction]
    | 1 => #[.appFunction, .appFunction, .appFunction, .appFunction]
    | 2 => #[.appFunction, .appFunction, .appFunction]
    | 3 => #[.appFunction, .appFunction]
    | 4 => #[.appFunction]
    | 5 => #[]
    | _ => #[]
  functions.push .appArgument

private def ofNatInstancePath (operandPath : Array ExprPathStep) (metadataDepth : Nat) :
    Array ExprPathStep :=
  operandPath ++ metadataPath metadataDepth ++
    #[.appArgument]

private def makeInputRef (expression : Expr) (path : Array ExprPathStep) :
    MetaM InputSubtermRef := do
  return { path, fingerprint := ← exprFingerprintHash expression }

private def makeInstanceWitness (_root expression : Expr) (path : Array ExprPathStep) :
    MetaM InstanceWitness := withRestoredMetaState do
  let reference ← makeInputRef expression path
  let expressionType ← inferType expression
  return {
    term := .input reference
    typeFingerprint := ← exprFingerprintHash expressionType
  }

private def validateStandardOfNatInstance (root : Expr)
    (numeral actualInstance : Expr) (witness : InstanceWitness) : MetaM Unit := do
  let resolvedInstance ← resolveAndValidateInstance root witness
  requireEqual "OfNat instance" actualInstance resolvedInstance
  unless ← defEqRestored actualInstance (mkInstOfNatNat numeral) do
    semanticError "OfNat instance is not definitionally the standard Nat instance"

private def interpretNatValueView (root actualOperand : Expr) (view : NatValueView) :
    MetaM Nat := do
  let reference := match view with
    | .raw reference .. => reference
    | .ofNat reference .. => reference
  let expression ← resolveInputSubterm root reference
  requireEqual "Nat value operand" actualOperand expression
  let metadataDepth := match view with
    | .raw _ _ depth => depth
    | .ofNat _ _ depth _ => depth
  let expression ← stripMetadataExact expression metadataDepth
  match view with
  | .raw _ value _ =>
      let .lit (.natVal actualValue) := expression
        | semanticError "raw Nat value is not a literal"
      unless actualValue == value do
        semanticError "raw Nat value does not match the derivation"
      return actualValue
  | .ofNat _ value _ witness =>
      let (type, numeral, actualInstance) ← strictOfNatParts expression
      requireNatType "OfNat Nat type" type
      let .lit (.natVal actualValue) := numeral
        | semanticError "OfNat numeral is not a direct raw Nat literal"
      unless actualValue == value do
        semanticError "OfNat numeral does not match the derivation"
      validateStandardOfNatInstance root numeral actualInstance witness
      return actualValue

private def natBinaryResult (operator : NatBinaryOperator) (lhs rhs : Nat) : Nat :=
  match operator with
  | .add => Nat.add lhs rhs
  | .div => if rhs == 0 then 0 else Nat.div lhs rhs

private def standardNatBinaryInstance (operator : NatBinaryOperator) : Expr :=
  match operator with
  | .add => Nat.mkInstHAdd
  | .div => Nat.mkInstHDiv

private def interpretNatBinaryCore (peeledInput : Expr)
    (derivation : NatBinaryDerivation) : MetaM Expr := do
  let (actualInstance, actualLhs, actualRhs) ←
    strictNatBinaryParts peeledInput derivation.operator
  let resolvedOperatorInstance ←
    resolveAndValidateInstance peeledInput derivation.operatorInstance
  requireEqual "Nat binary operator instance" actualInstance resolvedOperatorInstance
  unless ← defEqRestored actualInstance (standardNatBinaryInstance derivation.operator) do
    semanticError "Nat binary operator instance is not the standard Nat instance"
  let lhs ← interpretNatValueView peeledInput actualLhs derivation.lhsView
  let rhs ← interpretNatValueView peeledInput actualRhs derivation.rhsView
  unless lhs == derivation.lhs do
    semanticError "Nat binary lhs does not match the derivation"
  unless rhs == derivation.rhs do
    semanticError "Nat binary rhs does not match the derivation"
  let result := natBinaryResult derivation.operator lhs rhs
  unless result == derivation.result do
    semanticError "Nat binary result does not match the derivation"
  let canonical := mkNatLit result
  unless ← defEqCanonicalRestored canonical peeledInput do
    semanticError "canonical Nat result is not definitionally equal to the peeled input"
  return canonical

/-- Interpret a strict Nat binary semantic derivation without invoking a
  simproc, elaborating a term, or synthesizing an instance. -/
def interpretNatBinary (peeledInput : Expr) (derivation : NatBinaryDerivation) : MetaM Expr :=
  interpretNatBinaryCore peeledInput derivation

private def interpretIntNegOfNatSyntaxCore (peeledInput : Expr)
    (argument : InputSubtermRef) : MetaM Expr := do
  let actualArgument ← strictIntNegArgument peeledInput
  let _ ← strictOfNatParts actualArgument
  let resolvedArgument ← resolveInputSubterm peeledInput argument
  requireEqual "Int negative OfNat argument" actualArgument resolvedArgument
  return peeledInput

/-- Recheck the strict syntax guard used by `Int.reduceNeg`'s unchanged branch.
  The reference denotes the whole direct `OfNat.ofNat` argument and no integer
  value or arithmetic instance is reconstructed. -/
def interpretIntNegOfNatSyntax (peeledInput : Expr) (argument : InputSubtermRef) : MetaM Expr :=
  interpretIntNegOfNatSyntaxCore peeledInput argument

private def standardIntOfNatInstance (magnitude : Nat) : Expr :=
  mkApp (mkConst ``instOfNat) (mkRawNatLit magnitude)

private def validateIntInstance (root : Expr) (label : String) (actual expected : Expr)
    (witness : InstanceWitness) : MetaM Unit := do
  let resolved ← resolveAndValidateInstance root witness
  requireEqual label actual resolved
  unless ← defEqRestored actual expected do
    semanticError s!"{label} is not the pinned standard instance"

private def interpretIntNegateLiteralCore (peeledInput : Expr)
    (derivation : IntNegateLiteralDerivation) : MetaM Expr := do
  let (outerInstance, actualArgument) ← strictIntNegParts peeledInput
  unless derivation.argument.path == arity3ArgumentPath 2 do
    semanticError "Int negative argument path mismatch"
  let resolvedArgument ← resolveInputSubterm peeledInput derivation.argument
  requireEqual "Int negative argument" actualArgument resolvedArgument
  let (innerInstance, positiveLiteral) ← strictIntNegParts actualArgument
  let (literalType, numeralExpression, actualLiteralInstance) ←
    strictOfNatParts positiveLiteral
  requireEqual "Int literal type" (mkConst ``Int) literalType
  let numeralPath :=
    arity3ArgumentPath 2 ++ arity3ArgumentPath 2 ++ arity3ArgumentPath 1
  unless derivation.numeral.path == numeralPath do
    semanticError "Int magnitude numeral path mismatch"
  let resolvedNumeral ← resolveInputSubterm peeledInput derivation.numeral
  requireEqual "Int magnitude numeral" numeralExpression resolvedNumeral
  let strippedNumeral ←
    stripMetadataExact numeralExpression derivation.numeralMetadataDepth
  let .lit (.natVal magnitude) := strippedNumeral
    | semanticError "Int magnitude is not a raw Nat literal"
  unless magnitude == derivation.magnitude do
    semanticError "Int magnitude does not match the derivation"
  validateIntInstance peeledInput "outer Int Neg instance" outerInstance
    (mkConst ``Int.instNegInt) derivation.outerNegInstance
  validateIntInstance peeledInput "inner Int Neg instance" innerInstance
    (mkConst ``Int.instNegInt) derivation.innerNegInstance
  validateIntInstance peeledInput "Int OfNat instance" actualLiteralInstance
    (standardIntOfNatInstance magnitude) derivation.literalInstance
  let result : Int := Int.ofNat magnitude
  unless result == derivation.result do
    semanticError "Int negation result does not match the derivation"
  let canonical := toExpr result
  unless ← defEqIntLiteralRestored canonical peeledInput do
    semanticError "canonical Int result is not definitionally equal to the peeled input"
  return canonical

/-- Interpret the canonical double-negative branch of `Int.reduceNeg` from
  checked direct syntax and pinned instances. -/
def interpretIntNegateLiteral (peeledInput : Expr)
    (derivation : IntNegateLiteralDerivation) : MetaM Expr :=
  interpretIntNegateLiteralCore peeledInput derivation

private def natValueViewValue : NatValueView → Nat
  | .raw _ value _ => value
  | .ofNat _ value _ _ => value

private def natValueViewReference : NatValueView → InputSubtermRef
  | .raw reference .. => reference
  | .ofNat reference .. => reference

private def finNatValueExpression (value : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit value)
    (mkInstOfNatNat (mkRawNatLit value))

private def standardFinLiteralInstance (modulus source : Nat) : Expr :=
  let modulusExpr := finNatValueExpression modulus
  let sourceExpr := mkRawNatLit source
  mkApp3 (mkConst ``Fin.instOfNat []) modulusExpr
    (mkApp (mkConst ``Nat.instNeZeroSucc [])
      (finNatValueExpression (modulus - 1))) sourceExpr

private def canonicalFinLiteral (modulus normalized : Nat) : Expr :=
  let modulusExpr := finNatValueExpression modulus
  let sourceExpr := mkRawNatLit normalized
  let type := mkApp (mkConst ``Fin) modulusExpr
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) type sourceExpr
    (mkApp3 (mkConst ``Fin.instOfNat []) modulusExpr
      (mkApp (mkConst ``Nat.instNeZeroSucc [])
        (finNatValueExpression (modulus - 1))) sourceExpr)

private def requireFinLiteralViewPaths (modulusView sourceView : NatValueView) :
    MetaM Unit := do
  let expectedModulusPath := (arity3ArgumentPath 0).push .appArgument
  unless (natValueViewReference modulusView).path == expectedModulusPath do
    semanticError "Fin modulus view path mismatch"
  unless (natValueViewReference sourceView).path == arity3ArgumentPath 1 do
    semanticError "Fin source view path mismatch"

private def requireFinLiteralScalars (modulus source normalized : Nat)
    (modulusView sourceView : NatValueView) : MetaM Unit := do
  unless modulus == natValueViewValue modulusView do
    semanticError "Fin modulus does not match its view"
  unless source == natValueViewValue sourceView do
    semanticError "Fin source does not match its view"
  unless modulus > 0 do
    semanticError "Fin modulus is zero"
  unless normalized == source % modulus do
    semanticError "Fin normalized value does not match the modulus"

private def deriveRawNatView (expression : Expr) (path : Array ExprPathStep) :
    MetaM NatValueView := do
  let reference ← makeInputRef expression path
  let (metadataDepth, stripped) := peelMetadata expression
  let .lit (.natVal value) := stripped
    | semanticError "Fin source is not a raw Nat literal"
  return .raw reference value metadataDepth

private def interpretFinLiteralInRangeCore (peeledInput : Expr)
    (derivation : FinLiteralGuard) : MetaM Expr := do
  let (_, modulusExpression, sourceExpression, _) ← strictFinLiteralParts peeledInput
  requireFinLiteralViewPaths derivation.modulusView derivation.sourceView
  let modulus ← interpretNatValueView peeledInput modulusExpression derivation.modulusView
  let sourceView ← match derivation.sourceView with
    | .raw reference value metadataDepth => pure <| .raw reference value metadataDepth
    | .ofNat .. => semanticError "Fin source view is not raw"
  let source ← interpretNatValueView peeledInput sourceExpression sourceView
  requireFinLiteralScalars derivation.modulus derivation.source derivation.normalized
    derivation.modulusView sourceView
  unless derivation.source < derivation.modulus do
    semanticError "Fin in-range guard has an out-of-range source"
  unless modulus == derivation.modulus && source == derivation.source do
    semanticError "Fin literal guard scalar mismatch"
  return peeledInput

/-- Interpret the unchanged, in-range branch of `Fin.isValue` using only its
  checked direct syntax and Nat value views.  The outer OfNat instance is
  intentionally not reconstructed: the pinned branch ignores it. -/
def interpretFinLiteralInRange (peeledInput : Expr) (derivation : FinLiteralGuard) :
    MetaM Expr :=
  interpretFinLiteralInRangeCore peeledInput derivation

private def interpretFinLiteralModuloCore (peeledInput : Expr)
    (derivation : FinLiteralModuloDerivation) : MetaM Expr := do
  let (_, modulusExpression, sourceExpression, literalInstanceExpression) ←
    strictFinLiteralParts peeledInput
  requireFinLiteralViewPaths derivation.modulusView derivation.sourceView
  let modulus ← interpretNatValueView peeledInput modulusExpression derivation.modulusView
  let sourceView ← match derivation.sourceView with
    | .raw reference value metadataDepth => pure <| .raw reference value metadataDepth
    | .ofNat .. => semanticError "Fin source view is not raw"
  let source ← interpretNatValueView peeledInput sourceExpression sourceView
  requireFinLiteralScalars derivation.modulus derivation.source derivation.normalized
    derivation.modulusView sourceView
  unless derivation.modulus == modulus && derivation.source == source do
    semanticError "Fin literal modulo scalar mismatch"
  unless derivation.modulus ≤ derivation.source do
    semanticError "Fin modulo derivation has an in-range source"
  let reference ← match derivation.literalInstance.term with
    | .input reference => pure reference
    | _ => semanticError "Fin literal instance is not an input reference"
  unless reference.path == arity3ArgumentPath 2 do
    semanticError "Fin literal instance path mismatch"
  let resolvedInstance ← resolveAndValidateInstance peeledInput derivation.literalInstance
  requireEqual "Fin literal instance" literalInstanceExpression resolvedInstance
  let expectedInstance := standardFinLiteralInstance derivation.modulus derivation.source
  unless ← defEqRestored literalInstanceExpression expectedInstance do
    semanticError "Fin literal instance is not the standard Fin instance"
  let canonical := canonicalFinLiteral derivation.modulus derivation.normalized
  unless ← defEqFinLiteralRestored canonical peeledInput do
    semanticError "canonical Fin literal is not definitionally equal to the input"
  return canonical

/-- Interpret the modulo-normalizing branch of `Fin.isValue` without invoking
  a registry simproc or synthesizing any instances. -/
def interpretFinLiteralModulo (peeledInput : Expr)
    (derivation : FinLiteralModuloDerivation) : MetaM Expr :=
  interpretFinLiteralModuloCore peeledInput derivation

private def deriveNatValueView (root expression : Expr) (path : Array ExprPathStep) :
    MetaM NatValueView := do
  let reference ← makeInputRef expression path
  let (metadataDepth, stripped) := peelMetadata expression
  match stripped with
  | .lit (.natVal value) =>
      return .raw reference value metadataDepth
  | expression =>
      let (type, numeral, actualInstance) ← strictOfNatParts expression
      requireNatType "OfNat Nat type" type
      let .lit (.natVal value) := numeral
        | semanticError "OfNat numeral is not a direct raw Nat literal"
      let witness ← makeInstanceWitness root actualInstance
        (ofNatInstancePath path metadataDepth)
      validateStandardOfNatInstance root numeral actualInstance witness
      return .ofNat reference value metadataDepth witness

private def natEvalArgumentPath (arity index : Nat) : Array ExprPathStep :=
  (Array.replicate (arity - index - 1) .appFunction).push .appArgument

private structure NatEvalBinaryParts where
  operator : NatEvalBinaryOperator
  instance? : Option Expr
  instanceIndex : Option Nat
  lhs : Expr
  rhs : Expr
  arity : Nat

private structure NatEvalPowerParts where
  operator : NatEvalPowerOperator
  instance? : Option Expr
  instanceIndex : Option Nat
  base : Expr
  exponent : Expr
  arity : Nat

private def strictNatEvalApplication (expression : Expr) (name : Name)
    (levels : List Level) (arity : Nat) : MetaM (Array Expr) := do
  unless expression.isAppOfArity name arity do
    semanticError s!"Nat evaluator expression is not {name} with arity {arity}"
  requireConstLevels "Nat evaluator operator" expression.getAppFn name levels
  let arguments := expression.getAppArgs
  unless arguments.size == arity do
    semanticError "Nat evaluator operator has an unexpected arity"
  return arguments

private def strictNatEvalOverloadedBinary (expression : Expr) (name : Name)
    (levels : List Level) (operator : NatEvalBinaryOperator) (arity instanceIndex lhsIndex rhsIndex : Nat)
    (typeIndices : Array Nat) : MetaM NatEvalBinaryParts := do
  let arguments ← strictNatEvalApplication expression name levels arity
  for typeIndex in typeIndices do
    requireNatType "Nat evaluator operand type" arguments[typeIndex]!
  return {
    operator
    instance? := some arguments[instanceIndex]!
    instanceIndex := some instanceIndex
    lhs := arguments[lhsIndex]!
    rhs := arguments[rhsIndex]!
    arity
  }

private def natEvalBinaryParts (expression : Expr) : MetaM (Option NatEvalBinaryParts) := do
  let some name := expression.getAppFn.constName? | return none
  if name == `Nat.add then
    let arguments ← strictNatEvalApplication expression `Nat.add [] 2
    return some {
      operator := .natAdd
      instance? := none
      instanceIndex := none
      lhs := arguments[0]!
      rhs := arguments[1]!
      arity := 2
    }
  if name == `Add.add then
    return some <| ← strictNatEvalOverloadedBinary expression `Add.add [.zero] .add 4 1 2 3 #[0]
  if name == `HAdd.hAdd then
    return some <| ← strictNatEvalOverloadedBinary expression `HAdd.hAdd
      [.zero, .zero, .zero] .hAdd 6 3 4 5 #[0, 1, 2]
  if name == `Nat.sub then
    let arguments ← strictNatEvalApplication expression `Nat.sub [] 2
    return some {
      operator := .natSub
      instance? := none
      instanceIndex := none
      lhs := arguments[0]!
      rhs := arguments[1]!
      arity := 2
    }
  if name == `Sub.sub then
    return some <| ← strictNatEvalOverloadedBinary expression `Sub.sub [.zero] .sub 4 1 2 3 #[0]
  if name == `HSub.hSub then
    return some <| ← strictNatEvalOverloadedBinary expression `HSub.hSub
      [.zero, .zero, .zero] .hSub 6 3 4 5 #[0, 1, 2]
  if name == `Nat.mul then
    let arguments ← strictNatEvalApplication expression `Nat.mul [] 2
    return some {
      operator := .natMul
      instance? := none
      instanceIndex := none
      lhs := arguments[0]!
      rhs := arguments[1]!
      arity := 2
    }
  if name == `Mul.mul then
    return some <| ← strictNatEvalOverloadedBinary expression `Mul.mul [.zero] .mul 4 1 2 3 #[0]
  if name == `HMul.hMul then
    return some <| ← strictNatEvalOverloadedBinary expression `HMul.hMul
      [.zero, .zero, .zero] .hMul 6 3 4 5 #[0, 1, 2]
  if name == `Nat.div then
    let arguments ← strictNatEvalApplication expression `Nat.div [] 2
    return some {
      operator := .natDiv
      instance? := none
      instanceIndex := none
      lhs := arguments[0]!
      rhs := arguments[1]!
      arity := 2
    }
  if name == `Div.div then
    return some <| ← strictNatEvalOverloadedBinary expression `Div.div [.zero] .div 4 1 2 3 #[0]
  if name == `HDiv.hDiv then
    return some <| ← strictNatEvalOverloadedBinary expression `HDiv.hDiv
      [.zero, .zero, .zero] .hDiv 6 3 4 5 #[0, 1, 2]
  if name == `Nat.mod then
    let arguments ← strictNatEvalApplication expression `Nat.mod [] 2
    return some {
      operator := .natMod
      instance? := none
      instanceIndex := none
      lhs := arguments[0]!
      rhs := arguments[1]!
      arity := 2
    }
  if name == `Mod.mod then
    return some <| ← strictNatEvalOverloadedBinary expression `Mod.mod [.zero] .mod 4 1 2 3 #[0]
  if name == `HMod.hMod then
    return some <| ← strictNatEvalOverloadedBinary expression `HMod.hMod
      [.zero, .zero, .zero] .hMod 6 3 4 5 #[0, 1, 2]
  return none

private def strictNatEvalOverloadedPower (expression : Expr) (name : Name)
    (levels : List Level) (operator : NatEvalPowerOperator) (arity instanceIndex baseIndex exponentIndex : Nat)
    (typeIndices : Array Nat) : MetaM NatEvalPowerParts := do
  let arguments ← strictNatEvalApplication expression name levels arity
  for typeIndex in typeIndices do
    requireNatType "Nat evaluator power type" arguments[typeIndex]!
  return {
    operator
    instance? := some arguments[instanceIndex]!
    instanceIndex := some instanceIndex
    base := arguments[baseIndex]!
    exponent := arguments[exponentIndex]!
    arity
  }

private def natEvalPowerParts (expression : Expr) : MetaM (Option NatEvalPowerParts) := do
  let some name := expression.getAppFn.constName? | return none
  if name == `Nat.pow then
    let arguments ← strictNatEvalApplication expression `Nat.pow [] 2
    return some {
      operator := .natPow
      instance? := none
      instanceIndex := none
      base := arguments[0]!
      exponent := arguments[1]!
      arity := 2
    }
  if name == `NatPow.pow then
    return some <| ← strictNatEvalOverloadedPower expression `NatPow.pow [.zero]
      .natPowClass 4 1 2 3 #[0]
  if name == `Pow.pow then
    return some <| ← strictNatEvalOverloadedPower expression `Pow.pow [.zero, .zero]
      .pow 5 2 3 4 #[0, 1]
  if name == `HPow.hPow then
    return some <| ← strictNatEvalOverloadedPower expression `HPow.hPow
      [.zero, .zero, .zero] .hPow 6 3 4 5 #[0, 1, 2]
  return none

private def natEvalBinaryStandardInstance : NatEvalBinaryOperator → Expr
  | .natAdd | .add => Nat.mkInstAdd
  | .hAdd => Nat.mkInstHAdd
  | .natSub | .sub => Nat.mkInstSub
  | .hSub => Nat.mkInstHSub
  | .natMul | .mul => Nat.mkInstMul
  | .hMul => Nat.mkInstHMul
  | .natDiv | .div => Nat.mkInstDiv
  | .hDiv => Nat.mkInstHDiv
  | .natMod | .mod => Nat.mkInstMod
  | .hMod => Nat.mkInstHMod

private def natEvalPowerStandardInstance : NatEvalPowerOperator → Expr
  | .natPow | .natPowClass => Nat.mkInstNatPow
  | .pow => Nat.mkInstPow
  | .hPow => Nat.mkInstHPow

private def natEvalBinaryValue (operator : NatEvalBinaryOperator) (lhs rhs : Nat) : Nat :=
  match operator with
  | .natAdd | .add | .hAdd => lhs + rhs
  | .natSub | .sub | .hSub => lhs - rhs
  | .natMul | .mul | .hMul => lhs * rhs
  | .natDiv | .div | .hDiv => lhs / rhs
  | .natMod | .mod | .hMod => lhs % rhs

private def natEvalPowerValue (base exponent : Nat) : Nat := base ^ exponent

private def makeNatEvalInstanceWitness (root actual : Expr)
    (path : Array ExprPathStep) : MetaM InstanceWitness := do
  let witness ← makeInstanceWitness root actual path
  let .input reference := witness.term
    | semanticError "Nat evaluator instance witness is not input-backed"
  let resolved ← resolveInputSubterm root reference
  requireEqual "Nat evaluator instance reference" actual resolved
  return witness

private def validateNatEvalInstance (root actual expected : Expr)
    (path : Array ExprPathStep) (witness : InstanceWitness) : MetaM Unit := do
  let .input reference := witness.term
    | semanticError "Nat evaluator instance witness is not input-backed"
  unless reference.path == path do
    semanticError "Nat evaluator instance witness path mismatch"
  let resolved ← resolveAndValidateInstance root witness
  requireEqual "Nat evaluator instance" actual resolved
  unless ← defEqRestored actual expected do
    semanticError "Nat evaluator instance is not the pinned standard instance"

private def makeNatEvalOptionalInstance (root : Expr) (path : Array ExprPathStep)
    (actual? : Option Expr) (expected : Expr) : MetaM (Option InstanceWitness) := do
  match actual? with
  | none => return none
  | some actual =>
      let witness ← makeNatEvalInstanceWitness root actual path
      validateNatEvalInstance root actual expected path witness
      return some witness

private partial def deriveNatEvalTraceCore (root expression : Expr)
    (path : Array ExprPathStep) : MetaM (NatEvalTrace × Nat) := do
  if expression.isMVar then
    let assigned ← instantiateMVars expression
    unless !assigned.isMVar && !Expr.equal assigned expression do
      semanticError "Nat evaluator metavariable is unassigned"
    let (body, value) ← deriveNatEvalTraceCore root assigned path
    return (.assigned (← exprFingerprintHash assigned) value body, value)
  match expression with
  | .lit (.natVal value) => return (.raw value, value)
  | .mdata _ body =>
      let (trace, value) ← deriveNatEvalTraceCore root body (path.push .metadataBody)
      return (.metadata trace, value)
  | .const name levels =>
      unless name == `Nat.zero && levels.isEmpty do
        semanticError "Nat evaluator constant is not Nat.zero"
      return (.zero, 0)
  | .app .. =>
      if let some parts ← natEvalBinaryParts expression then
        let lhsPath := path ++ natEvalArgumentPath parts.arity (parts.arity - 2)
        let rhsPath := path ++ natEvalArgumentPath parts.arity (parts.arity - 1)
        let instance? ← match parts.instance?, parts.instanceIndex with
          | none, none => pure none
          | some actual, some index =>
              makeNatEvalOptionalInstance root (path ++ natEvalArgumentPath parts.arity index)
                (some actual) (natEvalBinaryStandardInstance parts.operator)
          | _, _ => semanticError "Nat evaluator binary instance shape mismatch"
        let (lhsTrace, lhs) ← deriveNatEvalTraceCore root parts.lhs lhsPath
        let (rhsTrace, rhs) ← deriveNatEvalTraceCore root parts.rhs rhsPath
        let result := natEvalBinaryValue parts.operator lhs rhs
        return (.binary parts.operator instance? lhsTrace rhsTrace result, result)
      if let some parts ← natEvalPowerParts expression then
        let exponentPath := path ++ natEvalArgumentPath parts.arity (parts.arity - 1)
        let (exponentTrace, exponent) ←
          deriveNatEvalTraceCore root parts.exponent exponentPath
        let threshold := exponentiation.threshold.get (← getOptions)
        unless exponent ≤ threshold do
          semanticError "Nat evaluator exponent exceeds the active threshold"
        let basePath := path ++ natEvalArgumentPath parts.arity (parts.arity - 2)
        let (baseTrace, base) ← deriveNatEvalTraceCore root parts.base basePath
        let instance? ← match parts.instance?, parts.instanceIndex with
          | none, none => pure none
          | some actual, some index =>
              makeNatEvalOptionalInstance root (path ++ natEvalArgumentPath parts.arity index)
                (some actual) (natEvalPowerStandardInstance parts.operator)
          | _, _ => semanticError "Nat evaluator power instance shape mismatch"
        let result := natEvalPowerValue base exponent
        return (.power parts.operator instance? baseTrace exponentTrace threshold result, result)
      if expression.isAppOfArity ``Nat.succ 1 then
        let _ ← strictNatEvalApplication expression `Nat.succ [] 1
        let argumentPath := path ++ natEvalArgumentPath 1 0
        let (trace, value) ← deriveNatEvalTraceCore root expression.appArg! argumentPath
        let result := value + 1
        return (.succ trace result, result)
      if expression.isAppOfArity ``OfNat.ofNat 3 then
        let (type, numeral, actualInstance) ← strictOfNatParts expression
        requireNatType "Nat evaluator OfNat type" type
        let numeralPath := path ++ natEvalArgumentPath 3 1
        let (trace, value) ← deriveNatEvalTraceCore root numeral numeralPath
        let instancePath := path ++ natEvalArgumentPath 3 2
        let witness ← makeNatEvalInstanceWitness root actualInstance instancePath
        validateStandardOfNatInstance root numeral actualInstance witness
        return (.ofNat witness trace value, value)
      semanticError "Nat evaluator application has an unsupported shape"
  | _ => semanticError "Nat evaluator expression has an unsupported shape"

private partial def interpretNatEvalTraceCore (root expression : Expr)
    (path : Array ExprPathStep) (trace : NatEvalTrace) : MetaM Nat := do
  match trace, expression with
  | .raw expected, .lit (.natVal actual) => do
      unless expected == actual do semanticError "Nat evaluator raw value mismatch"
      return actual
  | .metadata body, .mdata _ actualBody =>
      interpretNatEvalTraceCore root actualBody (path.push .metadataBody) body
  | .zero, .const name levels => do
      unless name == `Nat.zero && levels.isEmpty do
        semanticError "Nat evaluator Nat.zero mismatch"
      return 0
  | .assigned assignmentFingerprint expectedValue body, .mvar .. => do
      let assigned ← instantiateMVars expression
      unless !assigned.isMVar && !Expr.equal assigned expression do
        semanticError "Nat evaluator assigned metavariable mismatch"
      let actualFingerprint ← exprFingerprintHash assigned
      requireStringEqual "Nat evaluator assignment" assignmentFingerprint actualFingerprint
      let actualValue ← interpretNatEvalTraceCore root assigned path body
      unless actualValue == expectedValue do
        semanticError "Nat evaluator assigned value mismatch"
      return actualValue
  | .ofNat witness body expectedResult, _ => do
      let (type, numeral, actualInstance) ← strictOfNatParts expression
      requireNatType "Nat evaluator OfNat type" type
      let numeralPath := path ++ natEvalArgumentPath 3 1
      let actualValue ← interpretNatEvalTraceCore root numeral numeralPath body
      let instancePath := path ++ natEvalArgumentPath 3 2
      validateNatEvalInstance root actualInstance (mkInstOfNatNat numeral)
        instancePath witness
      unless expectedResult == actualValue do
        semanticError "Nat evaluator OfNat result mismatch"
      return actualValue
  | .succ body expectedResult, _ => do
      let _ ← strictNatEvalApplication expression `Nat.succ [] 1
      let actualValue ← interpretNatEvalTraceCore root expression.appArg!
        (path ++ natEvalArgumentPath 1 0) body
      unless expectedResult == actualValue + 1 do
        semanticError "Nat evaluator successor result mismatch"
      return actualValue + 1
  | .binary expectedOperator expectedInstance lhsTrace rhsTrace expectedResult, _ => do
      let some parts ← natEvalBinaryParts expression
        | semanticError "Nat evaluator binary expression mismatch"
      unless parts.operator == expectedOperator do
        semanticError "Nat evaluator binary operator mismatch"
      match parts.instance?, expectedInstance, parts.instanceIndex with
      | none, none, none => pure ()
      | some actual, some witness, some index =>
          validateNatEvalInstance root actual (natEvalBinaryStandardInstance expectedOperator)
            (path ++ natEvalArgumentPath parts.arity index) witness
      | _, _, _ => semanticError "Nat evaluator binary instance presence mismatch"
      let lhs ← interpretNatEvalTraceCore root parts.lhs
        (path ++ natEvalArgumentPath parts.arity (parts.arity - 2)) lhsTrace
      let rhs ← interpretNatEvalTraceCore root parts.rhs
        (path ++ natEvalArgumentPath parts.arity (parts.arity - 1)) rhsTrace
      let result := natEvalBinaryValue expectedOperator lhs rhs
      unless expectedResult == result do
        semanticError "Nat evaluator binary result mismatch"
      return result
  | .power expectedOperator expectedInstance baseTrace exponentTrace threshold expectedResult, _ => do
      let some parts ← natEvalPowerParts expression
        | semanticError "Nat evaluator power expression mismatch"
      unless parts.operator == expectedOperator do
        semanticError "Nat evaluator power operator mismatch"
      match parts.instance?, expectedInstance, parts.instanceIndex with
      | none, none, none => pure ()
      | some actual, some witness, some index =>
          validateNatEvalInstance root actual (natEvalPowerStandardInstance expectedOperator)
            (path ++ natEvalArgumentPath parts.arity index) witness
      | _, _, _ => semanticError "Nat evaluator power instance presence mismatch"
      let exponent ← interpretNatEvalTraceCore root parts.exponent
        (path ++ natEvalArgumentPath parts.arity (parts.arity - 1)) exponentTrace
      unless exponent ≤ threshold do
        semanticError "Nat evaluator exponent exceeds recorded threshold"
      let base ← interpretNatEvalTraceCore root parts.base
        (path ++ natEvalArgumentPath parts.arity (parts.arity - 2)) baseTrace
      let result := natEvalPowerValue base exponent
      unless expectedResult == result do
        semanticError "Nat evaluator power result mismatch"
      return result
  | _, _ => semanticError "Nat evaluator trace does not match the input expression"

private def natOffsetOperator? : NatEvalBinaryOperator → Option NatOffsetOperator
  | .natAdd => some .natAdd
  | .add => some .add
  | .hAdd => some .hAdd
  | _ => none

private def natOffsetStandardInstance (operator : NatOffsetOperator) : Expr :=
  match operator with
  | .natAdd => Nat.mkInstAdd
  | .add => Nat.mkInstAdd
  | .hAdd => Nat.mkInstHAdd

private def natOffsetBinaryOperator (operator : NatOffsetOperator) : NatEvalBinaryOperator :=
  match operator with
  | .natAdd => .natAdd
  | .add => .add
  | .hAdd => .hAdd

private partial def deriveNatOffsetTraceCore (root expression : Expr)
    (path : Array ExprPathStep) : MetaM (Option (NatOffsetTrace × Nat)) := do
  if let some name := expression.getAppFn.constName? then
    if name == `Nat.succ then
      let arguments ← strictNatEvalApplication expression `Nat.succ [] 1
      requireNatType "Nat offset successor argument type" (← inferType arguments[0]!)
      let argumentPath := path ++ natEvalArgumentPath 1 0
      let (trace, offset) ← match ← deriveNatOffsetTraceCore root arguments[0]! argumentPath with
        | some result => pure result
        | none =>
            pure (.base (← makeInputRef arguments[0]! argumentPath), 0)
      return some (.succ trace, offset + 1)
  if let some parts ← natEvalBinaryParts expression then
    let some operator := natOffsetOperator? parts.operator
      | return none
    let lhsPath := path ++ natEvalArgumentPath parts.arity (parts.arity - 2)
    let rhsPath := path ++ natEvalArgumentPath parts.arity (parts.arity - 1)
    let (rhsTrace, rhs) ← deriveNatEvalTraceCore root parts.rhs rhsPath
    let (lhsTrace, lhsOffset) ← match ← deriveNatOffsetTraceCore root parts.lhs lhsPath with
      | some result => pure result
      | none => pure (.base (← makeInputRef parts.lhs lhsPath), 0)
    let instance? ← match parts.instance?, parts.instanceIndex with
      | none, none => pure none
      | some actual, some index =>
          makeNatEvalOptionalInstance root (path ++ natEvalArgumentPath parts.arity index)
            (some actual) (natOffsetStandardInstance operator)
      | _, _ => semanticError "Nat offset binary instance shape mismatch"
    return some (.add operator instance? lhsTrace rhsTrace, lhsOffset + rhs)
  return none

private partial def interpretNatOffsetTraceCore (root expression : Expr)
    (path : Array ExprPathStep) : NatOffsetTrace → MetaM Nat
  | .base reference => do
      unless reference.path == path do
        semanticError "Nat offset base reference path mismatch"
      let resolved ← resolveInputSubterm root reference
      requireEqual "Nat offset base" expression resolved
      return 0
  | .succ trace => do
      let arguments ← strictNatEvalApplication expression `Nat.succ [] 1
      requireNatType "Nat offset successor argument type" (← inferType arguments[0]!)
      let argumentPath := path ++ natEvalArgumentPath 1 0
      return (← interpretNatOffsetTraceCore root arguments[0]! argumentPath trace) + 1
  | .add expectedOperator expectedInstance lhsTrace rhsTrace => do
      let some parts ← natEvalBinaryParts expression
        | semanticError "Nat offset binary expression mismatch"
      let some actualOperator := natOffsetOperator? parts.operator
        | semanticError "Nat offset binary operator is not addition"
      unless actualOperator == expectedOperator do
        semanticError "Nat offset binary operator mismatch"
      match parts.instance?, expectedInstance, parts.instanceIndex with
      | none, none, none => pure ()
      | some actual, some witness, some index =>
          validateNatEvalInstance root actual (natOffsetStandardInstance expectedOperator)
            (path ++ natEvalArgumentPath parts.arity index) witness
      | _, _, _ => semanticError "Nat offset binary instance presence mismatch"
      let lhs ← interpretNatOffsetTraceCore root parts.lhs
        (path ++ natEvalArgumentPath parts.arity (parts.arity - 2)) lhsTrace
      let rhs ← interpretNatEvalTraceCore root parts.rhs
        (path ++ natEvalArgumentPath parts.arity (parts.arity - 1)) rhsTrace
      return lhs + rhs

private def strictEqParts (expression : Expr) : MetaM (Expr × Expr × Expr) := do
  unless expression.isAppOfArity ``Eq 3 do
    semanticError "constructor equality is not a direct three-argument Eq application"
  let function := expression.getAppFn
  let .const name levels := function
    | semanticError "constructor equality head is not a constant"
  unless name == ``Eq && levels.length == 1 do
    semanticError "constructor equality has an unexpected Eq head"
  let arguments := expression.getAppArgs
  unless arguments.size == 3 do
    semanticError "constructor equality does not have exactly three arguments"
  return (arguments[0]!, arguments[1]!, arguments[2]!)

private def directInductiveInfo (type : Expr) : MetaM (Name × InductiveVal) := do
  let .const inductiveName levels := type.getAppFn
    | semanticError "constructor equality type is not a direct constant-headed inductive"
  let .inductInfo info ← getConstInfo inductiveName
    | semanticError "constructor equality type head is not an inductive declaration"
  unless levels.length == info.levelParams.length do
    semanticError "constructor equality type has an unexpected universe arity"
  return (inductiveName, info)

private def constructorInfo (name : Name) : MetaM ConstructorVal := do
  let .ctorInfo info ← getConstInfo name
    | semanticError s!"{name} is not a constructor declaration"
  return info

private def validateConstructorMetadata (inductiveName : Name)
    (view : ConstructorView) : MetaM ConstructorVal := do
  unless view.inductiveName == inductiveName do
    semanticError "constructor view inductive mismatch"
  let info ← constructorInfo view.constructor
  unless info.name == view.constructor && info.induct == inductiveName &&
      info.cidx == view.constructorIndex do
    semanticError "constructor view metadata mismatch"
  return info

private def deriveImmediateConstructorView (_root operand : Expr)
    (operandPath : Array ExprPathStep) (inductiveName : Name) : MetaM ConstructorView := do
  let .const constructorName levels := operand.getAppFn
    | semanticError "immediate constructor head is not a constant"
  let info ← constructorInfo constructorName
  unless levels.length == info.levelParams.length do
    semanticError "immediate constructor has an unexpected universe arity"
  unless info.induct == inductiveName do
    semanticError "immediate constructor belongs to a different inductive"
  let arity := info.numParams + info.numFields
  unless operand.getAppNumArgs == arity do
    semanticError "immediate constructor is not fully applied"
  let arguments := operand.getAppArgs
  unless arguments.size == arity do
    semanticError "immediate constructor argument count mismatch"
  let mut references : Array InputSubtermRef := #[]
  for index in *...arguments.size do
    references := references.push <| ← makeInputRef arguments[index]!
      (operandPath ++ natEvalArgumentPath arity index)
  return {
    operand := ← makeInputRef operand operandPath
    constructor := info.name
    inductiveName := info.induct
    constructorIndex := info.cidx
    origin := .immediate references
  }

private def deriveNatLiteralConstructorView (root operand : Expr)
    (operandPath : Array ExprPathStep) (inductiveName : Name) : MetaM (Option ConstructorView) := do
  unless inductiveName == `Nat do
    return none
  try
    let valueView ← deriveNatValueView root operand operandPath
    let value := natValueViewValue valueView
    let constructor := if value == 0 then `Nat.zero else `Nat.succ
    let info ← constructorInfo constructor
    return some {
      operand := ← makeInputRef operand operandPath
      constructor := info.name
      inductiveName := info.induct
      constructorIndex := info.cidx
      origin := .natLiteral valueView
    }
  catch _ =>
    return none

private def deriveConstructorView (root operand : Expr)
    (operandPath : Array ExprPathStep) (inductiveName : Name) : MetaM ConstructorView := do
  if let some (trace, offset) ← deriveNatOffsetTraceCore root operand operandPath then
    if offset > 0 then
      unless inductiveName == `Nat do
        semanticError "Nat offset constructor has a non-Nat equality type"
      let info ← constructorInfo `Nat.succ
      return {
        operand := ← makeInputRef operand operandPath
        constructor := info.name
        inductiveName := info.induct
        constructorIndex := info.cidx
        origin := .natOffset trace offset
      }
  if let some view ← deriveNatLiteralConstructorView root operand operandPath inductiveName then
    return view
  deriveImmediateConstructorView root operand operandPath inductiveName

private def interpretImmediateConstructorView (root operand : Expr)
    (operandPath : Array ExprPathStep) (view : ConstructorView) (info : ConstructorVal) :
    MetaM Unit := do
  unless view.constructor != `Nat.succ do
    semanticError "Nat successor must be represented by a positive Nat offset"
  let .const name levels := operand.getAppFn
    | semanticError "immediate constructor head is not a constant"
  unless name == view.constructor && levels.length == info.levelParams.length do
    semanticError "immediate constructor head mismatch"
  let arity := info.numParams + info.numFields
  unless operand.getAppNumArgs == arity do
    semanticError "immediate constructor is not fully applied"
  let arguments := operand.getAppArgs
  let references ← match view.origin with
    | .immediate references => pure references
    | _ => semanticError "immediate constructor origin mismatch"
  unless references.size == arity do
    semanticError "immediate constructor reference count mismatch"
  for index in *...arguments.size do
    let reference := references[index]!
    let expectedPath := operandPath ++ natEvalArgumentPath arity index
    unless reference.path == expectedPath do
      semanticError "immediate constructor argument path mismatch"
    let resolved ← resolveInputSubterm root reference
    requireEqual "immediate constructor argument" arguments[index]! resolved

private def interpretConstructorView (root operand : Expr) (operandPath : Array ExprPathStep)
    (inductiveName : Name) (view : ConstructorView) : MetaM Unit := do
  unless view.operand.path == operandPath do
    semanticError "constructor view operand path mismatch"
  let resolvedOperand ← resolveInputSubterm root view.operand
  requireEqual "constructor view operand" operand resolvedOperand
  let info ← validateConstructorMetadata inductiveName view
  match view.origin with
  | .immediate _ =>
      interpretImmediateConstructorView root operand operandPath view info
  | .natLiteral valueView => do
      unless inductiveName == `Nat do
        semanticError "Nat literal constructor has a non-Nat equality type"
      let value ← interpretNatValueView root operand valueView
      let expectedConstructor := if value == 0 then `Nat.zero else `Nat.succ
      unless view.constructor == expectedConstructor do
        semanticError "Nat literal constructor mismatch"
      unless view.constructorIndex == info.cidx do
        semanticError "Nat literal constructor index mismatch"
  | .natOffset trace expectedOffset => do
      unless inductiveName == `Nat && view.constructor == `Nat.succ &&
          view.constructorIndex == info.cidx && expectedOffset > 0 do
        semanticError "Nat offset constructor metadata mismatch"
      let actualOffset ← interpretNatOffsetTraceCore root operand operandPath trace
      unless actualOffset == expectedOffset && actualOffset > 0 do
        semanticError "Nat offset constructor value mismatch"

private def constructorIdxName (inductiveName : Name) : Name :=
  inductiveName.str "ctorIdx"

private def mkConstructorDisjointProof (e type lhs rhs : Expr)
    (ctorIdxDeclaration noConfusionDeclaration eqFalseDeclaration : Name) :
    MetaM Expr := do
  let inductiveLevels := type.getAppFn.constLevels!
  let ctorIdx := mkAppN (mkConst ctorIdxDeclaration inductiveLevels) type.getAppArgs
  let typeLevel ← getLevel type
  withLocalDeclD `h e fun h => do
    let noConfusion := mkAppN (mkConst noConfusionDeclaration [typeLevel])
      #[type, ctorIdx, lhs, rhs, h]
    let contradiction := mkApp2 (mkConst ``False.elim [Level.zero])
      (mkConst ``False) noConfusion
    let notEquality ← mkLambdaFVars #[h] contradiction
    let proof := mkApp2 (mkConst eqFalseDeclaration) e notEquality
    return proof

private def interpretConstructorDisjointCore (peeledInput : Expr)
    (witness : ConstructorDisjointWitness) : MetaM Simp.Result := do
  let (type, lhs, rhs) ← strictEqParts peeledInput
  unless witness.typeReference.path == arity3ArgumentPath 0 do
    semanticError "constructor equality type reference path mismatch"
  let resolvedType ← resolveInputSubterm peeledInput witness.typeReference
  requireEqual "constructor equality type reference" type resolvedType
  let (inductiveName, _) ← directInductiveInfo type
  unless witness.inductiveName == inductiveName do
    semanticError "constructor equality inductive mismatch"
  interpretConstructorView peeledInput lhs (arity3ArgumentPath 1) inductiveName witness.lhs
  interpretConstructorView peeledInput rhs (arity3ArgumentPath 2) inductiveName witness.rhs
  unless witness.lhs.constructor != witness.rhs.constructor &&
      witness.lhs.constructorIndex != witness.rhs.constructorIndex do
    semanticError "constructor equality views are not disjoint"
  let expectedCtorIdx := constructorIdxName inductiveName
  unless witness.ctorIdxDeclaration == expectedCtorIdx do
    semanticError "constructor equality ctorIdx declaration mismatch"
  unless witness.noConfusionDeclaration == ``noConfusion_of_Nat do
    semanticError "constructor equality no-confusion declaration mismatch"
  unless witness.eqFalseDeclaration == ``eq_false' do
    semanticError "constructor equality eq-false declaration mismatch"
  let _ ← getConstInfo witness.ctorIdxDeclaration
  let _ ← getConstInfo witness.noConfusionDeclaration
  let _ ← getConstInfo witness.eqFalseDeclaration
  let proof ← mkConstructorDisjointProof peeledInput type lhs rhs
    witness.ctorIdxDeclaration witness.noConfusionDeclaration witness.eqFalseDeclaration
  let falseExpression := mkConst ``False
  let proofType ← inferType proof
  let expectedProofType ← mkEq peeledInput falseExpression
  unless ← defEqRestored proofType expectedProofType do
    semanticError "constructor equality proof has an unexpected type"
  return { expr := falseExpression, proof? := some proof, cache := true }

def interpretConstructorDisjoint (peeledInput : Expr)
    (witness : ConstructorDisjointWitness) : MetaM Simp.Result :=
  interpretConstructorDisjointCore peeledInput witness

private def deriveConstructorDisjointCore (declaration : Name)
    (peeledInput procedureOutput : Expr) : MetaM (Option ConstructorDisjointWitness) := do
  unless declaration == `reduceCtorEq do
    return none
  unless Expr.equal procedureOutput (mkConst ``False) do
    return none
  if peeledInput.hasMVar || procedureOutput.hasMVar then
    return none
  let (type, lhs, rhs) ← strictEqParts peeledInput
  let (inductiveName, _) ← directInductiveInfo type
  let typeReference ← makeInputRef type (arity3ArgumentPath 0)
  let lhsView ← deriveConstructorView peeledInput lhs (arity3ArgumentPath 1) inductiveName
  let rhsView ← deriveConstructorView peeledInput rhs (arity3ArgumentPath 2) inductiveName
  unless lhsView.constructor != rhsView.constructor &&
      lhsView.constructorIndex != rhsView.constructorIndex do
    return none
  let witness : ConstructorDisjointWitness := {
    typeReference
    inductiveName := inductiveName
    lhs := lhsView
    rhs := rhsView
    ctorIdxDeclaration := constructorIdxName inductiveName
    noConfusionDeclaration := ``noConfusion_of_Nat
    eqFalseDeclaration := ``eq_false'
  }
  let interpreted ← interpretConstructorDisjoint peeledInput witness
  unless Expr.equal interpreted.expr procedureOutput && interpreted.proof?.isSome do
    return none
  return some witness

/-- Recognize the direct, literal, and positive-Nat-offset distinct-constructor
  branch of `reduceCtorEq`.  Recognition is fully replayable and performs no
  WHNF, literal conversion, offset recognizer, or simproc calls. -/
def deriveConstructorDisjoint? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option ConstructorDisjointWitness) := do
  try
    withRestoredMetaState <| deriveConstructorDisjointCore declaration peeledInput procedureOutput
  catch _ =>
    return none

private def strictFinMkParts (expression : Expr) : MetaM (Expr × Expr × Expr) := do
  let arguments ← strictNatEvalApplication expression `Fin.mk [] 3
  requireNatType "Fin.mk modulus type" (← inferType arguments[0]!)
  return (arguments[0]!, arguments[1]!, arguments[2]!)

private def interpretFinMkCanonicalCore (peeledInput : Expr)
    (derivation : FinMkCanonicalDerivation) : MetaM Expr := do
  let (modulusExpression, valueExpression, _) ← strictFinMkParts peeledInput
  unless derivation.modulusReference.path == arity3ArgumentPath 0 do
    semanticError "Fin.mk modulus reference path mismatch"
  let resolvedModulus ← resolveInputSubterm peeledInput derivation.modulusReference
  requireEqual "Fin.mk modulus reference" modulusExpression resolvedModulus
  let (modulusTraceValue) ←
    interpretNatEvalTraceCore peeledInput modulusExpression (arity3ArgumentPath 0)
      derivation.modulusTrace
  let value ← interpretNatValueView peeledInput valueExpression derivation.valueView
  unless (natValueViewReference derivation.valueView).path == arity3ArgumentPath 1 do
    semanticError "Fin.mk value view path mismatch"
  unless derivation.value == natValueViewValue derivation.valueView &&
      derivation.value == value && derivation.modulus > 0 &&
      derivation.normalized == derivation.value % derivation.modulus do
    semanticError "Fin.mk scalar equation mismatch"
  unless modulusTraceValue == derivation.modulus do
    semanticError "Fin.mk modulus trace value mismatch"
  unless value == derivation.value do
    semanticError "Fin.mk value view mismatch"
  let canonical := canonicalFinLiteral derivation.modulus derivation.normalized
  unless ← defEqFinLiteralRestored canonical peeledInput do
    semanticError "canonical Fin.mk literal is not definitionally equal to the input"
  return canonical

def interpretFinMkCanonical (peeledInput : Expr)
    (derivation : FinMkCanonicalDerivation) : MetaM Expr :=
  interpretFinMkCanonicalCore peeledInput derivation

private def deriveFinMkCanonicalCore (declaration : Name)
    (peeledInput procedureOutput : Expr) : MetaM (Option FinMkCanonicalDerivation) := do
  unless declaration == `Fin.reduceFinMk do
    return none
  if procedureOutput.hasMVar then
    return none
  let (modulusExpression, valueExpression, _) ← strictFinMkParts peeledInput
  let modulusReference ← makeInputRef modulusExpression (arity3ArgumentPath 0)
  let (modulusTrace, modulus) ←
    deriveNatEvalTraceCore peeledInput modulusExpression (arity3ArgumentPath 0)
  let valueView ← deriveNatValueView peeledInput valueExpression (arity3ArgumentPath 1)
  let value := natValueViewValue valueView
  unless modulus > 0 do
    return none
  let normalized := value % modulus
  let derivation : FinMkCanonicalDerivation := {
    modulus
    value
    normalized
    modulusReference
    modulusTrace
    valueView
  }
  let interpreted ← interpretFinMkCanonical peeledInput derivation
  unless Expr.equal interpreted procedureOutput do
    return none
  return some derivation

/-- Recognize `Fin.reduceFinMk` by independently replayable structural Nat
  evaluation of its modulus and the existing strict Nat value view. -/
def deriveFinMkCanonical? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option FinMkCanonicalDerivation) := do
  try
    withRestoredMetaState <| deriveFinMkCanonicalCore declaration peeledInput procedureOutput
  catch _ =>
    return none

private def deriveFinLiteralCore (declaration : Name)
    (peeledInput procedureOutput : Expr) : MetaM (Option SemanticSimproc) := do
  unless declaration == `Fin.isValue do
    return none
  if procedureOutput.hasMVar then
    return none
  let (_, modulusExpression, sourceExpression, literalInstanceExpression) ←
    strictFinLiteralParts peeledInput
  let modulusView ← deriveNatValueView peeledInput modulusExpression
    ((arity3ArgumentPath 0).push .appArgument)
  let sourceView ← deriveRawNatView sourceExpression (arity3ArgumentPath 1)
  let modulus := natValueViewValue modulusView
  let source := natValueViewValue sourceView
  unless modulus > 0 do
    return none
  let normalized := source % modulus
  if source < modulus then
    let derivation : FinLiteralGuard := {
      modulus
      source
      normalized
      modulusView
      sourceView
    }
    let interpreted ← interpretFinLiteralInRange peeledInput derivation
    unless Expr.equal interpreted procedureOutput do
      return none
    return some <| .valueGuard (.finLiteralInRange derivation)
  let literalInstance ← makeInstanceWitness peeledInput literalInstanceExpression
    (arity3ArgumentPath 2)
  let derivation : FinLiteralModuloDerivation := {
    modulus
    source
    normalized
    modulusView
    sourceView
    literalInstance
  }
  let interpreted ← interpretFinLiteralModulo peeledInput derivation
  unless Expr.equal interpreted procedureOutput do
    return none
  return some <| .canonicalValue (.finLiteralModulo derivation)

/-- Recognize the strict direct-syntax guard and modulo branches of
  `Fin.isValue`.  All semantic derivation is observational and restores Meta
  state and diagnostics. -/
def deriveFinLiteral? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option SemanticSimproc) := do
  try
    withRestoredMetaState <| deriveFinLiteralCore declaration peeledInput procedureOutput
  catch _ =>
    return none

private def deriveIteSelectionCore (declaration : Name) (peeledInput procedureOutput : Expr)
    (conditionProgram : NestedProgram) : MetaM (Option IteSelection) := do
  unless declaration == `reduceIte do
    return none
  if peeledInput.hasMVar || procedureOutput.hasMVar then
    return none
  let_expr _f@ite _α c _i tb eb ← peeledInput | return none
  let conditionFingerprint ← exprFingerprintHash c
  unless conditionProgram.program.initialFingerprint == conditionFingerprint do
    return none
  let trueFingerprint ← exprFingerprintHash (mkConst ``True)
  let falseFingerprint ← exprFingerprintHash (mkConst ``False)
  let (decision, selectedBranch, selectedIndex) ←
    if conditionProgram.program.finalFingerprint == trueFingerprint then
      pure (.trueBranch, tb, 3)
    else if conditionProgram.program.finalFingerprint == falseFingerprint then
      pure (.falseBranch, eb, 4)
    else
      return none
  unless Expr.equal selectedBranch procedureOutput do
    return none
  let conditionRef ← makeInputRef c (conditionalArgumentPath 1)
  let selectedBranchRef ← makeInputRef selectedBranch (conditionalArgumentPath selectedIndex)
  return some {
    decision
    conditionRef
    selectedBranchRef
    conditionProgram
  }

/-- Recognize the source-pinned `reduceIte` result after its condition has been
  executed by the recording engine.  Recognition is strict and observational:
  it accepts only a direct `ite` application, an exact direct `True`/`False`
  nested final fingerprint, and the branch returned by the procedure itself. -/
def deriveIteSelection? (declaration : Name) (peeledInput procedureOutput : Expr)
    (conditionProgram : NestedProgram) : MetaM (Option IteSelection) := do
  try
    withRestoredMetaState <|
      deriveIteSelectionCore declaration peeledInput procedureOutput conditionProgram
  catch _ =>
    return none

/-- Interpret a recorded `reduceIte` selection from a replayed condition result.
  The condition and branch references are resolved directly against the current
  peeled input, and the equality proof uses the exact upstream constructor. -/
def interpretIteSelection (peeledInput : Expr) (selection : IteSelection)
    (conditionResult : Simp.Result) : MetaM Simp.Result := do
  if peeledInput.hasMVar || conditionResult.expr.hasMVar then
    semanticError "open or unassigned metavariable in ite selection"
  let_expr f@ite α c i tb eb ← peeledInput
    | semanticError "ite selection input is not a direct ite"
  unless selection.conditionRef.path == conditionalArgumentPath 1 do
    semanticError "ite condition reference path mismatch"
  let selectedBranch ← match selection.decision with
    | .trueBranch => do
        unless selection.selectedBranchRef.path == conditionalArgumentPath 3 do
          semanticError "ite true-branch reference path mismatch"
        pure tb
    | .falseBranch => do
        unless selection.selectedBranchRef.path == conditionalArgumentPath 4 do
          semanticError "ite false-branch reference path mismatch"
        pure eb
  let resolvedCondition ← resolveInputSubterm peeledInput selection.conditionRef
  requireEqual "ite condition" c resolvedCondition
  let resolvedBranch ← resolveInputSubterm peeledInput selection.selectedBranchRef
  requireEqual "ite selected branch" selectedBranch resolvedBranch
  let expectedExpression := match selection.decision with
    | .trueBranch => mkConst ``True
    | .falseBranch => mkConst ``False
  requireEqual "ite condition result" expectedExpression conditionResult.expr
  let conditionProof ← conditionResult.getProof
  let proofName := match selection.decision with
    | .trueBranch => ``ite_cond_eq_true
    | .falseBranch => ``ite_cond_eq_false
  let proof := mkApp (mkApp5 (mkConst proofName f.constLevels!) α c i tb eb) conditionProof
  return { expr := selectedBranch, proof? := proof }

private def deriveDIteSelectionCore (declaration : Name) (peeledInput procedureOutput : Expr)
    (conditionProgram : NestedProgram) (conditionResult : Simp.Result) :
    MetaM (Option DIteSelection) := do
  unless declaration == `reduceDIte do
    return none
  if peeledInput.hasMVar || procedureOutput.hasMVar || conditionResult.expr.hasMVar then
    return none
  let_expr _f@dite _α c _i tb eb ← peeledInput | return none
  let conditionFingerprint ← exprFingerprintHash c
  unless conditionProgram.program.initialFingerprint == conditionFingerprint do
    return none
  let trueFingerprint ← exprFingerprintHash (mkConst ``True)
  let falseFingerprint ← exprFingerprintHash (mkConst ``False)
  let (decision, selectedBranch, selectedIndex, expectedExpression) ←
    if conditionProgram.program.finalFingerprint == trueFingerprint then
      pure (.trueBranch, tb, 3, mkConst ``True)
    else if conditionProgram.program.finalFingerprint == falseFingerprint then
      pure (.falseBranch, eb, 4, mkConst ``False)
    else
      return none
  requireEqual "dite condition result" expectedExpression conditionResult.expr
  let conditionProof ← conditionResult.getProof
  let h := match decision with
    | .trueBranch => mkApp2 (mkConst ``of_eq_true) c conditionProof
    | .falseBranch => mkApp2 (mkConst ``of_eq_false) c conditionProof
  let headBetaInput := mkApp selectedBranch h
  let headBetaOutput := headBetaInput.headBeta
  unless Expr.equal headBetaOutput procedureOutput do
    return none
  let conditionRef ← makeInputRef c (conditionalArgumentPath 1)
  let selectedBranchRef ← makeInputRef selectedBranch (conditionalArgumentPath selectedIndex)
  return some {
    decision
    conditionRef
    selectedBranchRef
    conditionProgram
    headBeta := {
      inputFingerprint := ← exprFingerprintHash headBetaInput
      outputFingerprint := ← exprFingerprintHash headBetaOutput
    }
  }

/-- Recognize the source-pinned `reduceDIte` result after its condition has been
  executed by the recording engine.  Recognition records only the exact
  pre-`headBeta` application and its output fingerprints; the proof term itself
  remains ephemeral and is never serialized. -/
def deriveDIteSelection? (declaration : Name) (peeledInput procedureOutput : Expr)
    (conditionProgram : NestedProgram) (conditionResult : Simp.Result) :
    MetaM (Option DIteSelection) := do
  try
    withRestoredMetaState <|
      deriveDIteSelectionCore declaration peeledInput procedureOutput conditionProgram
        conditionResult
  catch _ =>
    return none

/-- Interpret a recorded `reduceDIte` selection from a replayed condition result.
  The branch application is reconstructed from the exact equality proof and
  reduced with the fixed `Expr.headBeta` operation before the source-pinned
  `dite_cond_eq_true/false` proof is rebuilt. -/
def interpretDIteSelection (peeledInput : Expr) (selection : DIteSelection)
    (conditionResult : Simp.Result) : MetaM Simp.Result := do
  if peeledInput.hasMVar || conditionResult.expr.hasMVar then
    semanticError "open or unassigned metavariable in dite selection"
  let_expr f@dite α c i tb eb ← peeledInput
    | semanticError "dite selection input is not a direct dite"
  unless selection.conditionRef.path == conditionalArgumentPath 1 do
    semanticError "dite condition reference path mismatch"
  let selectedBranch ← match selection.decision with
    | .trueBranch => do
        unless selection.selectedBranchRef.path == conditionalArgumentPath 3 do
          semanticError "dite true-branch reference path mismatch"
        pure tb
    | .falseBranch => do
        unless selection.selectedBranchRef.path == conditionalArgumentPath 4 do
          semanticError "dite false-branch reference path mismatch"
        pure eb
  let resolvedCondition ← resolveInputSubterm peeledInput selection.conditionRef
  requireEqual "dite condition" c resolvedCondition
  let resolvedBranch ← resolveInputSubterm peeledInput selection.selectedBranchRef
  requireEqual "dite selected branch" selectedBranch resolvedBranch
  let expectedExpression := match selection.decision with
    | .trueBranch => mkConst ``True
    | .falseBranch => mkConst ``False
  requireEqual "dite condition result" expectedExpression conditionResult.expr
  let conditionProof ← conditionResult.getProof
  let h := match selection.decision with
    | .trueBranch => mkApp2 (mkConst ``of_eq_true) c conditionProof
    | .falseBranch => mkApp2 (mkConst ``of_eq_false) c conditionProof
  let headBetaInput := mkApp selectedBranch h
  let headBetaInputFingerprint ← exprFingerprintHash headBetaInput
  requireStringEqual "dite headBeta input" selection.headBeta.inputFingerprint
    headBetaInputFingerprint
  let headBetaOutput := headBetaInput.headBeta
  let headBetaOutputFingerprint ← exprFingerprintHash headBetaOutput
  requireStringEqual "dite headBeta output" selection.headBeta.outputFingerprint
    headBetaOutputFingerprint
  let proofName := match selection.decision with
    | .trueBranch => ``dite_cond_eq_true
    | .falseBranch => ``dite_cond_eq_false
  let proof := mkApp (mkApp5 (mkConst proofName f.constLevels!) α c i tb eb) conditionProof
  return { expr := headBetaOutput, proof? := proof }

private def deriveNatBinaryInputCore (declaration : Name) (peeledInput : Expr) :
    MetaM (Option (NatBinaryDerivation × Expr)) := do
  let operator ← if declaration == `Nat.reduceAdd then
      pure .add
    else if declaration == `Nat.reduceDiv then
      pure .div
    else
      return none
  if peeledInput.hasMVar then
    return none
  let (actualInstance, actualLhs, actualRhs) ← strictNatBinaryParts peeledInput operator
  let operatorPath := binaryArgumentPath 3
  let operatorInstance ← makeInstanceWitness peeledInput actualInstance operatorPath
  let lhsView ← deriveNatValueView peeledInput actualLhs (binaryArgumentPath 4)
  let rhsView ← deriveNatValueView peeledInput actualRhs (binaryArgumentPath 5)
  let lhs := match lhsView with
    | .raw _ value _ => value
    | .ofNat _ value _ _ => value
  let rhs := match rhsView with
    | .raw _ value _ => value
    | .ofNat _ value _ _ => value
  let result := natBinaryResult operator lhs rhs
  let derivation : NatBinaryDerivation := {
    operator
    lhs
    rhs
    result
    lhsView
    rhsView
    operatorInstance
  }
  let interpreted ← interpretNatBinary peeledInput derivation
  return some (derivation, interpreted)

private def deriveNatBinaryCore (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option NatBinaryDerivation) := do
  if procedureOutput.hasMVar then
    return none
  let some (derivation, interpreted) ← deriveNatBinaryInputCore declaration peeledInput
    | return none
  unless Expr.equal interpreted procedureOutput do
    return none
  return some derivation

/-- Recognize the supported `Nat.reduceAdd`/`Nat.reduceDiv` syntax and build a
  self-validating semantic derivation.  Recognition is observational: all
  shadow validation state and diagnostics are restored, and unsupported input
  returns `none`. -/
def deriveNatBinary? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option NatBinaryDerivation) := do
  try
    withRestoredMetaState <| deriveNatBinaryCore declaration peeledInput procedureOutput
  catch _ =>
    return none

private def deriveIntNegOfNatSyntaxCore (declaration : Name)
    (peeledInput procedureOutput : Expr) : MetaM (Option InputSubtermRef) := do
  unless declaration == `Int.reduceNeg do
    return none
  if procedureOutput.hasMVar then
    return none
  unless Expr.equal peeledInput procedureOutput do
    return none
  let actualArgument ← strictIntNegArgument peeledInput
  let _ ← strictOfNatParts actualArgument
  let reference ← makeInputRef actualArgument #[.appArgument]
  let _ ← interpretIntNegOfNatSyntax peeledInput reference
  return some reference

/-- Recognize only the unchanged, syntax-guard branch of `Int.reduceNeg`.
  Recognition restores all Meta state and diagnostics, and records a checked
  reference to the complete direct `OfNat.ofNat` argument. -/
def deriveIntNegOfNatSyntax? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option InputSubtermRef) := do
  try
    withRestoredMetaState <| deriveIntNegOfNatSyntaxCore declaration peeledInput procedureOutput
  catch _ =>
    return none

private def deriveIntNegateLiteralCore (declaration : Name)
    (peeledInput procedureOutput : Expr) : MetaM (Option IntNegateLiteralDerivation) := do
  unless declaration == `Int.reduceNeg do
    return none
  if peeledInput.hasMVar || procedureOutput.hasMVar then
    return none
  let (outerInstance, argument) ← strictIntNegParts peeledInput
  -- The unchanged syntax guard owns every direct positive literal.
  if argument.isAppOfArity ``OfNat.ofNat 3 then
    return none
  let (innerInstance, positiveLiteral) ← strictIntNegParts argument
  let (literalType, numeralExpression, literalInstanceExpression) ←
    strictOfNatParts positiveLiteral
  requireEqual "Int literal type" (mkConst ``Int) literalType
  let (numeralMetadataDepth, strippedNumeral) := peelMetadata numeralExpression
  let .lit (.natVal magnitude) := strippedNumeral
    | return none
  let argumentPath := arity3ArgumentPath 2
  let numeralPath :=
    argumentPath ++ arity3ArgumentPath 2 ++ arity3ArgumentPath 1
  let outerInstancePath := arity3ArgumentPath 1
  let innerInstancePath := argumentPath ++ arity3ArgumentPath 1
  let literalInstancePath :=
    argumentPath ++ arity3ArgumentPath 2 ++ arity3ArgumentPath 2
  let derivation : IntNegateLiteralDerivation := {
    magnitude
    result := Int.ofNat magnitude
    argument := ← makeInputRef argument argumentPath
    numeral := ← makeInputRef numeralExpression numeralPath
    numeralMetadataDepth
    outerNegInstance := ← makeInstanceWitness peeledInput outerInstance outerInstancePath
    innerNegInstance := ← makeInstanceWitness peeledInput innerInstance innerInstancePath
    literalInstance := ←
      makeInstanceWitness peeledInput literalInstanceExpression literalInstancePath
  }
  let interpreted ← interpretIntNegateLiteral peeledInput derivation
  unless Expr.equal interpreted procedureOutput do
    return none
  return some derivation

/-- Recognize the changing, canonical double-negative branch of
  `Int.reduceNeg`. Unsupported positive-metadata and non-direct views remain
  deferred. -/
def deriveIntNegateLiteral? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option IntNegateLiteralDerivation) := do
  try
    withRestoredMetaState <|
      deriveIntNegateLiteralCore declaration peeledInput procedureOutput
  catch _ =>
    return none

/-- Classify either supported branch of `Int.reduceNeg`. -/
def deriveIntNeg? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option SemanticSimproc) := do
  if let some argument ← deriveIntNegOfNatSyntax? declaration peeledInput procedureOutput then
    return some <| .valueGuard (.intNegOfNatSyntax argument)
  if let some derivation ← deriveIntNegateLiteral? declaration peeledInput procedureOutput then
    return some <| .canonicalValue (.intNegateLiteral derivation)
  return none

/-! ## `Matrix.cons_val`

The vector lookup simproc is a dsimproc, but its body performs two different
sorts of reduction itself: `whnfR` exposes a vecCons spine and `whnfD`
classifies the length of the remaining tail.  The certificate records the
boundaries of those reductions and replays exactly those two operations.  No
expression produced by either operation is serialized. -/

private def matrixVecConsName : Name :=
  Name.str (Name.str .anonymous "Matrix") "vecCons"

private def vectorWhnfWitness (input output : Expr) : MetaM VectorWhnfWitness := do
  return {
    inputFingerprint := ← exprFingerprintHash input
    outputFingerprint := ← exprFingerprintHash output
  }

private def strictVectorConsParts (expression : Expr) (arity : Nat) :
    MetaM (Array Expr) := do
  unless expression.isAppOfArity matrixVecConsName arity do
    semanticError s!"vector vecCons view is not a fully applied {arity}-argument Matrix.vecCons"
  let .const name _ := expression.getAppFn
    | semanticError "vector vecCons view head is not a constant"
  unless name == matrixVecConsName do
    semanticError "vector vecCons view has an unexpected head"
  let arguments := expression.getAppArgs
  unless arguments.size == arity do
    semanticError "vector vecCons view argument count mismatch"
  return arguments

private def vectorIndexView (expression : Expr) : MetaM VectorIndexView := do
  if expression.hasMVar || expression.hasLooseBVars then
    semanticError "vector index contains an open metavariable or bound variable"
  let some value := expression.int?
    | semanticError "vector index is not the strict Expr.int? syntax"
  let constructor ← if expression.isAppOfArity ``OfNat.ofNat 3 then
    let .const name levels := expression.getAppFn
      | semanticError "vector positive index head is not a constant"
    unless name == ``OfNat.ofNat && levels == [.zero] do
      semanticError "vector positive index has an unsupported head"
    pure .positive
  else if expression.isAppOfArity ``Neg.neg 3 then
    let argument := expression.getAppArgs[2]!
    -- Expr.int? checks the inner OfNat syntax itself.  Keep this second
    -- structural check explicit so a future broadening of int? cannot
    -- silently broaden the certificate language.
    unless argument.nat?.isSome do
      semanticError "vector negative index is not a strict OfNat numeral"
    let .const name levels := expression.getAppFn
      | semanticError "vector negative index head is not a constant"
    unless name == ``Neg.neg && levels == [.zero] do
      semanticError "vector negative index has an unsupported head"
    pure .negative
  else
    semanticError "vector index has an unsupported constructor"
  return {
    wholeFingerprint := ← exprFingerprintHash expression
    value
    constructor
  }

private def vectorIndexValue (view : VectorIndexView) : Int := view.value

private def vectorWhnfRChecked (input : Expr) (witness : VectorWhnfWitness) :
    MetaM Expr := withRestoredMetaState do
  let inputFingerprint ← exprFingerprintHash input
  requireStringEqual "vector whnfR input" witness.inputFingerprint inputFingerprint
  let output ← Meta.whnfR input
  let outputFingerprint ← exprFingerprintHash output
  requireStringEqual "vector whnfR output" witness.outputFingerprint outputFingerprint
  return output

private def vectorWhnfDChecked (input : Expr) (witness : VectorWhnfWitness) :
    MetaM Expr := withRestoredMetaState do
  let inputFingerprint ← exprFingerprintHash input
  requireStringEqual "vector whnfD input" witness.inputFingerprint inputFingerprint
  let output ← Meta.whnfD input
  let outputFingerprint ← exprFingerprintHash output
  requireStringEqual "vector whnfD output" witness.outputFingerprint outputFingerprint
  return output

private def makeVectorWhnfWitness (input : Expr) :
    MetaM (Expr × VectorWhnfWitness) := do
  let output ← Meta.whnfR input
  return (output, ← vectorWhnfWitness input output)

private def makeVectorWhnfDWitness (input : Expr) :
    MetaM (Expr × VectorWhnfWitness) := do
  let output ← Meta.whnfD input
  return (output, ← vectorWhnfWitness input output)

private def vectorDependencyLocal (localDecl : LocalDecl) : MetaM LocalRef := do
  return {
    contextIndex := localDecl.index
    binderDepth := (← getLCtx).numIndices
    typeFingerprint := ← exprFingerprintHash localDecl.type
    valueFingerprint := ← localDecl.value?.mapM exprFingerprintHash
  }

private def vectorDependencyLevel? (level : Level) : Option LevelDescriptor :=
  match level with
  | .zero => some .zero
  | .succ level => (vectorDependencyLevel? level).map .succ
  | .max lhs rhs => do
      return .max (← vectorDependencyLevel? lhs) (← vectorDependencyLevel? rhs)
  | .imax lhs rhs => do
      return .imax (← vectorDependencyLevel? lhs) (← vectorDependencyLevel? rhs)
  | .param name => some (.param name)
  | .mvar _ => none

private partial def deriveVectorDependencyCore (expression : Expr) :
    MetaM DependencyTerm := do
  if expression.hasMVar || expression.hasLooseBVars then
    semanticError "vector dependency contains an open metavariable or bound variable"
  match expression with
  | .fvar fvarId =>
      let localDecl ← getFVarLocalDecl (.fvar fvarId)
      return .local (← vectorDependencyLocal localDecl)
  | .lit (.natVal value) => return .literal (.nat value)
  | .lit (.strVal value) => return .literal (.string value)
  | .const name levels =>
      let levels ← levels.mapM fun level =>
        match vectorDependencyLevel? level with
        | some level => pure level
        | none => semanticError "vector dependency has a universe metavariable"
      return .application name levels.toArray #[]
  | .app _ _ =>
      let .const name levels := expression.getAppFn
        | semanticError "vector dependency application is not constant-headed"
      let arguments ← expression.getAppArgs.mapM deriveVectorDependencyCore
      let levels ← levels.mapM fun level =>
        match vectorDependencyLevel? level with
        | some level => pure level
        | none => semanticError "vector dependency has a universe metavariable"
      return .application name levels.toArray arguments
  | _ => semanticError "vector dependency has an unsupported expression form"

private def vectorDependencyTerm (expression : Expr) : MetaM DependencyTerm :=
  deriveVectorDependencyCore expression

private def vectorTraceBaseExpression (trace : NatOffsetTrace) (root : Expr) :
    MetaM Expr :=
  match trace with
  | .base reference => resolveInputSubterm root reference
  | .succ trace => vectorTraceBaseExpression trace root
  | .add _ _ lhs _ => vectorTraceBaseExpression lhs root

private def vectorCanonicalOffset (trace : NatOffsetTrace) (root : Expr)
    (offset : Nat) : MetaM Expr := do
  let base ← vectorTraceBaseExpression trace root
  return mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    Nat.mkType Nat.mkType Nat.mkType Nat.mkInstHAdd base (mkNatLit offset)

private def vectorCanonicalClosed (value : Nat) : Expr :=
  mkNatLit value

private def vectorTailLengthValue : VectorTailLength → Nat
  | .closed _ value _ => value
  | .offset _ _ knownOffset _ => knownOffset
  | .symbolic .. => 0

private def vectorTailLengthIsClosed : VectorTailLength → Bool
  | .closed .. => true
  | _ => false

private partial def deriveVectorLookupWalk (peeledInput procedureOutput : Expr)
    (rootWitness : VectorWhnfWitness) (indexView : VectorIndexView)
    (elements : Array Expr) (nestedViews : Array VectorConsView)
    (currentTail tailLengthExpression : Expr) :
    MetaM (Option VectorLookupDerivation) := do
  let (tailWhnf, tailWitness) ← makeVectorWhnfWitness currentTail
  if tailWhnf.isAppOfArity matrixVecConsName 4 then
    let arguments ← strictVectorConsParts tailWhnf 4
    deriveVectorLookupWalk peeledInput procedureOutput rootWitness indexView
      (elements.push arguments[2]!)
      (nestedViews.push { whnf := tailWitness, arity := 4 })
      arguments[3]! arguments[1]!
  else
    let stop := tailWitness
    let (lengthWhnf, lengthWitness) ← makeVectorWhnfDWitness tailLengthExpression
    let (tailLength, canonicalTailLength) ← if let .lit (.natVal value) := lengthWhnf then
      let canonical := vectorCanonicalClosed value
      pure (VectorTailLength.closed lengthWitness value
          (← exprFingerprintHash canonical), canonical)
    else if let some (_, offset) ← (Meta.isOffset? lengthWhnf).run then
      let some (trace, traceOffset) ← deriveNatOffsetTraceCore lengthWhnf lengthWhnf #[]
        | return none
      unless traceOffset == offset do return none
      let canonical ← vectorCanonicalOffset trace lengthWhnf offset
      pure (VectorTailLength.offset lengthWitness trace offset
          (← exprFingerprintHash canonical), canonical)
    else
      pure (VectorTailLength.symbolic lengthWitness
          { path := #[], fingerprint := ← exprFingerprintHash tailLengthExpression }
          (← exprFingerprintHash tailLengthExpression), tailLengthExpression)
    let prefixLength := elements.size
    let rawIndex := vectorIndexValue indexView
    let knownOffset := vectorTailLengthValue tailLength
    let variadic := !vectorTailLengthIsClosed tailLength
    let wrapped : Nat ← if variadic then
      unless 0 ≤ rawIndex && rawIndex < Int.ofNat (prefixLength + knownOffset) do
        return none
      pure rawIndex.toNat
    else
      pure (rawIndex % Int.ofNat (prefixLength + knownOffset)).toNat
    let selection ← if h : wrapped < prefixLength then
      unless Expr.equal elements[wrapped] procedureOutput do return none
      pure <| VectorSelection.prefix wrapped
    else
      let residual := wrapped - prefixLength
      let .app actualTail actualIndex := procedureOutput
        | return none
      unless Expr.equal actualTail currentTail do return none
      let indexType ← try inferType actualIndex catch _ => return none
      let dependency ← try vectorDependencyTerm actualIndex catch _ => return none
      let dependencyTypeFingerprint ← exprFingerprintHash indexType
      let (finType, numeral, _) ← try strictOfNatParts actualIndex catch _ => return none
      unless Expr.equal finType (mkApp (mkConst ``Fin []) canonicalTailLength) do
        return none
      let .lit (.natVal numeralValue) := numeral | return none
      unless numeralValue == residual do return none
      pure <| VectorSelection.tail residual dependency dependencyTypeFingerprint
    let derivation : VectorLookupDerivation := {
      spine := {
        root := { whnf := rootWitness, arity := 5 }
        nested := nestedViews
        stop
      }
      rawIndex
      indexView
      tailLength
      wrappedIndex := wrapped
      selection
    }
    return some derivation

private def deriveVectorLookupCore (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option VectorLookupDerivation) := do
  unless declaration == `Matrix.cons_val do return none
  if peeledInput.hasMVar || peeledInput.hasLooseBVars || procedureOutput.hasMVar then
    return none
  let (rootOutput, rootWitness) ← makeVectorWhnfWitness peeledInput
  let rootArguments ← try strictVectorConsParts rootOutput 5 catch _ => return none
  let indexView ← try vectorIndexView rootArguments[4]! catch _ => return none
  deriveVectorLookupWalk peeledInput procedureOutput rootWitness indexView
    #[rootArguments[2]!] #[] rootArguments[3]! rootArguments[1]!

private def deriveVectorLookup? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option VectorLookupDerivation) := do
  try
    withRestoredMetaState <| deriveVectorLookupCore declaration peeledInput procedureOutput
  catch _ => return none

private def interpretVectorTailLength (lengthExpression : Expr)
    (tailLength : VectorTailLength) : MetaM (Nat × Expr) := do
  let lengthWhnf ← match tailLength with
    | .closed witness .. | .offset witness .. | .symbolic witness .. =>
        vectorWhnfDChecked lengthExpression witness
  match tailLength with
  | .closed _ value canonicalFingerprint =>
      let .lit (.natVal actual) := lengthWhnf
        | semanticError "vector closed tail length is not a raw literal"
      unless actual == value do semanticError "vector closed tail length value mismatch"
      requireStringEqual "vector closed canonical length"
        canonicalFingerprint (← exprFingerprintHash (vectorCanonicalClosed actual))
      return (actual, vectorCanonicalClosed actual)
  | .offset _ trace knownOffset canonicalFingerprint =>
      let actualOffset ← interpretNatOffsetTraceCore lengthWhnf lengthWhnf #[] trace
      unless actualOffset == knownOffset do
        semanticError "vector offset tail length mismatch"
      let canonical ← vectorCanonicalOffset trace lengthWhnf knownOffset
      requireStringEqual "vector offset canonical length"
        canonicalFingerprint (← exprFingerprintHash canonical)
      return (knownOffset, canonical)
  | .symbolic _ original canonicalFingerprint =>
      unless original.path.isEmpty do
        semanticError "vector symbolic tail length reference is not rooted at its source view"
      requireStringEqual "vector symbolic tail length reference"
        original.fingerprint (← exprFingerprintHash lengthExpression)
      requireStringEqual "vector symbolic canonical length"
        canonicalFingerprint (← exprFingerprintHash lengthExpression)
      return (0, lengthExpression)

private def interpretVectorIndex (expression : Expr) (view : VectorIndexView) :
    MetaM Int := do
  let actual ← vectorIndexView expression
  unless actual == view do semanticError "vector index syntax/value mismatch"
  return actual.value

private def interpretVectorLookupCore (peeledInput : Expr)
    (derivation : VectorLookupDerivation) : MetaM Expr := do
  let rootOutput ← vectorWhnfRChecked peeledInput derivation.spine.root.whnf
  let rootArguments ← strictVectorConsParts rootOutput derivation.spine.root.arity
  let rawIndex ← interpretVectorIndex rootArguments[4]! derivation.indexView
  unless rawIndex == derivation.rawIndex do
    semanticError "vector raw index mismatch"
  let mut elements : Array Expr := #[rootArguments[2]!]
  let mut currentTail := rootArguments[3]!
  let mut tailLengthExpression := rootArguments[1]!
  for view in derivation.spine.nested do
    let tailWhnf ← vectorWhnfRChecked currentTail view.whnf
    let arguments ← strictVectorConsParts tailWhnf view.arity
    elements := elements.push arguments[2]!
    currentTail := arguments[3]!
    tailLengthExpression := arguments[1]!
  let stopWhnf ← vectorWhnfRChecked currentTail derivation.spine.stop
  if stopWhnf.isAppOfArity matrixVecConsName 4 then
    semanticError "vector stop view is still a vecCons"
  let (tailLength, canonicalTailLength) ←
    interpretVectorTailLength tailLengthExpression derivation.tailLength
  let prefixLength := elements.size
  let variadic := !vectorTailLengthIsClosed derivation.tailLength
  let knownOffset := vectorTailLengthValue derivation.tailLength
  let wrapped ← if variadic then
    unless 0 ≤ rawIndex && rawIndex < Int.ofNat (prefixLength + knownOffset) do
      semanticError "vector variadic index is out of bounds"
    pure rawIndex.toNat
  else
    pure (rawIndex % Int.ofNat (prefixLength + tailLength)).toNat
  unless wrapped == derivation.wrappedIndex do
    semanticError "vector wrapped index mismatch"
  match derivation.selection with
  | .prefix index => do
      unless index == wrapped && index < prefixLength do
        semanticError "vector prefix selection mismatch"
      return elements[index]!
  | .tail residual dependency typeFingerprint => do
      unless wrapped >= prefixLength && residual == wrapped - prefixLength do
        semanticError "vector tail residual mismatch"
      let index ← reconstructDependencyTerm peeledInput dependency
      let indexType ← try inferType index catch _ =>
        semanticError "vector tail index has no inferable type"
      requireStringEqual "vector tail index type" typeFingerprint
        (← exprFingerprintHash indexType)
      let expectedType := mkApp (mkConst ``Fin []) canonicalTailLength
      requireEqual "vector tail index expected type" expectedType indexType
      let (tailIndexType, numeral, _) ← strictOfNatParts index
      requireEqual "vector tail index type syntax" expectedType tailIndexType
      let .lit (.natVal numeralValue) := numeral
        | semanticError "vector tail index is not a raw literal"
      unless numeralValue == residual do
        semanticError "vector tail index literal mismatch"
      return mkApp currentTail index

def interpretVectorLookup (peeledInput : Expr)
    (derivation : VectorLookupDerivation) : MetaM Expr :=
  withRestoredMetaState <| interpretVectorLookupCore peeledInput derivation

def deriveVectorLookup (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option VectorLookupDerivation) :=
  deriveVectorLookup? declaration peeledInput procedureOutput

private structure ExistsEqFound where
  route : Array ExistsEqRouteStep
  binderSide : EqualityBinderSide
  replacementPath : Array ExprPathStep
  binderDepth : Nat

private structure ExistsEqBinder where
  fvar : Expr
  type : Expr
  head : Expr
  body : Expr
  proof : Option Expr := none
  deriving Inhabited

private structure ExistsEqTransform where
  body : Expr
  binders : Array ExistsEqBinder := #[]
  replacement : Option Expr := none
  lctx : LocalContext := {}

private def existsArgumentPath (index : Nat) : Array ExprPathStep :=
  match index with
  | 0 => #[.appFunction, .appArgument]
  | 1 => #[.appArgument]
  | _ => #[]

private def andArgumentPath (index : Nat) : Array ExprPathStep :=
  match index with
  | 0 => #[.appFunction, .appArgument]
  | 1 => #[.appArgument]
  | _ => #[]

private def appendPath (path suffix : Array ExprPathStep) : Array ExprPathStep :=
  path ++ suffix

private structure ExistsEqLambdaBinder where
  name : Name
  type : Expr
  binderInfo : BinderInfo

private def closeExistsEqRawSubterm (expression : Expr)
    (binders : Array ExistsEqLambdaBinder) : Expr :=
  binders.toList.foldr
    (fun binder result => mkLambda binder.name binder.binderInfo binder.type result) expression

private def resolveExistsEqRawPath (root : Expr) (path : Array ExprPathStep) :
    MetaM (Expr × Array ExistsEqLambdaBinder) := do
  let mut current := root
  let mut binders : Array ExistsEqLambdaBinder := #[]
  let mut stepIndex := 0
  for step in path do
    current ← match step, current with
      | .appFunction, .app function _ => pure function
      | .appArgument, .app _ argument => pure argument
      | .metadataBody, .mdata _ body => pure body
      | .lambdaType, .lam _ type _ _ => pure type
      | .lambdaBody, .lam name type body binderInfo =>
          binders := binders.push { name, type, binderInfo }
          pure body
      | .forallType, .forallE _ type _ _ => pure type
      | .forallBody, .forallE _ _ body _ => pure body
      | .letType, .letE _ type _ _ _ => pure type
      | .letValue, .letE _ _ value _ _ => pure value
      | .letBody, .letE _ _ _ body _ => pure body
      | _, expression =>
          semanticError s!"exists-and-eq raw path step {stepIndex} ({repr step}) does not match {expression.ctorName}"
    stepIndex := stepIndex + 1
  return (current, binders)

private def resolveExistsEqInputSubterm (root : Expr) (reference : InputSubtermRef) :
    MetaM Expr := do
  let (current, binders) ← resolveExistsEqRawPath root reference.path
  let closed := closeExistsEqRawSubterm current binders
  unless !closed.hasLooseBVars do
    semanticError "exists-and-eq replacement reference leaves loose bound variables"
  let actualFingerprint ← exprFingerprintHash closed
  requireStringEqual "exists-and-eq replacement input subterm" reference.fingerprint
    actualFingerprint
  return current

private def strictExistsParts (expression : Expr) : MetaM (Expr × Expr × Expr) := do
  unless expression.isAppOfArity ``Exists 2 do
    semanticError "exists-and-eq input is not a direct two-argument Exists application"
  let function := expression.getAppFn
  let .const name levels := function
    | semanticError "exists-and-eq input head is not a constant"
  unless name == ``Exists && levels.length == 1 do
    semanticError "exists-and-eq input has an unexpected Exists head"
  let arguments := expression.getAppArgs
  unless arguments.size == 2 do
    semanticError "exists-and-eq input does not have exactly two Exists arguments"
  let predicate := arguments[1]!
  let .lam _ _ _ _ := predicate
    | semanticError "exists-and-eq predicate is not a direct lambda"
  return (arguments[0]!, predicate, function)

private def strictAndParts (expression : Expr) : MetaM (Expr × Expr × Expr) := do
  unless expression.isAppOfArity ``And 2 do
    semanticError "exists-and-eq route expected a direct And"
  let function := expression.getAppFn
  let .const name levels := function
    | semanticError "exists-and-eq And head is not a constant"
  unless name == ``And && levels.isEmpty do
    semanticError "exists-and-eq And has an unexpected head"
  let arguments := expression.getAppArgs
  unless arguments.size == 2 do
    semanticError "exists-and-eq And does not have exactly two arguments"
  return (arguments[0]!, arguments[1]!, function)

private def strictEqType (expression : Expr) : MetaM Expr := do
  let (type, _, _) ← strictEqParts expression
  return type

private partial def findExistsEqRouteCore (outer : Expr) (expression : Expr)
    (path : Array ExprPathStep) (route : Array ExistsEqRouteStep)
    (binderDepth : Nat) : MetaM (Option ExistsEqFound) := do
  if expression.isAppOfArity ``Eq 3 then
    let (type, lhs, rhs) ← strictEqParts expression
    let outerType ← inferType outer
    unless ← defEqRestored type outerType do
      return none
    if Expr.equal outer lhs && !rhs.containsFVar outer.fvarId! then
      return some {
        route
        binderSide := .left
        replacementPath := appendPath path (arity3ArgumentPath 2)
        binderDepth
      }
    if Expr.equal outer rhs && !lhs.containsFVar outer.fvarId! then
      return some {
        route
        binderSide := .right
        replacementPath := appendPath path (arity3ArgumentPath 1)
        binderDepth
      }
    return none
  if expression.isAppOfArity ``And 2 then
    let (lhs, rhs, _) ← strictAndParts expression
    if let some result ← findExistsEqRouteCore outer lhs
        (appendPath path (andArgumentPath 0)) (route.push .andLeft) binderDepth then
      return some result
    return ← findExistsEqRouteCore outer rhs
      (appendPath path (andArgumentPath 1)) (route.push .andRight) binderDepth
  if expression.isAppOfArity ``Exists 2 then
    let arguments := expression.getAppArgs
    let binderType := arguments[0]!
    unless !binderType.containsFVar outer.fvarId! do
      return none
    let predicate := arguments[1]!
    let .lam name _ body _ := predicate
      | return none
    return ← withLocalDecl name .default binderType fun binder => do
      let openedBody := body.instantiate1 binder
      return ← findExistsEqRouteCore outer openedBody
        (appendPath path ((existsArgumentPath 1).push .lambdaBody))
        (route.push .existsBody) (binderDepth + 1)
  return none

private def findExistsEqRoute (outer : Expr) (body : Expr) :
    MetaM (Option ExistsEqFound) :=
  findExistsEqRouteCore outer body (#[.appArgument, .lambdaBody]) #[] 0

private def replaceExistsEqOuter (expression outer replacement : Expr) : Expr :=
  expression.replaceFVar outer replacement

private partial def transformExistsEqBodyCore (root outer : Expr)
    (expression : Expr) (path : Array ExprPathStep)
    (derivation : ExistsAndEqDerivation) (routeIndex binderDepth : Nat) :
    MetaM ExistsEqTransform := do
  if expression.isAppOfArity ``And 2 then
    let (lhs, rhs, head) ← strictAndParts expression
    let routeStep? := derivation.route[routeIndex]?
    match routeStep? with
    | some .andLeft => do
        let selected ← transformExistsEqBodyCore root outer lhs
          (appendPath path (andArgumentPath 0)) derivation (routeIndex + 1) binderDepth
        let body := mkApp2 head selected.body rhs
        return {
          body
          binders := selected.binders
          replacement := selected.replacement
          lctx := selected.lctx
        }
    | some .andRight => do
        let selected ← transformExistsEqBodyCore root outer rhs
          (appendPath path (andArgumentPath 1)) derivation (routeIndex + 1) binderDepth
        let body := mkApp2 head lhs selected.body
        return {
          body
          binders := selected.binders
          replacement := selected.replacement
          lctx := selected.lctx
        }
    | _ => semanticError "exists-and-eq route does not select an And branch"
  else if expression.isAppOfArity ``Exists 2 then
    let routeStep? := derivation.route[routeIndex]?
    match routeStep? with
    | some .existsBody => do
        let arguments := expression.getAppArgs
        let binderType := arguments[0]!
        unless !binderType.containsFVar outer.fvarId! do
          semanticError "exists-and-eq crossed binder type depends on outer binder"
        let predicate := arguments[1]!
        let .lam name _ body _ := predicate
          | semanticError "exists-and-eq nested Exists predicate is not a direct lambda"
        withLocalDecl name .default binderType fun binder => do
          let openedBody := body.instantiate1 binder
          let selected ← transformExistsEqBodyCore root outer openedBody
            (appendPath path ((existsArgumentPath 1).push .lambdaBody)) derivation
            (routeIndex + 1) (binderDepth + 1)
          return {
            body := selected.body
            binders := #[{
              fvar := binder
              type := binderType
              head := expression.getAppFn
              body := openedBody
            }] ++ selected.binders
            replacement := selected.replacement
            lctx := selected.lctx
          }
    | _ => semanticError "exists-and-eq route does not select an Exists body"
  else if expression.isAppOfArity ``Eq 3 then
    unless routeIndex == derivation.route.size do
      semanticError "exists-and-eq route has trailing steps after equality"
    let (type, lhs, rhs) ← strictEqParts expression
    let outerType ← inferType outer
    unless ← defEqRestored type outerType do
      semanticError "exists-and-eq equality type mismatch"
    let replacementExpression ← match derivation.binderSide with
      | .left => do
          unless Expr.equal outer lhs && !rhs.containsFVar outer.fvarId! do
            semanticError "exists-and-eq left orientation mismatch"
          pure rhs
      | .right => do
          unless Expr.equal outer rhs && !lhs.containsFVar outer.fvarId! do
            semanticError "exists-and-eq right orientation mismatch"
          pure lhs
    unless derivation.replacement.binderDepth == binderDepth do
      semanticError "exists-and-eq replacement binder depth mismatch"
    let replacementReference := derivation.replacement.reference
    let expectedPath := appendPath path <| match derivation.binderSide with
      | .left => arity3ArgumentPath 2
      | .right => arity3ArgumentPath 1
    unless replacementReference.path == expectedPath do
      semanticError "exists-and-eq replacement path mismatch"
    let resolvedReplacement ← resolveExistsEqInputSubterm root replacementReference
    unless !replacementExpression.containsFVar outer.fvarId! do
      semanticError "exists-and-eq replacement depends on eliminated binder"
    unless ← defEqRestored (← inferType replacementExpression) outerType do
      semanticError "exists-and-eq replacement type mismatch"
    let _ := resolvedReplacement
    return { body := expression, replacement := some replacementExpression, lctx := ← getLCtx }
  else
    semanticError "exists-and-eq route reached an unsupported proposition"

private def wrapExistsEqBinders (binders : Array ExistsEqBinder) (body : Expr) : MetaM Expr := do
  let mut result := body
  let mut index := binders.size
  while index > 0 do
    index := index - 1
    let binder := binders[index]!
    let predicate ← mkLambdaFVars #[binder.fvar] result
    let level ← getLevel binder.type
    result := mkApp2 (mkConst ``Exists [level]) binder.type predicate
  return result

private def interpretExistsAndEqShape (peeledInput : Expr)
    (derivation : ExistsAndEqDerivation) : MetaM (Expr × Expr × Array ExistsEqBinder) := do
  let (outerType, predicate, _) ← strictExistsParts peeledInput
  let .lam name _ body _ := predicate
    | semanticError "exists-and-eq outer predicate is not a direct lambda"
  withLocalDecl name .default outerType fun outer => do
    let openedBody := body.instantiate1 outer
    let some found ← findExistsEqRoute outer openedBody
      | semanticError "exists-and-eq derivation does not describe the source's first eligible equality"
    unless derivation.route == found.route do
      semanticError "exists-and-eq route is not the source's first eligible route"
    unless derivation.binderSide == found.binderSide do
      semanticError "exists-and-eq equality orientation is not the source's first eligible orientation"
    unless derivation.replacement.reference.path == found.replacementPath do
      semanticError "exists-and-eq replacement path is not the source's first eligible path"
    unless derivation.replacement.binderDepth == found.binderDepth do
      semanticError "exists-and-eq replacement binder depth is not the source's first eligible depth"
    let transformed ← transformExistsEqBodyCore peeledInput outer openedBody
      (#[.appArgument, .lambdaBody]) derivation 0 0
    let some replacement := transformed.replacement
      | semanticError "exists-and-eq route did not find a replacement"
    let output ← withLCtx' transformed.lctx do
      let replacedBody := replaceExistsEqOuter transformed.body outer replacement
      wrapExistsEqBinders transformed.binders replacedBody
    let outputType ← inferType output
    unless ← defEqRestored outputType (mkSort .zero) do
      semanticError "exists-and-eq output is not a proposition"
    return (output, replacement, transformed.binders)

private def deriveExistsAndEqCore (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option ExistsAndEqDerivation) := do
  unless declaration == `ExistsAndEq.existsAndEq do
    return none
  if peeledInput.hasMVar || procedureOutput.hasMVar then
    return none
  let (outerType, predicate, _) ← strictExistsParts peeledInput
  let .lam name _ body _ := predicate
    | return none
  withLocalDecl name .default outerType fun outer => do
    let openedBody := body.instantiate1 outer
    let some found ← findExistsEqRoute outer openedBody | return none
    let (replacementExpression, replacementBinders) ←
      resolveExistsEqRawPath peeledInput found.replacementPath
    let closedReplacement := closeExistsEqRawSubterm replacementExpression replacementBinders
    unless !closedReplacement.hasLooseBVars do
      semanticError "exists-and-eq replacement reference leaves loose bound variables"
    let replacementReference : InputSubtermRef := {
      path := found.replacementPath
      fingerprint := ← exprFingerprintHash closedReplacement
    }
    let derivation : ExistsAndEqDerivation := {
      route := found.route
      binderSide := found.binderSide
      replacement := {
        reference := replacementReference
        binderDepth := found.binderDepth
      }
    }
    let interpreted ← interpretExistsAndEqShape peeledInput derivation
    unless exprEqualIgnoringBinderNames interpreted.1 procedureOutput do
      return none
    return some derivation

private def mkExistsEqExistsIntro (goal value proof : Expr) : MetaM Expr := do
  let (α, predicate, _) ← strictExistsParts goal
  let level ← getLevel α
  return mkAppN (mkConst ``Exists.intro [level]) #[α, predicate, value, proof]

private def mkExistsEqExistsElim (proof eliminator : Expr) : MetaM Expr :=
  do
    let proofType ← inferType proof
    let (α, p, _) ← strictExistsParts proofType
    let eliminatorType ← inferType eliminator
    let .forallE _ _ afterBinder _ := eliminatorType
      | semanticError "exists-and-eq Exists.elim argument is not a two-binder function"
    let .forallE _ _ goal _ := afterBinder
      | semanticError "exists-and-eq Exists.elim eliminator has an unexpected type"
    let level ← getLevel α
    return mkAppN (mkConst ``Exists.elim [level]) #[α, p, goal, proof, eliminator]

private def mkExistsEqExistsElimWithPredicate
    (α predicate proof eliminator : Expr) : MetaM Expr := do
  let eliminatorType ← inferType eliminator
  let .forallE _ _ afterBinder _ := eliminatorType
    | semanticError "exists-and-eq Exists.elim argument is not a two-binder function"
  let .forallE _ _ goal _ := afterBinder
    | semanticError "exists-and-eq Exists.elim eliminator has an unexpected type"
  let level ← getLevel α
  return mkAppN (mkConst ``Exists.elim [level]) #[α, predicate, goal, proof, eliminator]

private def mkExistsEqAndIntro (lhs rhs : Expr) : MetaM Expr :=
  mkAppM ``And.intro #[lhs, rhs]

private def mkExistsEqAndLeft (proof : Expr) : MetaM Expr :=
  mkAppM ``And.left #[proof]

private def mkExistsEqAndRight (proof : Expr) : MetaM Expr :=
  mkAppM ``And.right #[proof]

private def mkExistsEqSymm (proof : Expr) : MetaM Expr :=
  mkAppM ``Eq.symm #[proof]

private def mkExistsEqCongrArg (motive proof : Expr) : MetaM Expr :=
  mkAppM ``congrArg #[motive, proof]

private def mkExistsEqEqMp (equality proof : Expr) : MetaM Expr :=
  mkAppM ``Eq.mp #[equality, proof]

private def mkExistsEqRfl (value : Expr) : MetaM Expr := do
  let valueType ← inferType value
  let level ← getLevel valueType
  return mkApp2 (mkConst ``rfl [level]) valueType value

private def canonicalExistsEqInput (input : Expr) : MetaM Expr := do
  let (outerType, predicate, head) ← strictExistsParts input
  let .lam _ _ body binderInfo := predicate
    | semanticError "exists-and-eq canonical proof input predicate is not a lambda"
  return mkApp2 head outerType (mkLambda `a binderInfo outerType body)

private structure ExistsEqProofBinder where
  binder : ExistsEqBinder
  bodyProof : Expr

private partial def withExistsEqElimAlongRoute
    (expression proof outer : Expr) (route : Array ExistsEqRouteStep) (routeIndex : Nat)
    (crossed : Array ExistsEqProofBinder)
    (act : Array ExistsEqProofBinder → EqualityBinderSide → Expr → MetaM Expr) :
    MetaM Expr := do
  if expression.isAppOfArity ``And 2 then
    let (lhs, rhs, _) ← strictAndParts expression
    let some routeStep := route[routeIndex]? |
      semanticError "exists-and-eq proof route ended at an And"
    match routeStep with
    | .andLeft =>
        let branchProof ← mkExistsEqAndLeft proof
        withExistsEqElimAlongRoute lhs branchProof outer route (routeIndex + 1) crossed act
    | .andRight =>
        let branchProof ← mkExistsEqAndRight proof
        withExistsEqElimAlongRoute rhs branchProof outer route (routeIndex + 1) crossed act
    | .existsBody =>
        semanticError "exists-and-eq proof route selected an Exists at an And"
  else if expression.isAppOfArity ``Exists 2 then
    let (binderType, predicate, head) ← strictExistsParts expression
    let some routeStep := route[routeIndex]? |
      semanticError "exists-and-eq proof route ended at an Exists"
    match routeStep with
    | .existsBody =>
        let .lam name _ body _ := predicate
          | semanticError "exists-and-eq proof nested predicate is not a lambda"
        return ← withLocalDecl name .default binderType fun binder => do
          let openedBody := body.instantiate1 binder
          withLocalDeclD .anonymous openedBody fun bodyProof => do
            let crossedBinder : ExistsEqProofBinder := {
              binder := {
                fvar := binder
                type := binderType
                head
                body := openedBody
                proof := some bodyProof
              }
              bodyProof
            }
            let inner ← withExistsEqElimAlongRoute openedBody bodyProof outer route
              (routeIndex + 1) (crossed.push crossedBinder) act
            let eliminator ← mkLambdaFVars #[binder, bodyProof] inner
            mkExistsEqExistsElim proof eliminator
    | _ => semanticError "exists-and-eq proof route selected a non-Exists step"
  else if expression.isAppOfArity ``Eq 3 then
    unless routeIndex == route.size do
      semanticError "exists-and-eq proof route has trailing steps"
    let (type, lhs, rhs) ← strictEqParts expression
    let outerType ← inferType outer
    unless ← defEqRestored type outerType do
      semanticError "exists-and-eq proof equality type mismatch"
    if Expr.equal outer lhs then
      act crossed .left proof
    else if Expr.equal outer rhs then
      let reversed ← mkExistsEqSymm proof
      act crossed .right reversed
    else
      semanticError "exists-and-eq proof equality does not mention outer binder"
  else
    semanticError "exists-and-eq proof route reached unsupported proposition"

private partial def mkExistsEqForwardBodyProof
    (expression proof outer replacement equality : Expr)
    (route : Array ExistsEqRouteStep) (routeIndex crossedIndex : Nat)
    (crossed : Array ExistsEqProofBinder) : MetaM Expr := do
  if expression.isAppOfArity ``And 2 then
    let (lhs, rhs, _) ← strictAndParts expression
    let some routeStep := route[routeIndex]? |
      semanticError "exists-and-eq forward route ended at an And"
    let selectedProof ← match routeStep with
      | .andLeft => mkExistsEqAndLeft proof
      | .andRight => mkExistsEqAndRight proof
      | .existsBody => semanticError "exists-and-eq forward route selected an Exists at And"
    let selectedExpression := match routeStep with
      | .andLeft => lhs
      | .andRight => rhs
      | .existsBody => lhs
    let selected ← mkExistsEqForwardBodyProof selectedExpression selectedProof outer replacement
      equality route (routeIndex + 1) crossedIndex crossed
    let offExpression := match routeStep with
      | .andLeft => rhs
      | .andRight => lhs
      | .existsBody => rhs
    let offProof ← match routeStep with
      | .andLeft => mkExistsEqAndRight proof
      | .andRight => mkExistsEqAndLeft proof
      | .existsBody => semanticError "exists-and-eq forward route selected an Exists at And"
    let motive ← mkLambdaFVars #[outer] offExpression
    let congruence ← mkExistsEqCongrArg motive equality
    let offRewritten ← mkExistsEqEqMp congruence offProof
    match routeStep with
    | .andLeft => return ← mkExistsEqAndIntro selected offRewritten
    | .andRight => return ← mkExistsEqAndIntro offRewritten selected
    | .existsBody => unreachable!
  else if expression.isAppOfArity ``Exists 2 then
    let some routeStep := route[routeIndex]? |
      semanticError "exists-and-eq forward route ended at an Exists"
    match routeStep with
    | .existsBody =>
        let some crossedBinder := crossed[crossedIndex]? |
          semanticError "exists-and-eq forward binder count mismatch"
        let bodyProof := crossedBinder.bodyProof
        mkExistsEqForwardBodyProof crossedBinder.binder.body bodyProof outer replacement equality
          route (routeIndex + 1) (crossedIndex + 1) crossed
    | _ => semanticError "exists-and-eq forward route selected a non-Exists step"
  else if expression.isAppOfArity ``Eq 3 then
    unless routeIndex == route.size do
      semanticError "exists-and-eq forward route has trailing steps"
    return ← mkExistsEqRfl replacement
  else
    semanticError "exists-and-eq forward proof reached unsupported proposition"

private partial def mkExistsEqIntroProof
    (goal : Expr) (values : Array Expr) (bodyProof : Expr) (index : Nat) : MetaM Expr := do
  if index == values.size then
    return bodyProof
  let (_, predicate, _) ← strictExistsParts goal
  let nestedGoal := match predicate with
    | .lam _ _ body _ => body.instantiate1 values[index]!
    | _ => unreachable!
  let inner ← mkExistsEqIntroProof nestedGoal values bodyProof (index + 1)
  mkExistsEqExistsIntro goal values[index]! inner

private partial def mkExistsEqAfterBodyProof
    (goal proof : Expr) (route : Array ExistsEqRouteStep) (routeIndex crossedIndex : Nat)
    (crossed : Array ExistsEqProofBinder) : MetaM Expr := do
  if goal.isAppOfArity ``Exists 2 then
    let some routeStep := route[routeIndex]? |
      semanticError "exists-and-eq reverse route ended at an Exists"
    match routeStep with
    | .existsBody =>
        let some crossedBinder := crossed[crossedIndex]? |
          semanticError "exists-and-eq reverse binder count mismatch"
        let (binderType, predicate, _) ← strictExistsParts goal
        unless ← defEqRestored binderType crossedBinder.binder.type do
          semanticError "exists-and-eq reverse binder type mismatch"
        let .lam _ _ body _ := predicate
          | semanticError "exists-and-eq reverse predicate is not a lambda"
        let nestedGoal := body.instantiate1 crossedBinder.binder.fvar
        let inner ← mkExistsEqAfterBodyProof nestedGoal proof route
          (routeIndex + 1) (crossedIndex + 1) crossed
        mkExistsEqExistsIntro goal crossedBinder.binder.fvar inner
    | _ => semanticError "exists-and-eq reverse route selected a non-Exists step"
  else if goal.isAppOfArity ``And 2 then
    let (lhs, rhs, _) ← strictAndParts goal
    let some routeStep := route[routeIndex]? |
      semanticError "exists-and-eq reverse route ended at an And"
    let selectedProof ← match routeStep with
      | .andLeft => mkExistsEqAndLeft proof
      | .andRight => mkExistsEqAndRight proof
      | .existsBody => semanticError "exists-and-eq reverse route selected an Exists at And"
    let selectedGoal := match routeStep with
      | .andLeft => lhs
      | .andRight => rhs
      | .existsBody => lhs
    let selected ← mkExistsEqAfterBodyProof selectedGoal selectedProof route
      (routeIndex + 1) crossedIndex crossed
    let offProof ← match routeStep with
      | .andLeft => mkExistsEqAndRight proof
      | .andRight => mkExistsEqAndLeft proof
      | .existsBody => semanticError "exists-and-eq reverse route selected an Exists at And"
    match routeStep with
    | .andLeft => mkExistsEqAndIntro selected offProof
    | .andRight => mkExistsEqAndIntro offProof selected
    | .existsBody => unreachable!
  else if goal.isAppOfArity ``Eq 3 then
    unless routeIndex == route.size do
      semanticError "exists-and-eq reverse route has trailing steps"
    let (type, lhs, rhs) ← strictEqParts goal
    unless ← defEqRestored type (← inferType lhs) do
      semanticError "exists-and-eq reverse equality type mismatch"
    unless ← defEqRestored lhs rhs do
      semanticError "exists-and-eq reverse terminal equality is not reflexive"
    mkExistsEqRfl lhs
  else
    semanticError "exists-and-eq reverse proof reached unsupported proposition"

private def mkExistsEqBeforeToAfterProof (input output : Expr)
    (derivation : ExistsAndEqDerivation) : MetaM Expr := do
  let (outerType, predicate, _) ← strictExistsParts input
  let .lam _ _ body _ := predicate
    | semanticError "exists-and-eq forward proof predicate is not a lambda"
  let proofInput ← canonicalExistsEqInput input
  withLocalDeclD .anonymous proofInput fun h => do
    withLocalDecl .anonymous .default outerType fun outer => do
      let openedBody := body.instantiate1 outer
      withLocalDeclD .anonymous openedBody fun bodyProof => do
        let act (crossed : Array ExistsEqProofBinder) (side : EqualityBinderSide)
            (equality : Expr) : MetaM Expr := do
          unless side == derivation.binderSide do
            semanticError "exists-and-eq forward proof orientation mismatch"
          let equalityType ← inferType equality
          let (_, lhs, rhs) ← strictEqParts equalityType
          unless Expr.equal lhs outer do
            semanticError "exists-and-eq forward equality is not oriented from outer binder"
          unless crossed.size == derivation.replacement.binderDepth do
            semanticError "exists-and-eq forward proof binder depth mismatch"
          let replacement := rhs
          let bodyProof' ← mkExistsEqForwardBodyProof openedBody bodyProof outer replacement equality
            derivation.route 0 0 crossed
          let values := crossed.map fun binder => binder.binder.fvar
          mkExistsEqIntroProof output values bodyProof' 0
        let result ← withExistsEqElimAlongRoute openedBody bodyProof outer derivation.route 0 #[] act
        let lambda ← mkLambdaFVars #[outer, bodyProof] result
        let eliminated ← mkExistsEqExistsElimWithPredicate outerType predicate h lambda
        mkLambdaFVars #[h] eliminated

private partial def withNestedExistsEqElim
    (expression proof : Expr) (remaining : Nat) (crossed : Array ExistsEqProofBinder)
    (act : Array ExistsEqProofBinder → Expr → MetaM Expr) : MetaM Expr := do
  if remaining == 0 then
    return ← act crossed proof
  let (binderType, predicate, head) ← strictExistsParts expression
  let .lam name _ body _ := predicate
    | semanticError "exists-and-eq reverse output predicate is not a lambda"
  return ← withLocalDecl name .default binderType fun binder => do
    let openedBody := body.instantiate1 binder
    withLocalDeclD .anonymous openedBody fun bodyProof => do
      let crossedBinder : ExistsEqProofBinder := {
        binder := {
          fvar := binder
          type := binderType
          head
          body := openedBody
          proof := some bodyProof
        }
        bodyProof
      }
      let inner ← withNestedExistsEqElim openedBody bodyProof (remaining - 1)
        (crossed.push crossedBinder) act
      let eliminator ← mkLambdaFVars #[binder, bodyProof] inner
      mkExistsEqExistsElim proof eliminator

private partial def resolveExistsEqReplacement
    (expression outer : Expr) (route : Array ExistsEqRouteStep) (routeIndex crossedIndex : Nat)
    (crossed : Array ExistsEqProofBinder) (side : EqualityBinderSide) : MetaM Expr := do
  if expression.isAppOfArity ``And 2 then
    let (lhs, rhs, _) ← strictAndParts expression
    let some routeStep := route[routeIndex]? |
      semanticError "exists-and-eq replacement route ended at an And"
    match routeStep with
    | .andLeft =>
        resolveExistsEqReplacement lhs outer route (routeIndex + 1) crossedIndex crossed side
    | .andRight =>
        resolveExistsEqReplacement rhs outer route (routeIndex + 1) crossedIndex crossed side
    | .existsBody =>
        semanticError "exists-and-eq replacement route selected an Exists at And"
  else if expression.isAppOfArity ``Exists 2 then
    let some routeStep := route[routeIndex]? |
      semanticError "exists-and-eq replacement route ended at an Exists"
    match routeStep with
    | .existsBody =>
        let some crossedBinder := crossed[crossedIndex]? |
          semanticError "exists-and-eq replacement binder count mismatch"
        let (binderType, predicate, _) ← strictExistsParts expression
        unless ← defEqRestored binderType crossedBinder.binder.type do
          semanticError "exists-and-eq replacement binder type mismatch"
        let .lam _ _ body _ := predicate
          | semanticError "exists-and-eq replacement predicate is not a lambda"
        let openedBody := body.instantiate1 crossedBinder.binder.fvar
        resolveExistsEqReplacement openedBody outer route (routeIndex + 1)
          (crossedIndex + 1) crossed side
    | _ => semanticError "exists-and-eq replacement route selected a non-Exists step"
  else if expression.isAppOfArity ``Eq 3 then
    unless routeIndex == route.size do
      semanticError "exists-and-eq replacement route has trailing steps"
    let (_, lhs, rhs) ← strictEqParts expression
    match side with
    | .left =>
        unless Expr.equal outer lhs && !rhs.containsFVar outer.fvarId! do
          semanticError "exists-and-eq replacement left orientation mismatch"
        return rhs
    | .right =>
        unless Expr.equal outer rhs && !lhs.containsFVar outer.fvarId! do
          semanticError "exists-and-eq replacement right orientation mismatch"
        return lhs
  else
    semanticError "exists-and-eq replacement route reached unsupported proposition"

private def mkExistsEqAfterToBeforeProof (input output : Expr)
    (derivation : ExistsAndEqDerivation) : MetaM Expr := do
  let (outerType, predicate, _) ← strictExistsParts input
  let .lam _ _ body _ := predicate
    | semanticError "exists-and-eq reverse proof predicate is not a lambda"
  let proofInput ← canonicalExistsEqInput input
  withLocalDecl .anonymous .default outerType fun outer => do
    let openedBody := body.instantiate1 outer
    withLocalDeclD .anonymous output fun h => do
      let act (crossed : Array ExistsEqProofBinder) (bodyProof : Expr) : MetaM Expr := do
        let replacement ← resolveExistsEqReplacement openedBody outer derivation.route 0 0 crossed
          derivation.binderSide
        unless !replacement.containsFVar outer.fvarId! do
          semanticError "exists-and-eq reverse replacement depends on outer binder"
        let goalBody := replaceExistsEqOuter openedBody outer replacement
        let bodyProof' ← mkExistsEqAfterBodyProof goalBody bodyProof derivation.route 0 0 crossed
        let result ← mkExistsEqExistsIntro proofInput replacement bodyProof'
        return result
      let result ← withNestedExistsEqElim output h derivation.replacement.binderDepth #[] act
      mkLambdaFVars #[h] result

private def mkExistsEqProof (input output : Expr)
    (derivation : ExistsAndEqDerivation) : MetaM Expr := do
  let before ← mkExistsEqBeforeToAfterProof input output derivation
  let after ← mkExistsEqAfterToBeforeProof input output derivation
  let iff ← mkAppM ``Iff.intro #[before, after]
  let proof ← mkAppM ``propext #[iff]
  let proof ← instantiateMVars proof
  unless !proof.hasMVar do
    semanticError "exists-and-eq proof contains metavariables after reconstruction"
  let proofType ← inferType proof
  let expected ← mkEq input output
  unless ← defEqRestored proofType expected do
    semanticError "exists-and-eq proof does not prove the exact input/output equality"
  return proof

private def interpretExistsAndEqCore (peeledInput : Expr)
    (derivation : ExistsAndEqDerivation) : MetaM Simp.Result := do
  let peeledInput ← instantiateMVars peeledInput
  if peeledInput.hasMVar then
    semanticError "exists-and-eq input contains an unassigned metavariable"
  let (output, _, _) ← interpretExistsAndEqShape peeledInput derivation
  let proof ← mkExistsEqProof peeledInput output derivation
  return { expr := output, proof? := some proof, cache := true }

def interpretExistsAndEq (peeledInput : Expr)
    (derivation : ExistsAndEqDerivation) : MetaM Simp.Result :=
  withRestoredMetaState <| interpretExistsAndEqCore peeledInput derivation

def deriveExistsAndEq? (declaration : Name) (peeledInput procedureOutput : Expr) :
    MetaM (Option ExistsAndEqDerivation) := do
  try
    withRestoredMetaState do
      let peeledInput ← instantiateMVars peeledInput
      let procedureOutput ← instantiateMVars procedureOutput
      deriveExistsAndEqCore declaration peeledInput procedureOutput
  catch _ =>
    return none


end Lean.Meta.Simp.Engine
