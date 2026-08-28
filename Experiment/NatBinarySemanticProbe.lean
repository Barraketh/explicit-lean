import ExplicitLean.SimpEngine

open Lean Meta Elab Tactic

namespace NatBinarySemanticProbe

open Lean.Meta.Simp.Engine

def mkNatBinary (operator : NatBinaryOperator) (inst lhs rhs : Expr) : Expr :=
  let declaration := match operator with
    | .add => ``HAdd.hAdd
    | .div => ``HDiv.hDiv
  mkApp6 (mkConst declaration [.zero, .zero, .zero]) (mkConst ``Nat) (mkConst ``Nat)
    (mkConst ``Nat) inst lhs rhs

def expectSome (label : String) (result : Option α) : MetaM α := do
  match result with
  | some value => pure value
  | none => throwError "{label}: semantic recognition returned none"

def expectNone (label : String) (result : Option α) : MetaM Unit := do
  if result.isSome then
    throwError "{label}: unsupported semantic input was recognized"

def expectExpr (label : String) (expected actual : Expr) : MetaM Unit := do
  unless Expr.equal expected actual do
    throwError "{label}: expression mismatch"

def expectFailure (label : String) (action : MetaM α) : MetaM Unit := do
  let saved ← Meta.saveState
  let failed ← try
    let _ ← action
    pure false
  catch _ =>
    pure true
  saved.restore
  unless failed do
    throwError "{label}: malformed derivation did not fail locally"

def roundtrip (label : String) (value : α) [BEq α] [ToJson α] [FromJson α] : MetaM Unit := do
  let decoded : α ← match Lean.fromJson? (Lean.toJson value) with
    | .ok value => pure value
    | .error message => throwError "{label}: JSON decode failed: {message}"
  unless decoded == value do
    throwError "{label}: JSON roundtrip mismatch"

def mutateViewReferencePath : NatValueView → NatValueView
  | .raw reference value depth =>
      .raw { reference with path := #[.appArgument] } value depth
  | .ofNat reference value depth witness =>
      .ofNat { reference with path := #[.appArgument] } value depth witness

def mutateViewReferencePathRhs : NatValueView → NatValueView
  | .raw reference value depth =>
      .raw { reference with path := #[.appFunction, .appArgument] } value depth
  | .ofNat reference value depth witness =>
      .ofNat { reference with path := #[.appFunction, .appArgument] } value depth witness

def mutateViewReferenceFingerprint : NatValueView → NatValueView
  | .raw reference value depth =>
      .raw { reference with fingerprint := reference.fingerprint ++ ":mutated" } value depth
  | .ofNat reference value depth witness =>
      .ofNat { reference with fingerprint := reference.fingerprint ++ ":mutated" }
        value depth witness

def mutateViewMetadataDepth : NatValueView → NatValueView
  | .raw reference value depth => .raw reference value (depth + 1)
  | .ofNat reference value depth witness => .ofNat reference value (depth + 1) witness

def mutateViewInstanceTerm : NatValueView → NatValueView
  | .raw reference value depth => .raw reference value depth
  | .ofNat reference value depth witness =>
      .ofNat reference value depth { witness with term := .literal (.nat 0) }

def mutateViewInstanceType : NatValueView → NatValueView
  | .raw reference value depth => .raw reference value depth
  | .ofNat reference value depth witness =>
      .ofNat reference value depth {
        witness with typeFingerprint := witness.typeFingerprint ++ ":mutated" }

def withLhsView (derivation : NatBinaryDerivation) (view : NatValueView) :
    NatBinaryDerivation :=
  { derivation with lhsView := view }

def withRhsView (derivation : NatBinaryDerivation) (view : NatValueView) :
    NatBinaryDerivation :=
  { derivation with rhsView := view }

def checkDependencyReconstruction : MetaM Unit := do
  let natLiteral ← reconstructDependencyTerm (mkRawNatLit 0) (.literal (.nat 13))
  expectExpr "dependency.literal.nat" (mkRawNatLit 13) natLiteral
  let intLiteral ← reconstructDependencyTerm (mkRawNatLit 0) (.literal (.int (-13 : Int)))
  expectExpr "dependency.literal.int" (mkIntLit (-13 : Int)) intLiteral
  let boolLiteral ← reconstructDependencyTerm (mkRawNatLit 0) (.literal (.bool true))
  expectExpr "dependency.literal.bool" (mkConst ``Bool.true) boolLiteral
  let stringLiteral ← reconstructDependencyTerm (mkRawNatLit 0) (.literal (.string "semantic"))
  expectExpr "dependency.literal.string" (mkStrLit "semantic") stringLiteral
  let applicationTerm :=
    .application ``Nat.succ #[] #[.literal (.nat 13)]
  let application ← reconstructDependencyTerm (mkRawNatLit 0) applicationTerm
  expectExpr "dependency.application"
    (mkApp (mkConst ``Nat.succ) (mkRawNatLit 13)) application
  let lctx ← getLCtx
  let some localDecl := lctx.findFromUserName? `n
    | throwError "dependency.local: test local n is missing"
  let localReference : LocalRef := {
    contextIndex := localDecl.index
    binderDepth := lctx.numIndices
    typeFingerprint := ← exprFingerprintHash localDecl.type
    valueFingerprint := ← localDecl.value?.mapM exprFingerprintHash
  }
  let localExpr ← reconstructDependencyTerm (mkRawNatLit 0) (.local localReference)
  expectExpr "dependency.local" (mkFVar localDecl.fvarId) localExpr
  expectFailure "dependency.local.typeFingerprint" <|
    reconstructDependencyTerm (mkRawNatLit 0)
      (.local { localReference with typeFingerprint := localReference.typeFingerprint ++ ":mutated" })
  expectFailure "dependency.local.binderDepth" <|
    reconstructDependencyTerm (mkRawNatLit 0)
      (.local { localReference with binderDepth := localReference.binderDepth + 1 })

def checkPathSteps : MetaM Unit := do
  let raw := mkRawNatLit 3
  let raw₂ := mkRawNatLit 4
  let application := mkApp2 (mkConst ``Nat.add) raw raw₂
  let metadata := Expr.mdata {} raw
  let lambda := mkLambda `x .default (mkConst ``Nat) raw
  let forallE := mkForall `x .default (mkConst ``Nat) (mkConst ``Nat)
  let letE := mkLet `x (mkConst ``Nat) raw raw
  let check (label : String) (root : Expr) (path : Array ExprPathStep) (expected : Expr) : MetaM Unit := do
    let reference := { path, fingerprint := ← exprFingerprintHash expected }
    let actual ← resolveInputSubterm root reference
    expectExpr label expected actual
  check "path.appFunction" application #[.appFunction] (mkApp (mkConst ``Nat.add) raw)
  check "path.appArgument" application #[.appArgument] raw₂
  check "path.metadataBody" metadata #[.metadataBody] raw
  check "path.lambdaType" lambda #[.lambdaType] (mkConst ``Nat)
  check "path.lambdaBody" lambda #[.lambdaBody] raw
  check "path.forallType" forallE #[.forallType] (mkConst ``Nat)
  check "path.forallBody" forallE #[.forallBody] (mkConst ``Nat)
  check "path.letType" letE #[.letType] (mkConst ``Nat)
  check "path.letValue" letE #[.letValue] raw
  check "path.letBody" letE #[.letBody] raw
  let badReference := { path := #[.metadataBody], fingerprint := ← exprFingerprintHash raw }
  expectFailure "path.constructor mismatch" (resolveInputSubterm application badReference)
  let badFingerprint := { path := #[.appArgument], fingerprint := "wrong" }
  expectFailure "path.fingerprint mismatch" (resolveInputSubterm application badFingerprint)

def runOne (label : String) (operator : NatBinaryOperator) (lhs rhs : Expr)
    (procedureOutput : Expr) : MetaM NatBinaryDerivation := do
  let input := mkNatBinary operator (match operator with
    | .add => Nat.mkInstHAdd
    | .div => Nat.mkInstHDiv) lhs rhs
  let derivation ← expectSome label (← deriveNatBinary?
    (match operator with
    | .add => `Nat.reduceAdd
    | .div => `Nat.reduceDiv) input procedureOutput)
  let interpreted ← interpretNatBinary input derivation
  expectExpr (label ++ ".interpretation") procedureOutput interpreted
  roundtrip (label ++ ".json") derivation
  pure derivation

def checkMutationMatrix (input : Expr) (derivation : NatBinaryDerivation) : MetaM Unit := do
  expectFailure "mutation.operator" <| interpretNatBinary input
    { derivation with operator := match derivation.operator with
      | .add => .div
      | .div => .add }
  expectFailure "mutation.lhs" <| interpretNatBinary input
    { derivation with lhs := derivation.lhs + 1 }
  expectFailure "mutation.rhs" <| interpretNatBinary input
    { derivation with rhs := derivation.rhs + 1 }
  expectFailure "mutation.result" <| interpretNatBinary input
    { derivation with result := derivation.result + 1 }
  expectFailure "mutation.lhs.reference.path" <| interpretNatBinary input
    (withLhsView derivation (mutateViewReferencePath derivation.lhsView))
  expectFailure "mutation.lhs.reference.fingerprint" <| interpretNatBinary input
    (withLhsView derivation (mutateViewReferenceFingerprint derivation.lhsView))
  expectFailure "mutation.rhs.reference.path" <| interpretNatBinary input
    (withRhsView derivation (mutateViewReferencePathRhs derivation.rhsView))
  expectFailure "mutation.rhs.reference.fingerprint" <| interpretNatBinary input
    (withRhsView derivation (mutateViewReferenceFingerprint derivation.rhsView))
  expectFailure "mutation.lhs.metadataDepth" <| interpretNatBinary input
    (withLhsView derivation (mutateViewMetadataDepth derivation.lhsView))
  expectFailure "mutation.rhs.metadataDepth" <| interpretNatBinary input
    (withRhsView derivation (mutateViewMetadataDepth derivation.rhsView))
  expectFailure "mutation.lhs.instance.term" <| interpretNatBinary input
    (withLhsView derivation (mutateViewInstanceTerm derivation.lhsView))
  expectFailure "mutation.lhs.instance.typeFingerprint" <| interpretNatBinary input
    (withLhsView derivation (mutateViewInstanceType derivation.lhsView))
  expectFailure "mutation.operatorInstance.term" <| interpretNatBinary input
    { derivation with operatorInstance :=
        { derivation.operatorInstance with term := .literal (.nat 0) } }
  expectFailure "mutation.operatorInstance.typeFingerprint" <| interpretNatBinary input
    { derivation with operatorInstance :=
        { derivation.operatorInstance with typeFingerprint :=
            derivation.operatorInstance.typeFingerprint ++ ":mutated" } }

@[reducible] def badHAdd : HAdd Nat Nat Nat := { hAdd := fun lhs rhs => lhs + rhs + 1 }
@[reducible] def badHDiv : HDiv Nat Nat Nat := { hDiv := fun lhs _rhs => lhs }
@[reducible] def badOfNat : OfNat Nat 7 := { ofNat := 99 }
abbrev NatAlias := Nat

def checkUnsupported : MetaM Unit := do
  let raw7 := mkRawNatLit 7
  let raw11 := mkRawNatLit 11
  let expected18 := mkNatLit 18
  let badAdd := mkNatBinary .add (mkConst ``NatBinarySemanticProbe.badHAdd) raw7 raw11
  expectNone "nonstandard HAdd" (← deriveNatBinary? `Nat.reduceAdd badAdd expected18)
  let badDiv := mkNatBinary .div (mkConst ``NatBinarySemanticProbe.badHDiv) raw7 raw11
  expectNone "nonstandard HDiv" (← deriveNatBinary? `Nat.reduceDiv badDiv (mkNatLit 0))
  let badOfNatOperand := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) raw7
    (mkConst ``NatBinarySemanticProbe.badOfNat)
  let badOfNatInput := mkNatBinary .add Nat.mkInstHAdd badOfNatOperand raw11
  expectNone "nonstandard OfNat" (← deriveNatBinary? `Nat.reduceAdd badOfNatInput expected18)
  let aliasTypeInput := mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    (mkConst ``NatBinarySemanticProbe.NatAlias) (mkConst ``Nat)
    (mkConst ``Nat) Nat.mkInstHAdd raw7 raw11
  expectNone "reducible type alias" (← deriveNatBinary? `Nat.reduceAdd aliasTypeInput expected18)
  let internalMetadata := mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat)
    (Expr.mdata {} raw7) (mkInstOfNatNat raw7)
  let internalMetadataInput := mkNatBinary .add Nat.mkInstHAdd internalMetadata raw11
  expectNone "numeral-internal metadata" (← deriveNatBinary? `Nat.reduceAdd internalMetadataInput expected18)
  let malformed := mkApp6 (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat) Nat.mkInstHAdd
    (mkConst ``Nat) raw11
  expectNone "open unsupported shape" (← deriveNatBinary? `Nat.reduceAdd malformed expected18)
  let mvar ← mkFreshExprMVar (mkConst ``Nat)
  let openInput := mkNatBinary .add Nat.mkInstHAdd mvar raw11
  expectNone "open metavariable shape" (← deriveNatBinary? `Nat.reduceAdd openInput expected18)

elab "check_nat_binary_semantic" : tactic => withMainContext do
  checkPathSteps
  checkDependencyReconstruction
  let raw7 := mkRawNatLit 7
  let raw11 := mkRawNatLit 11
  let raw17 := mkRawNatLit 17
  let raw20 := mkRawNatLit 20
  let raw5 := mkRawNatLit 5
  let raw0 := mkRawNatLit 0
  let addRawInput := mkNatBinary .add Nat.mkInstHAdd raw7 raw11
  let _ ← runOne "add.raw" .add raw7 raw11 (mkNatLit 18)
  expectExpr "add.raw.input" addRawInput (mkNatBinary .add Nat.mkInstHAdd raw7 raw11)
  let _ ← runOne "div.raw" .div raw17 raw5 (mkNatLit 3)
  let _ ← runOne "div.exact" .div raw20 raw5 (mkNatLit 4)
  let _ ← runOne "div.numerator.zero" .div raw0 raw5 (mkNatLit 0)
  let _ ← runOne "div.divisor.zero" .div raw17 raw0 (mkNatLit 0)
  let _ ← runOne "add.ofNat" .add (mkNatLit 7) (mkNatLit 11) (mkNatLit 18)
  let metadataLhs := Expr.mdata {} (mkNatLit 7)
  let metadataRhs := Expr.mdata {} (mkRawNatLit 11)
  let metadataInput := mkNatBinary .add Nat.mkInstHAdd metadataLhs metadataRhs
  let metadataDerivation ← runOne "add.outerMetadata" .add metadataLhs metadataRhs (mkNatLit 18)
  unless metadataDerivation.lhsView matches .ofNat _ _ 1 _ do
    throwError "add.outerMetadata: metadata depth was not recorded"
  let some witnessPath := match metadataDerivation.lhsView with
      | .ofNat _ _ _ witness =>
          match witness.term with
          | .input reference => some reference.path
          | _ => none
      | _ => none
    | throwError "add.outerMetadata: missing input instance witness"
  unless witnessPath.contains .metadataBody do
    throwError "add.outerMetadata: witness path did not cross metadataBody"
  expectExpr "add.outerMetadata.input" metadataInput
    (mkNatBinary .add Nat.mkInstHAdd metadataLhs metadataRhs)
  checkMutationMatrix metadataInput metadataDerivation
  checkUnsupported
  logInfo "SIMP_ENGINE_NAT_BINARY_SEMANTIC add=raw,ofNat,metadata div=zero,numeratorZero,exact,inexact: ok"

example (n : Nat) : True := by
  check_nat_binary_semantic
  trivial

end NatBinarySemanticProbe
