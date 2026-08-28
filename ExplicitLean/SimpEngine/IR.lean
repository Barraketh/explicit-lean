module
prelude

public import Lean.Meta.Tactic.Simp.Types
public import Lean.Data.Json.FromToJson

public section

namespace Lean.Meta.Simp.Engine

def nameJsonParts : Name → Array Json
  | .anonymous => #[]
  | .str parent value =>
      (nameJsonParts parent).push (.arr #[.str "str", .str value])
  | .num parent value =>
      (nameJsonParts parent).push (.arr #[.str "num", toJson value])

def nameFromJson (json : Json) : Except String Name := do
  let parts ← json.getArr?
  parts.foldlM (init := .anonymous) fun name part =>
    match part with
    | .arr #[.str "str", .str value] => return .str name value
    | .arr #[.str "num", value] => return .num name (← fromJson? value)
    | _ => throw s!"invalid schema-27 name component: {part.compress}"

local instance certificateNameToJson : ToJson Name where
  toJson name := .arr (nameJsonParts name)

local instance certificateNameFromJson : FromJson Name where
  fromJson? := nameFromJson

structure EngineId where
  leanVersion : String
  leanCommit : String
  certificateSchema : Nat
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

def engineId : EngineId := {
  leanVersion := "4.32.2"
  leanCommit := "f3b06c705e6c85f5314019d5d3baab0fec5b580c"
  certificateSchema := 27
}

inductive Mode where
  | simp
  | dsimp
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

inductive Phase where
  | pre
  | post
  | dpre
  | dpost
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

inductive ChildMode where
  | simp
  | dsimp
  | fixed
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

inductive StepDisposition where
  | done
  | visit
  | continueNone
  | continueSome
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

inductive SimprocKind where
  | simp
  | dsimp
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

/-- Diagnostic size of a simproc result. `treeNodes` counts an expression as if
    sharing were expanded, while `dagNodes` counts structurally distinct
    expression nodes. Tree counting saturates before diagnostic observation can
    itself create an unbounded-size integer. -/
structure ExprSize where
  treeNodes : Nat
  treeNodesCapped : Bool
  dagNodes : Nat
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

inductive ProjectionBranch where
  | requestedClass
  | constructorClass
  | structure
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive DeltaStrategy where
  | requestedSmart
  | requestedPartial
  | requestedOrdinary
  | autoSmart
  | autoMatch
  | ground
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive LocalDefReason where
  | zetaDelta
  | requested
  | implementationDetail
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive ForallBranch where
  | implicationContextual
  | implicationPlain
  | propositionDomainTransport
  | propositionDomainDSimp
  | nonPropositionDSimp
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive ArithHandler where
  | natRelation
  | natEquality
  | natExpression
  | natDivisibility
  | intRelation
  | intEquality
  | intExpression
  | intDivisibility
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive GeneratedCongruenceArgKind where
  | fixed
  | fixedNoParam
  | eq
  | cast
  | heq
  | subsingletonInst
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive PremiseTerminal where
  | localAssumption (contextIndex : Nat)
  | equationHypothesis
  | dischargeRfl
  | isTrue
  | failed
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure ExprFingerprint where
  printable : String
  fingerprint : String
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

/-! Schema-27's passive `fieldEq` audit.  These values are deliberately part
of the common IR rather than the Mathlib-dependent implementation module: a
recorded observation remains JSON-stable even when its audit is not used as a
replay authority. -/

inductive FieldEqStrategy where
  | assumption
  | normNum
  | positivity
  | recursiveSimp
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

inductive FieldEqOutcome where
  | success
  | notApplicable
  | returnedNonTrue
  | terminalNotTrue
  | conversionFailed
  | threw
  | failed
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure FieldEqSimpStateSummary where
  numSteps : Nat
  /-- Canonical, complete stage-1 cache entries, including key/result/proof
      fingerprints and each result's cache flag. -/
  cache : String
  /-- Canonical complete congruence-cache entries. -/
  congrCache : String
  /-- Canonical complete dsimp-cache entries. -/
  dsimpCache : String
  /-- Sorted theorem origins and use counts in `State.usedTheorems`. -/
  usedTheoremOrigins : Array String := #[]
  /-- Complete sorted diagnostic counters and bad-key entries. -/
  diagnostics : Array String := #[]
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure FieldEqAttempt where
  strategy : FieldEqStrategy
  outcome : FieldEqOutcome
  proofFingerprint : Option String := none
  beforeMetaEffectFingerprint : String := ""
  afterMetaEffectFingerprint : String := ""
  beforeSimpState : Option FieldEqSimpStateSummary := none
  afterSimpState : Option FieldEqSimpStateSummary := none
  terminalExpressionFingerprint : Option String := none
  terminalProofFingerprint : Option String := none
  terminalCache : Option Bool := none
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure FieldEqDischargeCall where
  ordinal : Nat
  parentOrdinal : Option Nat := none
  recursionDepth : Nat := 0
  proposition : ExprFingerprint
  size : ExprSize
  attempts : Array FieldEqAttempt := #[]
  outcome : FieldEqOutcome
  proofFingerprint : Option String := none
  terminalExpressionFingerprint : Option String := none
  terminalProofFingerprint : Option String := none
  terminalCache : Option Bool := none
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure FieldEqProcedureResult where
  disposition : StepDisposition
  outputFingerprint : String
  proofFingerprint : Option String := none
  cache : Option Bool := none
  simpState : FieldEqSimpStateSummary
  metaEffectFingerprint : String
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure FieldEqShadowEvidence where
  exact : Bool
  authoritative : FieldEqProcedureResult
  shadow : FieldEqProcedureResult
  diagnostic : Option String := none
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure FieldEqAudit where
  initialMetaEffectFingerprint : String
  authoritativeFinalMetaEffectFingerprint : String
  shadowFinalMetaEffectFingerprint : String
  dischargeCalls : Array FieldEqDischargeCall := #[]
  shadow : FieldEqShadowEvidence
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure LocalRef where
  contextIndex : Nat
  binderDepth : Nat
  typeFingerprint : String
  valueFingerprint : Option String := none
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive ExprPathStep where
  | appFunction
  | appArgument
  | metadataBody
  | lambdaType
  | lambdaBody
  | forallType
  | forallBody
  | letType
  | letValue
  | letBody
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure InputSubtermRef where
  path : Array ExprPathStep
  fingerprint : String
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive LevelDescriptor where
  | zero
  | succ (level : LevelDescriptor)
  | max (lhs rhs : LevelDescriptor)
  | imax (lhs rhs : LevelDescriptor)
  | param (name : Name)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive LiteralValue where
  | nat (value : Nat)
  | int (value : Int)
  | bool (value : Bool)
  | string (value : String)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive DependencyTerm where
  | input (reference : InputSubtermRef)
  | local (reference : LocalRef)
  | literal (value : LiteralValue)
  | application (declaration : Name) (levels : Array LevelDescriptor)
      (arguments : Array DependencyTerm)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure InstanceWitness where
  term : DependencyTerm
  typeFingerprint : String
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive NatValueView where
  | raw (reference : InputSubtermRef) (value : Nat) (metadataDepth : Nat)
  | ofNat (reference : InputSubtermRef) (value : Nat) (metadataDepth : Nat)
      («instance» : InstanceWitness)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive NatBinaryOperator where
  | add
  | div
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure NatBinaryDerivation where
  operator : NatBinaryOperator
  lhs : Nat
  rhs : Nat
  result : Nat
  lhsView : NatValueView
  rhsView : NatValueView
  operatorInstance : InstanceWitness
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure FinLiteralGuard where
  modulus : Nat
  source : Nat
  normalized : Nat
  modulusView : NatValueView
  sourceView : NatValueView
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure FinLiteralModuloDerivation where
  modulus : Nat
  source : Nat
  normalized : Nat
  modulusView : NatValueView
  sourceView : NatValueView
  literalInstance : InstanceWitness
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure IntNegateLiteralDerivation where
  magnitude : Nat
  result : Int
  argument : InputSubtermRef
  numeral : InputSubtermRef
  numeralMetadataDepth : Nat
  outerNegInstance : InstanceWitness
  innerNegInstance : InstanceWitness
  literalInstance : InstanceWitness
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive NatEvalBinaryOperator where
  | natAdd | add | hAdd
  | natSub | sub | hSub
  | natMul | mul | hMul
  | natDiv | div | hDiv
  | natMod | mod | hMod
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive NatEvalPowerOperator where
  | natPow | natPowClass | pow | hPow
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive NatEvalTrace where
  | raw (value : Nat)
  | metadata (body : NatEvalTrace)
  | zero
  | assigned (assignmentFingerprint : String) (value : Nat) (body : NatEvalTrace)
  | ofNat («instance» : InstanceWitness) (numeral : NatEvalTrace) (result : Nat)
  | succ (argument : NatEvalTrace) (result : Nat)
  | binary (operator : NatEvalBinaryOperator) («instance» : Option InstanceWitness)
      (lhs rhs : NatEvalTrace) (result : Nat)
  | power (operator : NatEvalPowerOperator) («instance» : Option InstanceWitness)
      (base exponent : NatEvalTrace) (exponentThreshold result : Nat)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive NatOffsetOperator where
  | natAdd
  | add
  | hAdd
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

mutual
  inductive NatOffsetTrace where
    | base (reference : InputSubtermRef)
    | succ (trace : NatOffsetTrace)
    | add (operator : NatOffsetOperator) (instance? : Option InstanceWitness)
        (lhs : NatOffsetTrace) (rhs : NatEvalTrace)
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson
end

inductive ConstructorViewOrigin where
  | immediate (arguments : Array InputSubtermRef)
  | natLiteral (view : NatValueView)
  | natOffset (trace : NatOffsetTrace) (offset : Nat)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure ConstructorView where
  operand : InputSubtermRef
  constructor : Name
  inductiveName : Name
  constructorIndex : Nat
  origin : ConstructorViewOrigin
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure ConstructorDisjointWitness where
  typeReference : InputSubtermRef
  inductiveName : Name
  lhs : ConstructorView
  rhs : ConstructorView
  ctorIdxDeclaration : Name
  noConfusionDeclaration : Name
  eqFalseDeclaration : Name
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure FinMkCanonicalDerivation where
  modulus : Nat
  value : Nat
  normalized : Nat
  modulusReference : InputSubtermRef
  modulusTrace : NatEvalTrace
  valueView : NatValueView
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

/- A single reduction performed by the vector lookup recognizer.  The
   expression itself is deliberately not serialized: replay repeats the named
   operation and checks both fingerprints before it consumes the resulting
   view. -/
structure VectorWhnfWitness where
  inputFingerprint : String
  outputFingerprint : String
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure VectorConsView where
  whnf : VectorWhnfWitness
  arity : Nat
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure VectorSpine where
  root : VectorConsView
  nested : Array VectorConsView := #[]
  stop : VectorWhnfWitness
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive VectorIndexConstructor where
  | positive
  | negative
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure VectorIndexView where
  wholeFingerprint : String
  value : Int
  constructor : VectorIndexConstructor
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive VectorTailLength where
  | closed (whnf : VectorWhnfWitness) (value : Nat) (canonicalFingerprint : String)
  | offset (whnf : VectorWhnfWitness) (trace : NatOffsetTrace) (knownOffset : Nat)
      (canonicalFingerprint : String)
  | symbolic (whnf : VectorWhnfWitness) (original : InputSubtermRef)
      (canonicalFingerprint : String)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive VectorSelection where
  | prefix (index : Nat)
  | tail (residual : Nat) (index : DependencyTerm) (indexTypeFingerprint : String)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

structure VectorLookupDerivation where
  spine : VectorSpine
  rawIndex : Int
  indexView : VectorIndexView
  tailLength : VectorTailLength
  wrappedIndex : Nat
  selection : VectorSelection
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive ValueGuard where
  | intNegOfNatSyntax (argument : InputSubtermRef)
  | finLiteralInRange (derivation : FinLiteralGuard)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

inductive ValueOperation where
  | natBinary (derivation : NatBinaryDerivation)
  | finLiteralModulo (derivation : FinLiteralModuloDerivation)
  | intNegateLiteral (derivation : IntNegateLiteralDerivation)
  | finMkCanonical (derivation : FinMkCanonicalDerivation)
  deriving Repr, BEq, Lean.ToJson, Lean.FromJson

instance : Inhabited LevelDescriptor := ⟨.zero⟩
instance : Inhabited DependencyTerm := ⟨.literal (.nat 0)⟩
instance : Inhabited InstanceWitness := ⟨{ term := .literal (.nat 0), typeFingerprint := "" }⟩
instance : Inhabited NatValueView := ⟨.raw { path := #[], fingerprint := "" } 0 0⟩
instance : Inhabited NatBinaryDerivation := ⟨{
  operator := .add
  lhs := 0
  rhs := 0
  result := 0
  lhsView := default
  rhsView := default
  operatorInstance := default
}⟩
instance : Inhabited FinLiteralGuard := ⟨{
  modulus := 1
  source := 0
  normalized := 0
  modulusView := default
  sourceView := default
}⟩
instance : Inhabited FinLiteralModuloDerivation := ⟨{
  modulus := 1
  source := 1
  normalized := 0
  modulusView := default
  sourceView := default
  literalInstance := default
}⟩
instance : Inhabited IntNegateLiteralDerivation := ⟨{
  magnitude := 0
  result := 0
  argument := default
  numeral := default
  numeralMetadataDepth := 0
  outerNegInstance := default
  innerNegInstance := default
  literalInstance := default
}⟩
instance : Inhabited NatEvalTrace := ⟨.raw 0⟩
instance : Inhabited NatOffsetTrace := ⟨.base default⟩
instance : Inhabited ConstructorViewOrigin := ⟨.immediate #[]⟩
instance : Inhabited ConstructorView := ⟨{
  operand := default
  constructor := .anonymous
  inductiveName := .anonymous
  constructorIndex := 0
  origin := default
}⟩
instance : Inhabited ConstructorDisjointWitness := ⟨{
  typeReference := default
  inductiveName := .anonymous
  lhs := default
  rhs := default
  ctorIdxDeclaration := .anonymous
  noConfusionDeclaration := .anonymous
  eqFalseDeclaration := .anonymous
}⟩
instance : Inhabited FinMkCanonicalDerivation := ⟨{
  modulus := 1
  value := 0
  normalized := 0
  modulusReference := default
  modulusTrace := default
  valueView := default
}⟩
instance : Inhabited VectorWhnfWitness := ⟨{
  inputFingerprint := ""
  outputFingerprint := ""
}⟩
instance : Inhabited VectorConsView := ⟨{
  whnf := default
  arity := 0
}⟩
instance : Inhabited VectorSpine := ⟨{
  root := default
  nested := #[]
  stop := default
}⟩
instance : Inhabited VectorIndexConstructor := ⟨.positive⟩
instance : Inhabited VectorIndexView := ⟨{
  wholeFingerprint := ""
  value := 0
  constructor := .positive
}⟩
instance : Inhabited VectorTailLength := ⟨.symbolic default default ""⟩
instance : Inhabited VectorSelection := ⟨.prefix 0⟩
instance : Inhabited VectorLookupDerivation := ⟨{
  spine := default
  rawIndex := 0
  indexView := default
  tailLength := default
  wrappedIndex := 0
  selection := .prefix 0
}⟩
instance : Inhabited ValueGuard := ⟨.intNegOfNatSyntax default⟩
instance : Inhabited ValueOperation := ⟨.natBinary default⟩

inductive NestedStatePolicy where
  | sharedSimpState
  | isolatedStats
  | isolatedDiscard
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive NestedConfigPolicy where
  | inherited
  | defaultSimp
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure ScopedLocalRef where
  ordinal : Nat
  typeFingerprint : String
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive RuleOrigin where
  | decl (name : Name)
  | equation (declaration : Name) (index : Nat)
  | syntax (source : String)
  | local (subject : LocalRef)
  | other (name : Name)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive PathStep where
  | simpCall (ordinal : Nat)
  | dsimpCall (ordinal : Nat)
  | simprocInternal (foldOrdinal : Nat) (candidateIndex : Nat) (nestedIndex : Nat)
  | preVisit (iteration : Nat)
  | reductionVisit (iteration : Nat)
  | postRestart (iteration : Nat)
  | projectionMajor (mode : Mode)
  | appFunction
  | appArgument (index : Nat) (mode : ChildMode)
  | userCongrHypothesis (theoremName : Name) (index : Nat)
  | autoCongrArgument (index : Nat) (mode : ChildMode)
  | matchDiscriminant (index : Nat) (mode : ChildMode)
  | lambdaDomain (index : Nat)
  | lambdaBody
  | forallDomain (index : Nat)
  | forallBody
  | metadataBody
  | implicationDomain
  | implicationBody
  | letType (index : Nat)
  | letValue (index : Nat) (mode : ChildMode)
  | letBody
  | haveValue (index : Nat) (mode : ChildMode)
  | haveBody
  | premise (index : Nat)
  | ground
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure ExecutionPath where
  steps : Array PathStep := #[]
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

structure SimprocObservation where
  path : ExecutionPath
  name : Name
  phase : Phase
  phaseInvocationOrdinal : Nat := 0
  setIndex : Nat := 0
  inputFingerprint : String
  outputFingerprint : String
  outputChanged : Bool
  stepDisposition : StepDisposition
  definitional : Bool
  procedureKind : SimprocKind
  numExtraArgs : Nat
  executed : Bool
  proofPresent : Bool
  cache : Option Bool
  outputSize : Option ExprSize
  /-- Optional Mathlib-specific schema-27 diagnostics.  This payload is
      observational only; replay never consults it as an authority. -/
  fieldEqAudit : Option FieldEqAudit := none
  deriving Inhabited, Repr, BEq, Hashable, Lean.ToJson, Lean.FromJson

/-- A lossless ordered committed simproc trace. Recorder-state rollback removes
    calls made only by failed speculative candidates. The JSON representation
    dictionary-compresses repeated observations while retaining one order index
    for every committed invocation. -/
structure SimprocTrace where
  observations : Array SimprocObservation := #[]
  deriving Inhabited, Repr, BEq

def SimprocTrace.size (trace : SimprocTrace) : Nat :=
  trace.observations.size

def SimprocTrace.isEmpty (trace : SimprocTrace) : Bool :=
  trace.observations.isEmpty

instance : Lean.ToJson SimprocTrace where
  toJson trace :=
    let (dictionary, _, order) := trace.observations.foldl
      (init := (#[], ({} : Std.HashMap SimprocObservation Nat), #[]))
      fun (dictionary, indices, order) observation =>
        match indices.get? observation with
        | some index => (dictionary, indices, order.push index)
        | none =>
            let index := dictionary.size
            (dictionary.push observation, indices.insert observation index,
              order.push index)
    Json.mkObj [
      ("dictionary", Lean.toJson dictionary),
      ("order", Lean.toJson order)
    ]

instance : Lean.FromJson SimprocTrace where
  fromJson? json := do
    let dictionary ← json.getObjValAs? (Array SimprocObservation) "dictionary"
    let order ← json.getObjValAs? (Array Nat) "order"
    let observations ← order.mapM fun index => do
      let some observation := dictionary[index]?
        | throw s!"invalid schema-27 simproc dictionary index: {index}/{dictionary.size}"
      return observation
    return { observations }

structure RuleRef where
  source : String
  origin : RuleOrigin
  inverse : Bool
  phase : Phase
  variant : Nat
  ruleFingerprint : String
  lhsFingerprint : String
  indexMode : Bool
  numExtraArgs : Nat
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure MatchEnvelope where
  binderAssignments : Array String := #[]
  instanceAssignments : Array String := #[]
  proofPresent : Bool
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive Reduction where
  | instantiateMVars
  | beta
  | projection (structureName : Name) (field : Nat)
  | projectionFunction (name : Name) (branch : ProjectionBranch)
  | iota
  | zetaUsed (zetaHave : Bool)
  | zetaUnused
  | delta (name : Name) (strategy : DeltaStrategy)
  | foldRawNatLit
  | localDef (subject : LocalRef) (reason : LocalDefReason)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive Builtin where
  | decideTrue
  | decideFalse
  | arith (handler : ArithHandler)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

mutual
  structure NestedProgram where
    program : Program
    simprocs : SimprocTrace
    statePolicy : NestedStatePolicy
    configPolicy : NestedConfigPolicy
    dischargeDepthIncrement : Nat
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  inductive IteDecision where
    | trueBranch
    | falseBranch
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure IteSelection where
    decision : IteDecision
    conditionRef : InputSubtermRef
    selectedBranchRef : InputSubtermRef
    conditionProgram : NestedProgram
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure HeadBetaWitness where
    inputFingerprint : String
    outputFingerprint : String
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure DIteSelection where
    decision : IteDecision
    conditionRef : InputSubtermRef
    selectedBranchRef : InputSubtermRef
    conditionProgram : NestedProgram
    headBeta : HeadBetaWitness
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  inductive ExistsEqRouteStep where
    | andLeft
    | andRight
    | existsBody
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  inductive EqualityBinderSide where
    | left
    | right
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure BoundSubtermRef where
    reference : InputSubtermRef
    binderDepth : Nat
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure ExistsAndEqDerivation where
    route : Array ExistsEqRouteStep
    binderSide : EqualityBinderSide
    replacement : BoundSubtermRef
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  inductive SemanticSimproc where
    | canonicalValue (operation : ValueOperation)
    | valueGuard (guard : ValueGuard)
    | constructorDisjoint (witness : ConstructorDisjointWitness)
    | iteSelect (selection : IteSelection)
    | diteSelect (selection : DIteSelection)
    | vectorLookup (derivation : VectorLookupDerivation)
    | existentialEqualityElim (derivation : ExistsAndEqDerivation)
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure PremiseProgram where
    resolvedPropositionFingerprint : String
    program : Program
    terminal : PremiseTerminal
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  inductive CongruenceChoice where
    | user (theoremName : Name) (priority : Nat) (hypothesisPositions : Array Nat)
        (theoremFingerprint : String) (matchEnvelope : MatchEnvelope)
        (premises : Array PremiseProgram)
    | userAttemptFailed (theoremName : Name) (priority : Nat)
        (hypothesisPositions : Array Nat) (theoremFingerprint : String)
        (matchEnvelope : MatchEnvelope) (premises : Array PremiseProgram)
    | generated (theoremTypeFingerprint proofFingerprint : String)
        (argumentKinds : Array GeneratedCongruenceArgKind)
        (arguments : Array ChildMode) (synthesizedAssignments : Array String)
    | generatedAttemptFailed
    | generic (arguments : Array ChildMode)
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  inductive Structural where
    | phaseOutcome (phase : Phase) (invocationOrdinal : Nat)
        (disposition : StepDisposition) (outputFingerprint : String) (proofPresent : Bool)
    | proofSkip (invocationOrdinal : Nat) (typeFingerprint : String)
    | unassignedMVarStop (simpStepOrdinal : Nat)
    | cacheHit (sourcePath : ExecutionPath) (sourceIndex : Nat)
    | congruence (invocationOrdinal : Nat) (choice : CongruenceChoice)
    | projectionMajor (structureName : Name) (field : Nat) (mode : ChildMode)
    | matchDiscriminants (count : Nat)
    | matchDiscriminantsAttemptFailed (count : Nat)
    | lambdaTelescope (count : Nat)
    | forallBranch (choice : ForallBranch)
    | contextualScope (locals : Array ScopedLocalRef)
    | letToHave
    | haveTelescope (fixed used : Array Bool)
    | dropUnusedHave (index : Nat)
    | dsimpCacheHit (sourcePath : ExecutionPath) (sourceIndex : Nat)
    | dsimpTransform (usedLetOnly skipInstances : Bool)
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure SimprocCandidateEvent where
    declaration : Name
    procedureKind : SimprocKind
    semantics : SemanticSimproc
    setIndex : Nat
    registryPost : Bool
    inputFingerprint : String
    peeledInputFingerprint : String
    extraArgumentFingerprints : Array String
    procedureOutputFingerprint : String
    outputFingerprint : String
    numExtraArgs : Nat
    disposition : StepDisposition
    proofPresent : Bool
    cache : Option Bool
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure SimprocFold where
    phase : Phase
    candidates : Array SimprocCandidateEvent
    finalOutputFingerprint : String
    finalDisposition : StepDisposition
    finalProofPresent : Bool
    finalCache : Option Bool
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  inductive Operation where
    | rewrite (rule : RuleRef) (matchEnvelope : MatchEnvelope)
        (premises : Array PremiseProgram)
    | rewriteAttemptFailed (rule : RuleRef) (matchEnvelope : MatchEnvelope)
        (premises : Array PremiseProgram)
    | reduce (reduction : Reduction)
    | builtin (builtin : Builtin)
    | semanticSimproc (fold : SimprocFold)
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure Event where
    path : ExecutionPath
    phase : Phase
    invocationOrdinal : Nat
    operation : Operation
    inputFingerprint : String
    outputFingerprint : String
    stepDisposition : StepDisposition
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure StructuralWitness where
    path : ExecutionPath
    witness : Structural
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  structure Program where
    initialFingerprint : String := ""
    finalFingerprint : String := ""
    structural : Array StructuralWitness := #[]
    events : Array Event := #[]
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson
end

instance : Inhabited Program := ⟨{}⟩
instance : Inhabited CongruenceChoice := ⟨.generatedAttemptFailed⟩
instance : Inhabited Structural := ⟨.matchDiscriminants 0⟩
instance : Inhabited NestedProgram := ⟨{
  program := default
  simprocs := default
  statePolicy := .sharedSimpState
  configPolicy := .inherited
  dischargeDepthIncrement := 0
}⟩
instance : Inhabited IteDecision := ⟨.falseBranch⟩
instance : Inhabited IteSelection := ⟨{
  decision := default
  conditionRef := default
  selectedBranchRef := default
  conditionProgram := default
}⟩
instance : Inhabited HeadBetaWitness := ⟨{
  inputFingerprint := ""
  outputFingerprint := ""
}⟩
instance : Inhabited DIteSelection := ⟨{
  decision := default
  conditionRef := default
  selectedBranchRef := default
  conditionProgram := default
  headBeta := default
}⟩
instance : Inhabited ExistsEqRouteStep := ⟨.andLeft⟩
instance : Inhabited EqualityBinderSide := ⟨.left⟩
instance : Inhabited BoundSubtermRef := ⟨{
  reference := default
  binderDepth := 0
}⟩
instance : Inhabited ExistsAndEqDerivation := ⟨{
  route := #[]
  binderSide := .left
  replacement := default
}⟩
instance : Inhabited SemanticSimproc := ⟨.canonicalValue default⟩
instance : Inhabited SimprocCandidateEvent := ⟨{
  declaration := .anonymous
  procedureKind := .simp
  semantics := .canonicalValue (.natBinary {
    operator := .add
    lhs := 0
    rhs := 0
    result := 0
    lhsView := .raw { path := #[], fingerprint := "" } 0 0
    rhsView := .raw { path := #[], fingerprint := "" } 0 0
    operatorInstance := {
      term := .literal (.nat 0)
      typeFingerprint := ""
    }
  })
  setIndex := 0
  registryPost := false
  inputFingerprint := ""
  peeledInputFingerprint := ""
  extraArgumentFingerprints := #[]
  procedureOutputFingerprint := ""
  outputFingerprint := ""
  numExtraArgs := 0
  disposition := .continueNone
  proofPresent := false
  cache := none
}⟩
instance : Inhabited SimprocFold := ⟨{
  phase := .pre
  candidates := #[]
  finalOutputFingerprint := ""
  finalDisposition := .continueNone
  finalProofPresent := false
  finalCache := none
}⟩

inductive DeferredReason where
  | simproc (name : Name) (phase : Phase)
  | customDischarger
  | simprocAndCustomDischarger (name : Name) (phase : Phase)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure Recording where
  engine : EngineId := engineId
  program : Program
  deferred : Option DeferredReason := none
  simprocs : SimprocTrace := {}
  coveredBranches : Array String := #[]
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive SubjectRef where
  | target
  | local (subject : LocalRef)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive ProofPresence where
  | explicit
  | definitional
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive EtaStructPolicy where
  | all
  | notClasses
  | none
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive SubjectTerminal where
  | targetTrue (proofPresence : ProofPresence)
  | targetTransport (proofPresence : ProofPresence)
  | localFalse (proofPresence : ProofPresence)
  | localDefEqReplace
  | localAssertClear (proofPresence : ProofPresence)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure SubjectProgram where
  subject : SubjectRef
  initialFingerprint : String
  program : Program
  terminal : SubjectTerminal
  deferred : Option DeferredReason := none
  simprocs : SimprocTrace := {}
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure StateFingerprint where
  targetFingerprint : String
  localContextFingerprint : String
  metavariableContextFingerprint : String
  goalCount : Nat
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure ReplayConfig where
  maxSteps : Nat
  maxDischargeDepth : Nat
  contextual : Bool
  memoize : Bool
  singlePass : Bool
  zeta : Bool
  dsimp : Bool
  beta : Bool
  eta : Bool
  etaStruct : EtaStructPolicy
  proj : Bool
  iota : Bool
  zetaDelta : Bool
  zetaHave : Bool
  zetaUnused : Bool
  autoUnfold : Bool
  unfoldPartialApp : Bool
  letToHave : Bool
  decide : Bool
  arith : Bool
  ground : Bool
  index : Bool
  implicitDefEqProofs : Bool
  failIfUnchanged : Bool
  catchRuntime : Bool
  congrConsts : Bool
  bitVecOfNat : Bool
  warnExponents : Bool
  locals : Bool
  instances : Bool
  dsimpProofs : Bool
  reducibleClassField : Bool
  smartUnfolding : Bool
  useBackwardDefEq : Bool
  dsimpUseDefEqAttr : Bool
  skipAssignedInstances : Bool
  simprocsEnabled : Bool
  userConfigFingerprint : String
  metaConfigFingerprint : String
  indexConfigFingerprint : String
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure Certificate where
  engine : EngineId := engineId
  config : ReplayConfig
  subjects : Array SubjectProgram := #[]
  initialState : StateFingerprint
  finalState : StateFingerprint
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

end Lean.Meta.Simp.Engine
