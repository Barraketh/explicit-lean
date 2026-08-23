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
    | _ => throw s!"invalid schema-16 name component: {part.compress}"

local instance schema16NameToJson : ToJson Name where
  toJson name := .arr (nameJsonParts name)

local instance schema16NameFromJson : FromJson Name where
  fromJson? := nameFromJson

structure EngineId where
  leanVersion : String
  leanCommit : String
  certificateSchema : Nat
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

def engineId : EngineId := {
  leanVersion := "4.32.2"
  leanCommit := "f3b06c705e6c85f5314019d5d3baab0fec5b580c"
  certificateSchema := 16
}

inductive Mode where
  | simp
  | dsimp
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive Phase where
  | pre
  | post
  | dpre
  | dpost
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive ChildMode where
  | simp
  | dsimp
  | fixed
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive StepDisposition where
  | done
  | visit
  | continueNone
  | continueSome
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

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
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure LocalRef where
  contextIndex : Nat
  binderDepth : Nat
  typeFingerprint : String
  valueFingerprint : Option String := none
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure ScopedLocalRef where
  ordinal : Nat
  typeFingerprint : String
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive RuleOrigin where
  | decl (name : Name)
  | syntax (source : String)
  | local (subject : LocalRef)
  | other (name : Name)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive PathStep where
  | simpCall (ordinal : Nat)
  | dsimpCall (ordinal : Nat)
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
  | forallDomain
  | forallBody
  | implicationDomain
  | implicationBody
  | letType (index : Nat)
  | letValue (index : Nat) (mode : ChildMode)
  | letBody
  | haveValue (index : Nat) (mode : ChildMode)
  | haveBody
  | premise (index : Nat)
  | ground
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure ExecutionPath where
  steps : Array PathStep := #[]
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure RuleRef where
  source : String
  origin : RuleOrigin
  inverse : Bool
  phase : Phase
  variant : Nat
  ruleFingerprint : String
  lhsFingerprint : String
  indexMode : Bool
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

inductive CongruenceChoice where
  | user (theoremName : Name) (priority : Nat) (hypothesisPositions : Array Nat)
  | userAttemptFailed (theoremName : Name) (priority : Nat)
      (hypothesisPositions : Array Nat)
  | generated (shapeFingerprint : String) (arguments : Array ChildMode)
      (synthesizedAssignments : Array String)
  | generatedAttemptFailed
  | generic (arguments : Array ChildMode)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

inductive Structural where
  | phaseOutcome (phase : Phase) (invocationOrdinal : Nat)
      (disposition : StepDisposition) (outputFingerprint : String) (proofPresent : Bool)
  | proofSkip (invocationOrdinal : Nat) (typeFingerprint : String)
  | unassignedMVarStop (simpStepOrdinal : Nat)
  | cacheHit (sourcePath : ExecutionPath)
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
  | dsimpCacheHit (sourcePath : ExecutionPath)
  | dsimpTransform (usedLetOnly skipInstances : Bool)
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

mutual
  structure PremiseProgram where
    propositionFingerprint : String
    program : Program
    terminal : PremiseTerminal
    deriving Repr, BEq, Lean.ToJson, Lean.FromJson

  inductive Operation where
    | rewrite (rule : RuleRef) (matchEnvelope : MatchEnvelope)
        (premises : Array PremiseProgram)
    | rewriteAttemptFailed (rule : RuleRef) (matchEnvelope : MatchEnvelope)
        (premises : Array PremiseProgram)
    | reduce (reduction : Reduction)
    | builtin (builtin : Builtin)
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

inductive DeferredReason where
  | simproc (name : Name) (phase : Phase)
  | customDischarger
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure SimprocObservation where
  path : ExecutionPath
  name : Name
  phase : Phase
  inputFingerprint : String
  outputFingerprint : String
  stepDisposition : StepDisposition
  definitional : Bool
  deriving Inhabited, Repr, BEq, Lean.ToJson, Lean.FromJson

structure Recording where
  engine : EngineId := engineId
  program : Program
  deferred : Option DeferredReason := none
  simprocs : Array SimprocObservation := #[]
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
  simprocs : Array SimprocObservation := #[]
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
