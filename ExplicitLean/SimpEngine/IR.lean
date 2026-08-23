module
prelude

public import Lean.Meta.Tactic.Simp.Types

public section

namespace Lean.Meta.Simp.Engine

structure EngineId where
  leanVersion : String
  leanCommit : String
  certificateSchema : Nat
  deriving Inhabited, Repr, BEq

def engineId : EngineId := {
  leanVersion := "4.32.2"
  leanCommit := "f3b06c705e6c85f5314019d5d3baab0fec5b580c"
  certificateSchema := 16
}

inductive Mode where
  | simp
  | dsimp
  deriving Inhabited, Repr, BEq

inductive Phase where
  | pre
  | post
  | dpre
  | dpost
  deriving Inhabited, Repr, BEq

inductive ChildMode where
  | simp
  | dsimp
  | fixed
  deriving Inhabited, Repr, BEq

inductive StepDisposition where
  | done
  | visit
  | continueNone
  | continueSome
  deriving Inhabited, Repr, BEq

inductive ProjectionBranch where
  | requestedClass
  | constructorClass
  | structure
  deriving Inhabited, Repr, BEq

inductive DeltaStrategy where
  | requestedSmart
  | requestedPartial
  | requestedOrdinary
  | autoSmart
  | autoMatch
  | ground
  deriving Inhabited, Repr, BEq

inductive LocalDefReason where
  | zetaDelta
  | requested
  | implementationDetail
  deriving Inhabited, Repr, BEq

inductive ForallBranch where
  | implicationContextual
  | implicationPlain
  | propositionDomainTransport
  | propositionDomainDSimp
  | nonPropositionDSimp
  deriving Inhabited, Repr, BEq

inductive ArithHandler where
  | natRelation
  | natEquality
  | natExpression
  | natDivisibility
  | intRelation
  | intEquality
  | intExpression
  | intDivisibility
  deriving Inhabited, Repr, BEq

inductive PremiseTerminal where
  | localAssumption (contextIndex : Nat)
  | equationHypothesis
  | dischargeRfl
  | isTrue
  deriving Inhabited, Repr, BEq

structure ExprFingerprint where
  printable : String
  fingerprint : String
  deriving Inhabited, Repr, BEq

structure LocalRef where
  contextIndex : Nat
  binderDepth : Nat
  typeFingerprint : String
  valueFingerprint : Option String := none
  deriving Inhabited, Repr, BEq

structure ScopedLocalRef where
  ordinal : Nat
  typeFingerprint : String
  deriving Inhabited, Repr, BEq

inductive RuleOrigin where
  | decl (name : Name)
  | syntax (source : String)
  | local (subject : LocalRef)
  | other (name : Name)
  deriving Inhabited, Repr, BEq

inductive PathStep where
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
  deriving Inhabited, Repr, BEq

structure ExecutionPath where
  steps : Array PathStep := #[]
  deriving Inhabited, Repr, BEq

structure RuleRef where
  source : String
  origin : RuleOrigin
  inverse : Bool
  phase : Phase
  variant : Nat
  ruleFingerprint : String
  lhsFingerprint : String
  indexMode : Bool
  deriving Inhabited, Repr, BEq

structure MatchEnvelope where
  binderAssignments : Array String := #[]
  instanceAssignments : Array String := #[]
  proofPresent : Bool
  deriving Inhabited, Repr, BEq

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
  deriving Inhabited, Repr, BEq

inductive Builtin where
  | decideTrue
  | decideFalse
  | arith (handler : ArithHandler)
  deriving Inhabited, Repr, BEq

inductive CongruenceChoice where
  | user (theoremName : Name) (priority : Nat) (hypothesisPositions : Array Nat)
  | generated (shapeFingerprint : String) (arguments : Array ChildMode)
      (synthesizedAssignments : Array String)
  | generic (arguments : Array ChildMode)
  deriving Inhabited, Repr, BEq

inductive Structural where
  | cacheHit (sourcePath : ExecutionPath)
  | congruence (choice : CongruenceChoice)
  | projectionMajor (structureName : Name) (field : Nat) (mode : ChildMode)
  | matchDiscriminants (count : Nat)
  | lambdaTelescope (count : Nat)
  | forallBranch (choice : ForallBranch)
  | contextualScope (locals : Array ScopedLocalRef)
  | letToHave
  | haveTelescope (fixed used : Array Bool)
  | dropUnusedHave (index : Nat)
  | dsimpCacheHit (sourcePath : ExecutionPath)
  | dsimpTransform (usedLetOnly skipInstances : Bool)
  deriving Inhabited, Repr, BEq

mutual
  structure PremiseProgram where
    propositionFingerprint : String
    program : Program
    terminal : PremiseTerminal
    deriving Repr, BEq

  inductive Operation where
    | rewrite (rule : RuleRef) (matchEnvelope : MatchEnvelope)
        (premises : Array PremiseProgram)
    | reduce (reduction : Reduction)
    | builtin (builtin : Builtin)
    deriving Repr, BEq

  structure Event where
    path : ExecutionPath
    phase : Phase
    operation : Operation
    inputFingerprint : String
    outputFingerprint : String
    stepDisposition : StepDisposition
    deriving Repr, BEq

  structure StructuralWitness where
    path : ExecutionPath
    witness : Structural
    deriving Repr, BEq

  structure Program where
    initialFingerprint : String := ""
    finalFingerprint : String := ""
    structural : Array StructuralWitness := #[]
    events : Array Event := #[]
    deriving Repr, BEq
end

instance : Inhabited Program := ⟨{}⟩

inductive DeferredReason where
  | simproc (name : Name) (phase : Phase)
  | customDischarger
  deriving Inhabited, Repr, BEq

structure SimprocObservation where
  path : ExecutionPath
  name : Name
  phase : Phase
  inputFingerprint : String
  outputFingerprint : String
  stepDisposition : StepDisposition
  definitional : Bool
  deriving Inhabited, Repr, BEq

structure Recording where
  engine : EngineId := engineId
  program : Program
  deferred : Option DeferredReason := none
  simprocs : Array SimprocObservation := #[]
  coveredBranches : Array String := #[]
  deriving Inhabited, Repr, BEq

inductive SubjectRef where
  | target
  | local (subject : LocalRef)
  deriving Inhabited, Repr, BEq

inductive ProofPresence where
  | explicit
  | definitional
  deriving Inhabited, Repr, BEq

inductive SubjectTerminal where
  | targetTrue (proofPresence : ProofPresence)
  | targetTransport (proofPresence : ProofPresence)
  | localFalse (proofPresence : ProofPresence)
  | localDefEqReplace
  | localAssertClear (proofPresence : ProofPresence)
  deriving Inhabited, Repr, BEq

structure SubjectProgram where
  subject : SubjectRef
  initialFingerprint : String
  program : Program
  terminal : SubjectTerminal
  deriving Inhabited, Repr, BEq

structure StateFingerprint where
  targetFingerprint : String
  localContextFingerprint : String
  metavariableContextFingerprint : String
  goalCount : Nat
  deriving Inhabited, Repr, BEq

structure ReplayConfig where
  contextual : Bool
  memoize : Bool
  singlePass : Bool
  dsimp : Bool
  beta : Bool
  proj : Bool
  iota : Bool
  zeta : Bool
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
  etaStruct : Bool
  instances : Bool
  congrConsts : Array Name := #[]
  dsimpProofs : Bool
  reducibleClassField : Bool
  smartUnfolding : Bool
  useBackwardDefEq : Bool
  dsimpUseDefEqAttr : Bool
  skipAssignedInstances : Bool
  metaConfigFingerprint : String
  indexConfigFingerprint : String
  deriving Inhabited, Repr, BEq

structure Certificate where
  engine : EngineId := engineId
  config : ReplayConfig
  subjects : Array SubjectProgram := #[]
  initialState : StateFingerprint
  finalState : StateFingerprint
  deriving Inhabited, Repr, BEq

inductive RecordingFailure where
  | unobservedTransition (site : String)
  | discontinuity (path : ExecutionPath) (expected actual : String)
  | invalidFingerprint (path : ExecutionPath)
  deriving Inhabited, Repr, BEq

inductive ExecutionOutcome where
  | success (changed : Bool)
  | tacticFailure (kind : String)
  deriving Inhabited, Repr, BEq

end Lean.Meta.Simp.Engine
