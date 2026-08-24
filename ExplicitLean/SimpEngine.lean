/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Pinned reference fork for Explicit Lean.
Upstream: Lean 4.32.2, f3b06c705e6c85f5314019d5d3baab0fec5b580c.
-/
module
prelude
public import ExplicitLean.SimpEngine.Runtime
public import Lean.Elab.Tactic.Simp
import Lean.Meta.HaveTelescope
public section
namespace Lean.Meta
namespace Simp.Engine

open Simp

private def etaStructPolicy : EtaStructMode → EtaStructPolicy
  | .all => .all
  | .notClasses => .notClasses
  | .none => .none

def replayConfigOfContext (ctx : Simp.Context) : MetaM ReplayConfig := do
  let cfg := ctx.config
  let base ← Meta.getConfig
  let metaConfig : Meta.Config := { base with
    beta := cfg.beta
    iota := cfg.iota
    zeta := cfg.zeta
    zetaHave := cfg.zetaHave
    zetaUnused := cfg.zetaUnused
    zetaDelta := cfg.zetaDelta
    etaStruct := cfg.etaStruct
    proj := if cfg.proj then .yesWithDelta else .no
    transparency := .reducible
  }
  let indexConfig : Meta.Config := { base with
    beta := cfg.beta
    iota := cfg.iota
    zeta := cfg.zeta
    zetaHave := cfg.zetaHave
    zetaUnused := cfg.zetaUnused
    zetaDelta := cfg.zetaDelta
    etaStruct := cfg.etaStruct
    proj := .no
    transparency := .reducible
  }
  return {
    maxSteps := cfg.maxSteps
    maxDischargeDepth := cfg.maxDischargeDepth
    contextual := cfg.contextual
    memoize := cfg.memoize
    singlePass := cfg.singlePass
    zeta := cfg.zeta
    dsimp := cfg.dsimp
    beta := cfg.beta
    eta := cfg.eta
    etaStruct := etaStructPolicy cfg.etaStruct
    proj := cfg.proj
    iota := cfg.iota
    zetaDelta := cfg.zetaDelta
    zetaHave := cfg.zetaHave
    zetaUnused := cfg.zetaUnused
    autoUnfold := cfg.autoUnfold
    unfoldPartialApp := cfg.unfoldPartialApp
    letToHave := cfg.letToHave
    decide := cfg.decide
    arith := cfg.arith
    ground := cfg.ground
    index := cfg.index
    implicitDefEqProofs := cfg.implicitDefEqProofs
    failIfUnchanged := cfg.failIfUnchanged
    catchRuntime := cfg.catchRuntime
    congrConsts := cfg.congrConsts
    bitVecOfNat := cfg.bitVecOfNat
    warnExponents := cfg.warnExponents
    locals := cfg.locals
    instances := cfg.instances
    dsimpProofs := backward.dsimp.proofs.get (← getOptions)
    reducibleClassField := backward.whnf.reducibleClassField.get (← getOptions)
    smartUnfolding := smartUnfolding.get (← getOptions)
    useBackwardDefEq := backward.defeqAttrib.useBackward.get (← getOptions)
    dsimpUseDefEqAttr := backward.dsimp.useDefEqAttr.get (← getOptions)
    skipAssignedInstances := tactic.skipAssignedInstances.get (← getOptions)
    simprocsEnabled := simprocs.get (← getOptions)
    userConfigFingerprint := optionsFingerprint ctx.userConfig
    metaConfigFingerprint := metaConfigFingerprint metaConfig
    indexConfigFingerprint := metaConfigFingerprint indexConfig
  }

/- Nesting the fork under `Lean.Meta.Simp` preserves upstream unqualified-name
   resolution while giving every copied execution function a distinct name. -/

private opaque MethodsRefPointed : NonemptyType.{0}

def MethodsRef : Type := MethodsRefPointed.type

instance : Nonempty MethodsRef := by exact MethodsRefPointed.property

abbrev EngineM := ReaderT MethodsRef $ ReaderT Runtime SimpM

abbrev Simproc := Expr → EngineM Step

abbrev DSimproc := Expr → EngineM DStep

abbrev Discharge := Expr → EngineM (Option Expr)

structure Methods where
  pre : Simproc := fun _ => return .continue
  post : Simproc := fun e => return .done { expr := e }
  dpre : DSimproc := fun _ => return .continue
  dpost : DSimproc := fun e => return .done e
  discharge? : Discharge := fun _ => return none
  wellBehavedDischarge : Bool := true
  customDischarger : Bool := false
  base : Simp.Methods := {}
  deriving Inhabited

unsafe def Methods.toMethodsRefImpl (methods : Methods) : MethodsRef :=
  unsafeCast methods

@[implemented_by Methods.toMethodsRefImpl]
opaque Methods.toMethodsRef (methods : Methods) : MethodsRef

unsafe def MethodsRef.toMethodsImpl (methods : MethodsRef) : Methods :=
  unsafeCast methods

@[implemented_by MethodsRef.toMethodsImpl]
opaque MethodsRef.toMethods (methods : MethodsRef) : Methods

@[inline] def getMethods : EngineM Methods :=
  return MethodsRef.toMethods (← read)

@[inline] def pre (e : Expr) : EngineM Step := do
  (← getMethods).pre e

@[inline] def post (e : Expr) : EngineM Step := do
  (← getMethods).post e

@[inline] def liftSimpM (x : SimpM α) : EngineM α :=
  fun _ _ => x

@[inline] def mapSimpM (f : SimpM α → SimpM α) (x : EngineM α) : EngineM α :=
  fun methods runtime => f (x methods runtime)

@[inline] def getContext : EngineM Context := liftSimpM Simp.getContext

@[inline] def getConfig : EngineM Config := liftSimpM Simp.getConfig

@[inline] def getSimpTheorems : EngineM SimpTheoremsArray :=
  liftSimpM Simp.getSimpTheorems

@[inline] def getSimpCongrTheorems : EngineM SimpCongrTheorems :=
  liftSimpM Simp.getSimpCongrTheorems

@[inline] def inDSimp : EngineM Bool := liftSimpM Simp.inDSimp

@[inline] def withIncDischargeDepth (x : EngineM α) : EngineM α :=
  mapSimpM Simp.withIncDischargeDepth x

@[inline] def withSimpTheorems (theorems : SimpTheoremsArray)
    (x : EngineM α) : EngineM α :=
  mapSimpM (Simp.withSimpTheorems theorems) x

@[inline] def withSimpIndexConfig (x : EngineM α) : EngineM α :=
  mapSimpM Simp.withSimpIndexConfig x

@[inline] def withSimpMetaConfig (x : EngineM α) : EngineM α :=
  mapSimpM Simp.withSimpMetaConfig x

@[inline] def withParent (parent : Expr) (x : EngineM α) : EngineM α :=
  mapSimpM (Simp.withParent parent) x

@[inline] def withUserConfig (f : Options → Options) (x : EngineM α) : EngineM α :=
  mapSimpM (Simp.withUserConfig f) x

@[inline] def withFreshCache (x : EngineM α) : EngineM α := do
  let runtime : Runtime ← readThe Runtime
  if runtime.mode == .reference then
    mapSimpM Simp.withFreshCache x
  else
    let saved := (← runtime.cacheProvenance.get).simpSources
    runtime.cacheProvenance.modify fun current => { current with simpSources := {} }
    try mapSimpM Simp.withFreshCache x finally
      runtime.cacheProvenance.modify fun current => { current with simpSources := saved }

@[inline] def withPreservedCache (x : EngineM α) : EngineM α := do
  let runtime : Runtime ← readThe Runtime
  if runtime.mode == .reference then
    mapSimpM Simp.withPreservedCache x
  else
    let saved := (← runtime.cacheProvenance.get).simpSources
    runtime.cacheProvenance.modify fun current => {
      current with simpSources := current.simpSources.switch
    }
    try mapSimpM Simp.withPreservedCache x finally
      runtime.cacheProvenance.modify fun current => {
        current with simpSources := {
          current.simpSources with map₂ := saved.map₂, stage₁ := saved.stage₁
        }
      }

@[inline] def withInDSimpWithCache
    (k : ExprStructMap Expr → EngineM (α × ExprStructMap Expr)) : EngineM α :=
  fun methods runtime => Simp.withInDSimpWithCache fun cache => do
    if runtime.mode == .reference then
      k cache methods runtime
    else
      let saved ← runtime.cacheProvenance.get
      runtime.cacheProvenance.modify fun current => {
        current with
        dsimpSources := saved.dsimpStateSources
        dsimpStateSources := {}
      }
      let (result, cache) ← k cache methods runtime
      runtime.cacheProvenance.modify fun current => {
        current with
        dsimpStateSources := current.dsimpSources
        dsimpSources := saved.dsimpSources
      }
      return (result, cache)

@[inline] def recordTriedSimpTheorem (origin : Origin) : EngineM Unit :=
  liftSimpM (Simp.recordTriedSimpTheorem origin)

@[inline] def recordSimpTheorem (origin : Origin) : EngineM Unit :=
  liftSimpM (Simp.recordSimpTheorem origin)

@[inline] def recordCongrTheorem (name : Name) : EngineM Unit :=
  liftSimpM (Simp.recordCongrTheorem name)

@[inline] def getRuntime : EngineM Runtime := readThe Runtime

private def getOperationSourceContext : EngineM Context := do
  let runtime ← getRuntime
  let state ← runtime.state.get
  if runtime.mode == .replay && state.path.steps.contains .ground then
    getContext
  else
    pure <| runtime.ruleContext.getD (← getContext)

@[inline] def getRecorderState : EngineM RecorderState := do
  return ← (← getRuntime).state.get

@[inline] def setRecorderState (state : RecorderState) : EngineM Unit := do
  (← getRuntime).state.set state

@[inline] def modifyRecorderState (f : RecorderState → RecorderState) : EngineM Unit := do
  let runtime ← getRuntime
  if runtime.mode != .reference then
    runtime.state.modify f

@[inline] def recordBranch (branch : String) : EngineM Unit := do
  let runtime ← getRuntime
  if runtime.mode == .record then
    runtime.observations.modify fun observations =>
      { observations with coveredBranches := observations.coveredBranches.push branch }

@[inline] def withPath (step : PathStep) (x : EngineM α) : EngineM α := do
  let runtime ← getRuntime
  if runtime.mode == .reference then
    x
  else
    let previous ← runtime.state.get
    runtime.state.set { previous with path.steps := previous.path.steps.push step }
    try x finally
      runtime.state.modify fun current => { current with path := previous.path }

@[inline] def withPhase (phase : Phase) (x : EngineM α) : EngineM α := do
  let runtime ← getRuntime
  if runtime.mode == .reference then
    x
  else
    let previous ← runtime.state.get
    runtime.state.set {
      previous with
      phase
      currentPhaseInvocationOrdinal := previous.phaseInvocationOrdinal
      phaseInvocationOrdinal := previous.phaseInvocationOrdinal + 1
    }
    try x finally
      runtime.state.modify fun current => {
        current with
        phase := previous.phase
        currentPhaseInvocationOrdinal := previous.currentPhaseInvocationOrdinal
      }

def emitStructural (witness : Structural) : EngineM Unit := do
  let runtime ← getRuntime
  let state ← runtime.state.get
  let item : StructuralWitness := { path := state.path, witness }
  if runtime.mode == .record then
    runtime.state.set {
      state with program.structural := state.program.structural.push item
    }
  else if runtime.mode == .replay then
    let some expected := state.program.structural[state.structuralCursor]?
      | throwError "replay_program_exhausted: unexpected structural witness {repr item}"
    unless expected == item do
      throwError "replay_structural_mismatch at {state.structuralCursor}: expected {repr expected}, got {repr item}"
    runtime.state.set { state with structuralCursor := state.structuralCursor + 1 }

def emitEvent (input output : Expr) (operation : Operation)
    (stepDisposition : StepDisposition) : EngineM Unit := do
  let runtime ← getRuntime
  if runtime.mode != .reference then
    let state ← runtime.state.get
    let inputFingerprint ← liftM (exprFingerprintHash input)
    let outputFingerprint ← liftM (exprFingerprintHash output)
    let event : Event := {
      path := state.path
      phase := state.phase
      invocationOrdinal := state.currentPhaseInvocationOrdinal
      operation
      inputFingerprint
      outputFingerprint
      stepDisposition
    }
    if runtime.mode == .record then
      runtime.state.set { state with program.events := state.program.events.push event }
    else
      let some expected := state.program.events[state.eventCursor]?
        | throwError "replay_program_exhausted: unexpected event {repr event}"
      unless expected == event do
        throwError "replay_event_mismatch at {state.eventCursor}: expected {repr expected}, got {repr event}"
      runtime.state.set { state with eventCursor := state.eventCursor + 1 }

private def phaseBranch (phase : Phase) (disposition : StepDisposition) : String :=
  let phase := match phase with
    | .pre => "pre"
    | .post => "post"
    | .dpre => "dpre"
    | .dpost => "dpost"
  let disposition := match disposition with
    | .done => "done"
    | .visit => "visit"
    | .continueNone => "continueNone"
    | .continueSome => "continueSome"
  s!"control.phase.{phase}.{disposition}"

private def recordPhaseStep (input : Expr) (x : EngineM Step) : EngineM Step := do
  let result ← x
  if (← getRuntime).mode == .record then
    let (disposition, output, proofPresent) := match result with
      | .done result => (.done, result.expr, result.proof?.isSome)
      | .visit result => (.visit, result.expr, result.proof?.isSome)
      | .continue none => (.continueNone, input, false)
      | .continue (some result) => (.continueSome, result.expr, result.proof?.isSome)
    let state ← getRecorderState
    let outputFingerprint ← liftM (exprFingerprintHash output)
    emitStructural (.phaseOutcome state.phase state.currentPhaseInvocationOrdinal
      disposition outputFingerprint proofPresent)
    recordBranch (phaseBranch state.phase disposition)
  return result

private def recordDPhaseStep (input : Expr) (x : EngineM DStep) : EngineM DStep := do
  let result ← x
  if (← getRuntime).mode == .record then
    let (disposition, output) := match result with
      | .done output => (.done, output)
      | .visit output => (.visit, output)
      | .continue none => (.continueNone, input)
      | .continue (some output) => (.continueSome, output)
    let state ← getRecorderState
    let outputFingerprint ← liftM (exprFingerprintHash output)
    emitStructural (.phaseOutcome state.phase state.currentPhaseInvocationOrdinal
      disposition outputFingerprint false)
    recordBranch (phaseBranch state.phase disposition)
  return result

@[inline] def peekReplayEvent? : EngineM (Option Event) := do
  let runtime ← getRuntime
  if runtime.mode != .replay then return none
  let state ← runtime.state.get
  return state.program.events[state.eventCursor]?

@[inline] def peekReplayStructural? : EngineM (Option StructuralWitness) := do
  let runtime ← getRuntime
  if runtime.mode != .replay then return none
  let state ← runtime.state.get
  return state.program.structural[state.structuralCursor]?

def findReplayCongruenceChoice? (invocationOrdinal : Nat) : EngineM (Option CongruenceChoice) := do
  let runtime ← getRuntime
  unless runtime.mode == .replay do return none
  let state ← runtime.state.get
  for h : index in state.structuralCursor...state.program.structural.size do
    let item := state.program.structural[index]
    if item.path == state.path then
      if let .congruence ordinal choice := item.witness then
        if ordinal == invocationOrdinal then return some choice
  return none

private def nextCongruenceInvocationOrdinal : EngineM Nat := do
  let runtime ← getRuntime
  if runtime.mode == .reference then return 0
  let state ← runtime.state.get
  runtime.state.set {
    state with congruenceInvocationOrdinal := state.congruenceInvocationOrdinal + 1 }
  return state.congruenceInvocationOrdinal

private def nextPathInvocationOrdinal : EngineM Nat := do
  let runtime ← getRuntime
  if runtime.mode == .reference then return 0
  let state ← runtime.state.get
  runtime.state.set {
    state with pathInvocationOrdinal := state.pathInvocationOrdinal + 1 }
  return state.pathInvocationOrdinal

@[inline] def isCurrentReplayEvent (event : Event) : EngineM Bool := do
  let state ← getRecorderState
  return event.path == state.path && event.phase == state.phase &&
    event.invocationOrdinal == state.currentPhaseInvocationOrdinal

@[inline] def isCurrentReplayStructural (item : StructuralWitness) : EngineM Bool := do
  return item.path == (← getRecorderState).path

private def assertReplayProgramConsumed (state : RecorderState) : MetaM Unit := do
  unless state.eventCursor == state.program.events.size do
    throwError "replay_unconsumed_events: {state.eventCursor}/{state.program.events.size}"
  unless state.structuralCursor == state.program.structural.size do
    throwError "replay_unconsumed_structural: {state.structuralCursor}/{state.program.structural.size}"

@[inline] def commitReduction (branch : String) (input output : Expr)
    (reduction : Reduction) (stepDisposition : StepDisposition := .continueSome) : EngineM Unit := do
  if input != output then
    recordBranch branch
    emitEvent input output (.reduce reduction) stepDisposition

private def mergeDeferredReason (current : Option DeferredReason)
    (next : DeferredReason) : Option DeferredReason :=
  match current, next with
  | none, next => some next
  | some (.simproc name phase), .customDischarger
  | some .customDischarger, .simproc name phase =>
      some (.simprocAndCustomDischarger name phase)
  | some current, _ => some current

private def deferredBySimproc : Option DeferredReason → Bool
  | some (.simproc ..) | some (.simprocAndCustomDischarger ..) => true
  | _ => false

def deferRecording (reason : DeferredReason) : EngineM Unit := do
  let runtime ← getRuntime
  if runtime.mode == .record then
    runtime.observations.modify fun observations =>
      { observations with deferred := mergeDeferredReason observations.deferred reason }

def observeSimproc (name : Name) (input output : Expr)
    (stepDisposition : StepDisposition) (definitional : Bool) : EngineM Unit := do
  let runtime ← getRuntime
  if runtime.mode == .record then
    let state ← runtime.state.get
    let observation : SimprocObservation := {
      path := state.path
      name
      phase := state.phase
      inputFingerprint := ← liftM (runtime.cachedFingerprintHash input)
      outputFingerprint := ← liftM (runtime.cachedFingerprintHash output)
      stepDisposition
      definitional
    }
    runtime.observations.modify fun observations => {
      observations with
      deferred := mergeDeferredReason observations.deferred (.simproc name state.phase)
      simprocs := observations.simprocs.push observation
      coveredBranches :=
        let branch := if definitional then "simproc.dsimp" else "simproc.simp"
        let branches := observations.coveredBranches.push branch
        if stepDisposition == .continueNone then
          branches.push s!"{branch}.continueNone"
        else
          branches
    }

@[inline] def setPremiseTerminal (terminal : PremiseTerminal) : EngineM Unit :=
  modifyRecorderState fun state => { state with lastPremiseTerminal := some terminal }

@[inline] def saveRecorderState : EngineM RecorderState := do
  let state ← getRecorderState
  let provenance ← (← getRuntime).cacheProvenance.get
  return {
    state with
    savedSimpCacheProducerCount := provenance.simpOrder.size
    savedDSimpCacheProducerCount := provenance.dsimpOrder.size
  }

@[inline] def restoreRecorderState (state : RecorderState) : EngineM Unit :=
  setRecorderState state

@[inline] def withDischarger (discharge? : Discharge)
    (wellBehavedDischarge : Bool) (x : EngineM α) : EngineM α :=
  withFreshCache <|
    withReader (fun ref =>
      { MethodsRef.toMethods ref with discharge?, wellBehavedDischarge }.toMethodsRef) x

@[always_inline] def andThen (f g : Simproc) : Simproc := fun e => do
  match ← f e with
  | .done result => return .done result
  | .continue none => g e
  | .continue (some result) => mkEqTransResultStep result (← g result.expr)
  | .visit result => return .visit result

instance : AndThen Simproc where
  andThen first second := andThen first (second ())

@[always_inline] def dandThen (f g : DSimproc) : DSimproc := fun e => do
  match ← f e with
  | .done result => return .done result
  | .continue none => g e
  | .continue (some result) => g result
  | .visit result => return .visit result

instance : AndThen DSimproc where
  andThen first second := dandThen first (second ())

def EngineM.runWithRuntime (runtime : Runtime) (ctx : Context) (state : State := {})
    (methods : Methods := {}) (x : EngineM α) : MetaM (α × State) := do
  SimpM.run ctx state methods.base (x methods.toMethodsRef runtime)

def EngineM.run (ctx : Context) (state : State := {}) (methods : Methods := {})
    (x : EngineM α) : MetaM (α × State) := do
  let runtime ← Runtime.reference
  EngineM.runWithRuntime runtime ctx state methods x

set_option compiler.ignoreBorrowAnnotation true in
@[extern "explicit_lean_simp_engine"]
opaque simp (e : Expr) : EngineM Result

set_option compiler.ignoreBorrowAnnotation true in
@[extern "explicit_lean_dsimp_engine"]
opaque dsimp (e : Expr) : EngineM Expr

/-- Return true if `e` is of the form `ofNat n` where `n` is a kernel Nat literal -/
def isOfNatNatLit (e : Expr) : Bool :=
  e.isAppOf ``OfNat.ofNat && e.getAppNumArgs >= 3 && (e.getArg! 1).isRawNatLit

/--
If `e` is a raw Nat literal and `OfNat.ofNat` is not in the list of declarations to unfold,
return an `OfNat.ofNat`-application.
-/
def foldRawNatLit (e : Expr) : EngineM Expr := do
  match e.rawNatLit? with
  | some n =>
    /- If `OfNat.ofNat` is marked to be unfolded, we do not pack orphan nat literals as `OfNat.ofNat` applications
        to avoid non-termination. See issue #788.  -/
    if (← readThe Simp.Context).isDeclToUnfold ``OfNat.ofNat then
      return e
    else
      let eNew := toExpr n
      commitReduction "reduce.foldRawNatLit" e eNew .foldRawNatLit
      return eNew
  | none   => return e

/-- Return true if `e` is of the form `ofScientific n b m` where `n` and `m` are kernel Nat literals. -/
def isOfScientificLit (e : Expr) : Bool :=
  e.isAppOfArity ``OfScientific.ofScientific 5 && (e.getArg! 4).isRawNatLit && (e.getArg! 2).isRawNatLit

/-- Return true if `e` is of the form `Char.ofNat n` where `n` is a kernel Nat literals. -/
def isCharLit (e : Expr) : Bool :=
  e.isAppOfArity ``Char.ofNat 1 && e.appArg!.isRawNatLit

/--
Unfold definition even if it is not marked as `@[reducible]`.
Remark: We never unfold irreducible definitions. Mathlib relies on that in the implementation of the
command `irreducible_def`.
-/
private def unfoldDefinitionAny? (e : Expr) : MetaM (Option Expr) := do
  if let .const declName _ := e.getAppFn then
    if (← isIrreducible declName) then
      return none
  unfoldDefinition? e (ignoreTransparency := true)

private def reduceProjFn? (e : Expr) : EngineM (Option (Expr × Reduction)) := do
  matchConst e.getAppFn (fun _ => pure none) fun cinfo _ => do
    match (← getProjectionFnInfo? cinfo.name) with
    | none => return none
    | some projInfo =>
      /- Helper function for applying `reduceProj?` to the result of `unfoldDefinition?` -/
      let reduceProjCont? (branch : ProjectionBranch)
          (e? : Option Expr) : EngineM (Option (Expr × Reduction)) := do
        match e? with
        | none   => pure none
        | some eNew =>
          match (← withSimpMetaConfig <| reduceProj? eNew.getAppFn) with
          | some f => return some (mkAppN f eNew.getAppArgs,
              .projectionFunction cinfo.name branch)
          | none   => return none
      if projInfo.fromClass then
        -- `class` projection
        if (← getContext).isDeclToUnfold cinfo.name then
          /-
          If user requested `class` projection to be unfolded (e.g., `simp [X.x]`), we set transparency
          mode to `.instances` and invoke `unfoldDefinition?`.
          Recall that `unfoldDefinition?` has support for unfolding this kind of projection when
          transparency mode is `.instances`.

          Note: this unfolds the projection function but may leave a `.proj` node that cannot be further
          reduced. For example, given:
          ```
          def a' := 0; def b' := 0
          class X where x : Nat
          instance instX (n : Nat) : X where x := n
          ```
          `simp [X.x]` on `(instX a').x = (instX b').x` unfolds `X.x` to expose `.proj X 0 (instX a')`,
          but cannot reduce further because `instX a'` is not a constructor application at `.reducible`.
          The resulting goal `(instX a').1 = (instX b').1` is expected and reasonable: the user explicitly
          requested the unfolding, and the projection is stuck because `a'` and `b'` are semireducible.
          -/
          let e? ← withReducibleAndInstances <| unfoldDefinition? e
          if e?.isSome then
            recordSimpTheorem (.decl cinfo.name)
          return e?.map fun eNew =>
            (eNew, .projectionFunction cinfo.name .requestedClass)
        else
          /-
          Recall that class projections are **not** marked with `[reducible]` because we want them to be
          in "reducible canonical form". However, if we have a class projection of the form `Class.projFn (Class.mk ...)`,
          we want to reduce it. See issue #1869 for an example where this is important.
          -/
          unless e.getAppNumArgs > projInfo.numParams do
            return none
          let major := e.getArg! projInfo.numParams
          unless (← isConstructorApp major) do
            return none
          if backward.whnf.reducibleClassField.get (← getOptions) then
            /-
            When `backward.whnf.reducibleClassField` is `true`, `unfoldDefault` (in WHNF.lean)
            already reduces the `.proj` node during `unfoldDefinitionAny?`, so `reduceProjCont?`
            would discard the fully-reduced result because it expects a `.proj` head.
            We return the unfolded result directly; the dsimp traversal will revisit it
            (via `.visit`) and handle any remaining `.proj` nodes naturally.
            -/
            return (← unfoldDefinitionAny? e).map fun eNew =>
              (eNew, .projectionFunction cinfo.name .constructorClass)
          else
            reduceProjCont? .constructorClass (← unfoldDefinitionAny? e)
      else
        -- `structure` projections
        reduceProjCont? .structure (← unfoldDefinition? e)

private def localRefOfDecl (localDecl : LocalDecl) : EngineM LocalRef := do
  let typeFingerprint ← liftM (exprFingerprintHash localDecl.type)
  let valueFingerprint ← localDecl.value?.mapM fun value => liftM (exprFingerprintHash value)
  return {
    contextIndex := localDecl.index
    binderDepth := (← getLCtx).numIndices
    typeFingerprint
    valueFingerprint
  }

/--
  Return true if `declName` is the name of a definition of the form
  ```
  def declName ... :=
    match ... with
    | ...
  ```
-/
private partial def isMatchDef (declName : Name) : CoreM Bool := do
  let .defnInfo info ← getConstInfo declName | return false
  return go (← getEnv) info.value
where
  go (env : Environment) (e : Expr) : Bool :=
    if e.isLambda then
      go env e.bindingBody!
    else
      let f := e.getAppFn
      f.isConst && isMatcherCore env f.constName!

/--
Try to unfold `e`.
-/
private def unfold? (e : Expr) : EngineM (Option (Expr × DeltaStrategy)) := do
  let f := e.getAppFn
  if !f.isConst then
    return none
  let fName := f.constName!
  let ctx ← getContext
  let rec unfoldDeclToUnfold? : EngineM (Option (Expr × DeltaStrategy)) := do
    let options ← getOptions
    let cfg ← getConfig
    -- Support for issue #2042
    if smartUnfolding.get options && (← getEnv).contains (mkSmartUnfoldingNameFor fName) then
      return (← unfoldDefinitionAny? e).map fun eNew =>
        (eNew, DeltaStrategy.requestedSmart)
    else if cfg.unfoldPartialApp then
      return (← unfoldDefinitionAny? e).map fun eNew =>
        (eNew, DeltaStrategy.requestedPartial)
    else
      -- We are not unfolding partial applications, and `fName` does not have smart unfolding support.
      -- Thus, we must check whether the arity of the function >= number of arguments.
      let some cinfo := (← getEnv).find? fName | return none
      let some value := cinfo.value? | return none
      let arity := value.getNumHeadLambdas
      -- Partially applied function, return `none`. See issue #2042
      if arity > e.getAppNumArgs then return none
      return (← unfoldDefinitionAny? e).map fun eNew =>
        (eNew, DeltaStrategy.requestedOrdinary)
  if (← isProjectionFn fName) then
    return none -- should be reduced by `reduceProjFn?`
  else if ctx.config.autoUnfold then
    if ctx.simpTheorems.isErased (.decl fName) then
      return none
    else if hasSmartUnfoldingDecl (← getEnv) fName then
      return (← unfoldDefinitionAny? e).map (·, .autoSmart)
    else if (← isMatchDef fName) then
      let some value ← unfoldDefinitionAny? e | return none
      let .reduced value ← withSimpMetaConfig <| reduceMatcher? value | return none
      return some (value, .autoMatch)
    else
      return none
  else if ctx.isDeclToUnfold fName then
    unfoldDeclToUnfold?
  else
    return none

private def exactProjectionFunction (e : Expr) (name : Name)
    (branch : ProjectionBranch) : EngineM (Option Expr) := do
  unless e.getAppFn.isConstOf name do return none
  let sourceContext ← getOperationSourceContext
  match branch with
  | .requestedClass =>
      let some projection ← getProjectionFnInfo? name | return none
      unless projection.fromClass && sourceContext.isDeclToUnfold name do return none
      withReducibleAndInstances <| unfoldDefinition? e
  | .constructorClass | .structure =>
      if branch == .constructorClass && sourceContext.isDeclToUnfold name then
        return none
      match ← reduceProjFn? e with
      | some (output, .projectionFunction actualName actualBranch) =>
          if actualName == name && actualBranch == branch then return some output
          return none
      | _ => return none

private def exactDelta (e : Expr) (name : Name) (strategy : DeltaStrategy) : EngineM (Option Expr) := do
  unless e.getAppFn.isConstOf name do return none
  let sourceContext ← getOperationSourceContext
  let cfg ← getConfig
  let smart := smartUnfolding.get (← getOptions)
  if !(strategy matches .ground) && (← isProjectionFn name) then return none
  match strategy with
  | .requestedSmart =>
      unless !sourceContext.config.autoUnfold && sourceContext.isDeclToUnfold name &&
          smart && (← getEnv).contains (mkSmartUnfoldingNameFor name) do
        return none
      unfoldDefinitionAny? e
  | .requestedPartial =>
      unless !sourceContext.config.autoUnfold && sourceContext.isDeclToUnfold name &&
          !(smart && (← getEnv).contains (mkSmartUnfoldingNameFor name)) &&
          cfg.unfoldPartialApp do
        return none
      unfoldDefinitionAny? e
  | .requestedOrdinary =>
      unless !sourceContext.config.autoUnfold && sourceContext.isDeclToUnfold name &&
          !(smart && (← getEnv).contains (mkSmartUnfoldingNameFor name)) &&
          !cfg.unfoldPartialApp do
        return none
      let some cinfo := (← getEnv).find? name | return none
      let some value := cinfo.value? | return none
      if value.getNumHeadLambdas > e.getAppNumArgs then return none
      unfoldDefinitionAny? e
  | .autoSmart =>
      unless sourceContext.config.autoUnfold &&
          !sourceContext.simpTheorems.isErased (.decl name) &&
          hasSmartUnfoldingDecl (← getEnv) name do
        return none
      unfoldDefinitionAny? e
  | .autoMatch =>
      unless sourceContext.config.autoUnfold &&
          !sourceContext.simpTheorems.isErased (.decl name) &&
          !hasSmartUnfoldingDecl (← getEnv) name && (← isMatchDef name) do
        return none
      let some unfolded ← unfoldDefinitionAny? e | return none
      match ← withSimpMetaConfig <| reduceMatcher? unfolded with
      | .reduced output => return some output
      | _ => return none
  | .ground =>
      unless cfg.ground do return none
      unless !e.hasExprMVar && !e.hasFVar do return none
      let .const declName levels := e.getAppFn | return none
      if sourceContext.simpTheorems.isErased (.decl declName) then return none
      if (← isMatcher declName) then return none
      if (← getEqnsFor? declName).isSome then return none
      if e.isConst then
        if let .forallE .. ← whnfD (← inferType e) then return none
      let info ← getConstInfo declName
      unless info.hasValue && info.levelParams.length == levels.length do return none
      let body ← instantiateValueLevelParams info levels
      return some (body.betaRev e.getAppRevArgs (useZeta := true))

private def exactLocalDef (e : Expr) (expected : LocalRef)
    (expectedReason : LocalDefReason) : EngineM (Option Expr) := do
  unless e.isFVar do return none
  let localDecl ← getFVarLocalDecl e
  let actual ← localRefOfDecl localDecl
  unless actual == expected do return none
  let cfg ← getConfig
  let sourceContext ← getOperationSourceContext
  let sourceTheorems := sourceContext.simpTheorems
  let actualReason? :=
    if cfg.zetaDelta then some LocalDefReason.zetaDelta
    else if sourceTheorems.isLetDeclToUnfold localDecl.fvarId then some .requested
    else if localDecl.isImplementationDetail then some .implementationDetail
    else none
  unless actualReason? == some expectedReason do return none
  return localDecl.value?

private def executeRecordedReduction (e : Expr) (reduction : Reduction) : EngineM (Option Expr) := do
  let cfg ← getConfig
  match reduction with
  | .instantiateMVars =>
      unless e.getAppFn.isMVar do return none
      return some (← instantiateMVars e)
  | .beta =>
      unless cfg.beta do return none
      let fn := e.getAppFn
      unless fn.isHeadBetaTargetFn false do return none
      return some (fn.betaRev e.getAppRevArgs)
  | .projection structureName field =>
      unless cfg.proj do return none
      match e with
      | .proj actualStructure actualField _ =>
          unless actualStructure == structureName && actualField == field do return none
      | _ => return none
      withSimpMetaConfig <| reduceProj? e
  | .projectionFunction name branch =>
      unless cfg.proj do return none
      exactProjectionFunction e name branch
  | .iota =>
      unless cfg.iota do return none
      withSimpMetaConfig <| reduceRecMatcher? e
  | .zetaUsed zetaHave =>
      unless cfg.zeta && zetaHave == cfg.zetaHave do return none
      let .letE _ _ value body nondep := e | return none
      unless !nondep || zetaHave do return none
      return some (expandLet body #[value] (zetaHave := zetaHave))
  | .zetaUnused =>
      unless cfg.zetaUnused do return none
      let .letE _ _ _ body nondep := e | return none
      if cfg.zeta && (!nondep || cfg.zetaHave) then return none
      unless !body.hasLooseBVars do return none
      return some (consumeUnusedLet body)
  | .delta name strategy => exactDelta e name strategy
  | .foldRawNatLit =>
      let sourceContext ← getOperationSourceContext
      if sourceContext.isDeclToUnfold ``OfNat.ofNat then return none
      let some value := e.rawNatLit? | return none
      return some (toExpr value)
  | .localDef subject reason => exactLocalDef e subject reason

private def validateReductionDisposition (reduction : Reduction)
    (disposition : StepDisposition) : EngineM Unit := do
  let valid : Bool := match reduction with
    | .iota => disposition == .continueSome || disposition == .visit
    | .delta _ .ground => disposition == .visit
    | _ => disposition == .continueSome
  unless valid do
    throwError "replay_reduction_disposition_mismatch: {repr reduction}, {repr disposition}"

private def replayReductionStep? (e : Expr) : EngineM (Option Expr) := do
  let runtime ← getRuntime
  unless runtime.mode == .replay do return none
  let some expected ← peekReplayEvent? | return none
  unless ← isCurrentReplayEvent expected do return none
  let .reduce reduction := expected.operation | return none
  validateReductionDisposition reduction expected.stepDisposition
  let actualInput ← liftM (exprFingerprintHash e)
  unless actualInput == expected.inputFingerprint do
    throwError "replay_event_input_mismatch: expected {expected.inputFingerprint}, got {actualInput}"
  let some output ← executeRecordedReduction e reduction
    | throwError "replay_reduction_failed: {repr reduction}"
  if output == e then
    throwError "replay_reduction_unchanged: {repr reduction}"
  emitEvent e output (.reduce reduction) expected.stepDisposition
  return some output

private def reduceFVar (cfg : Config) (thms : SimpTheoremsArray) (e : Expr) : EngineM Expr := do
  if let some output ← replayReductionStep? e then
    return output
  if (← getRuntime).mode == .replay then
    return e
  let localDecl ← getFVarLocalDecl e
  if cfg.zetaDelta || thms.isLetDeclToUnfold e.fvarId! || localDecl.isImplementationDetail then
    if !cfg.zetaDelta && thms.isLetDeclToUnfold e.fvarId! then
      recordSimpTheorem (.fvar localDecl.fvarId)
    let some v := localDecl.value? | return e
    let reason :=
      if cfg.zetaDelta then LocalDefReason.zetaDelta
      else if thms.isLetDeclToUnfold e.fvarId! then .requested
      else .implementationDetail
    commitReduction "reduce.localDef" e v (.localDef (← localRefOfDecl localDecl) reason)
    return v
  else
    return e

private def reduceStep (e : Expr) : EngineM Expr := do
  if let some output ← replayReductionStep? e then
    return output
  if (← getRuntime).mode == .replay then
    return e
  let cfg ← getConfig
  let f := e.getAppFn
  if f.isMVar then
    let eNew ← instantiateMVars e
    commitReduction "reduce.instantiateMVars" e eNew .instantiateMVars
    return eNew
  withSimpMetaConfig do
  if cfg.beta then
    if f.isHeadBetaTargetFn false then
      let eNew := f.betaRev e.getAppRevArgs
      commitReduction "reduce.beta" e eNew .beta
      return eNew
  -- TODO: eta reduction
  if cfg.proj then
    match (← reduceProj? e) with
    | some eNew =>
      let reduction := match e with
        | .proj structureName field _ => Reduction.projection structureName field
        | _ => unreachable!
      commitReduction "reduce.projection" e eNew reduction
      return eNew
    | none =>
    match (← reduceProjFn? e) with
    | some (eNew, reduction) =>
      commitReduction "reduce.projectionFunction" e eNew reduction
      return eNew
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some eNew =>
      commitReduction "reduce.iota" e eNew .iota
      return eNew
    | none   => pure ()
  if let .letE _ _ v b nondep := e then
    if cfg.zeta && (!nondep || cfg.zetaHave) then
      let eNew := expandLet b #[v] (zetaHave := cfg.zetaHave)
      commitReduction "reduce.zetaUsed" e eNew (.zetaUsed cfg.zetaHave)
      return eNew
    else if cfg.zetaUnused && !b.hasLooseBVars then
      let eNew := consumeUnusedLet b
      commitReduction "reduce.zetaUnused" e eNew .zetaUnused
      return eNew
  match (← unfold? e) with
  | some (e', strategy) =>
    trace[Meta.Tactic.simp.rewrite] "unfold {.ofConst e.getAppFn}, {e} ==> {e'}"
    recordSimpTheorem (.decl e.getAppFn.constName!)
    commitReduction "reduce.delta" e e' (.delta e.getAppFn.constName! strategy)
    return e'
  | none => foldRawNatLit e

private partial def reduce (e : Expr) : EngineM Expr := withIncRecDepth do
  let e' ← reduceStep e
  if e' == e then
    return e'
  else
    trace[Debug.Meta.Tactic.simp] "reduce {e} => {e'}"
    reduce e'

local instance : Inhabited (EngineM α) where
  default := fun _ _ _ _ _ => default

partial def lambdaTelescopeDSimp (e : Expr) (k : Array Expr → Expr → EngineM α) : EngineM α := do
  go #[] e
where
  go (xs : Array Expr) (e : Expr) : EngineM α := do
    match e with
    | .lam n d b c =>
      let d ← withPath (.lambdaDomain xs.size) <| dsimp d
      withLocalDecl n c d fun x => go (xs.push x) (b.instantiate1 x)
    | e =>
      emitStructural (.lambdaTelescope xs.size)
      recordBranch "struct.lambdaTelescope"
      withPath .lambdaBody <| k xs e

private def scopedLocalRef (ordinal : Nat) (expression : Expr) : EngineM ScopedLocalRef := do
  return {
    ordinal
    typeFingerprint := ← liftM (exprFingerprintHash (← inferType expression))
  }

/--
We use `withNewLemmas` whenever updating the local context.
-/
def withNewLemmas {α} (xs : Array Expr) (f : EngineM α) : EngineM α := do
  if (← getConfig).contextual then
    withFreshCache do
      let mut s ← getSimpTheorems
      let mut updated := false
      let ctx ← getContext
      for x in xs do
        if (← isProof x) then
          s ← s.addTheorem (.fvar x.fvarId!) x (config := ctx.indexConfig)
          updated := true
      if updated then
        let locals ← xs.mapIdxM fun index x => scopedLocalRef index x
        emitStructural (.contextualScope locals)
        recordBranch "struct.contextualScope"
        withSimpTheorems s f
      else
        f
  else if (← getMethods).wellBehavedDischarge then
    -- See comment at `Methods.wellBehavedDischarge` to understand why
    -- we don't have to reset the cache
    f
  else
    withFreshCache do f

local instance : MonadSimp EngineM where
  simp e := do
    let state ← getRecorderState
    let path? := state.pendingMonadSimpPaths[0]?
    modifyRecorderState fun current => { current with pendingMonadSimpPaths := #[] }
    let r ← match path? with
      | some path => withPath path <| simp e
      | none => simp e
    modifyRecorderState fun current => {
      current with pendingMonadSimpPaths := state.pendingMonadSimpPaths.drop 1
    }
    if r.expr == e then
      return .rfl
    else
      return .step r.expr (← r.getProof)
  dsimp e := do
    let state ← getRecorderState
    let path? := state.pendingMonadSimpPaths[0]?
    modifyRecorderState fun current => { current with pendingMonadSimpPaths := #[] }
    let result ← match path? with
      | some path => withPath path <| dsimp e
      | none => dsimp e
    modifyRecorderState fun current => {
      current with pendingMonadSimpPaths := state.pendingMonadSimpPaths.drop 1
    }
    return result
  withNewLemmas := withNewLemmas

/--
Given a simplified function result `r` and arguments `args`, simplify arguments using `simp` and `dsimp`.
The resulting proof is built using `congr` and `congrFun` theorems.
-/
def congrArgs (r : Result) (args : Array Expr) : EngineM Result := do
  if args.isEmpty then
    return r
  else
    let cfg ← getConfig
    let infos := (← getFunInfoNArgs r.expr args.size).paramInfo
    let mut r := r
    let mut i := 0
    for arg in args do
      if h : i < infos.size then
        trace[Debug.Meta.Tactic.simp] "app [{i}] {infos.size} {arg} hasFwdDeps: {infos[i].hasFwdDeps}"
        let info := infos[i]
        if info.isInstance && (!cfg.instances || cfg.ground) then
          /-
          **Note**: We don't visit instance implicit arguments when we are reducing ground terms.
          Motivation: many instance implicit arguments are ground, and it does not make sense
          to reduce them if the parent term is not ground.
          -/
          r ← mkCongrFun r arg
        else if !info.hasFwdDeps then
          r ← mkCongr r (← withPath (.autoCongrArgument i .simp) <| simp arg)
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← mkCongr r (← withPath (.autoCongrArgument i .simp) <| simp arg)
        else
          r ← mkCongrFun r (← withPath (.autoCongrArgument i .dsimp) <| dsimp arg)
      else if (← whnfD (← inferType r.expr)).isArrow then
        r ← mkCongr r (← withPath (.autoCongrArgument i .simp) <| simp arg)
      else
        r ← mkCongrFun r (← withPath (.autoCongrArgument i .dsimp) <| dsimp arg)
      i := i + 1
    return r

/-- Helper function for `simpAppUsingCongr` -/
private def mkCongrFun' (e : Expr) (r : Result) (a : Expr) : MetaM Result := do
  let e' := e.updateApp! r.expr a
  match r.proof? with
  | none   => return { expr := e', proof? := none }
  | some hf =>
    let α ← inferType a
    let u ← getLevel α
    let v ← getLevel (← inferType e)
    let f := e.appFn!
    let .forallE x _ βx _ ← whnfD (← inferType f)
      | throwError "failed to build congruence proof, function expected{indentExpr f}"
    let β := Lean.mkLambda x .default α βx
    return { expr := e', proof? := mkApp6 (mkConst ``congrFun [u, v]) α β f r.expr hf a }

/-- Helper function for `simpAppUsingCongr` -/
private def mkCongrPrefix (declName : Name) (e : Expr) : MetaM Expr := do
  let α ← inferType e.appArg!
  let u ← getLevel α
  let β ← inferType e
  let v ← getLevel β
  return mkApp2 (mkConst declName [u, v]) α β

/-- Helper function for `simpAppUsingCongr` -/
private def mkCongrArg' (e : Expr) (f : Expr) (r : Result) : MetaM Result := do
  let e' := e.updateApp! f r.expr
  match r.proof? with
  | none   => return { expr := e', proof? := none }
  | some ha =>
    let h ← mkCongrPrefix ``congrArg e
    return { expr := e', proof? := mkApp4 h e.appArg! r.expr f ha }

/-- Helper function for `simpAppUsingCongr` -/
private def mkCongr' (e : Expr) (r₁ r₂ : Result) : MetaM Result := do
  let e' := e.updateApp! r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,    none    => return { expr := e', proof? := none }
  | some hf,  none    =>
    let h ← mkCongrPrefix ``congrFun' e
    return { expr := e', proof? := mkApp4 h e.appFn! r₁.expr hf r₂.expr }
  | none,    some ha  =>
    let h ← mkCongrPrefix ``congrArg e
    return { expr := e', proof? := mkApp4 h e.appArg! r₂.expr r₁.expr ha }
  | some hf, some ha =>
    let h ← mkCongrPrefix ``_root_.congr e
    return { expr := e', proof? := mkApp6 h e.appFn! r₁.expr e.appArg! r₂.expr hf ha }

/--
Given an application `e`, recursively simplifies its function and arguments and constructs a proof
using `congrArg`, `congrFun`, `congrFun'` and `congr`.
-/
def simpAppUsingCongr (e : Expr) (invocationOrdinal : Nat) : EngineM Result := do
  let f := e.getAppFn
  let numArgs := e.getAppNumArgs
  let cfg ← getConfig
  let infos := (← getFunInfoNArgs f numArgs).paramInfo
  let mut modes := #[]
  for h : i in *...numArgs do
    let mode ← if hInfo : i < infos.size then
      let info := infos[i]
      if info.isInstance && (!cfg.instances || cfg.ground) then pure ChildMode.fixed
      else if !info.hasFwdDeps then pure .simp
      else if (← whnfD (← inferType (e.stripArgsN (numArgs - i)))).isArrow then pure .simp
      else pure .dsimp
    else if (← whnfD (← inferType (e.stripArgsN (numArgs - i)))).isArrow then pure .simp
    else pure .dsimp
    modes := modes.push mode
  emitStructural (.congruence invocationOrdinal (.generic modes))
  recordBranch "struct.congruence.generic"
  let rec visit (e : Expr) (i : Nat) : EngineM Result := do
    if i == 0 then
      withPath .appFunction <| simp f
    else
      checkSystem "simp"
      let i := i - 1
      let .app f a := e | unreachable!
      let fr ← visit f i
      if h : i < infos.size then
        let info := infos[i]
        trace[Debug.Meta.Tactic.simp] "app [{i}] {infos.size} {a} hasFwdDeps: {infos[i].hasFwdDeps}"
        if info.isInstance && (!cfg.instances || cfg.ground) then
          /-
          **Note**: We don't visit instance implicit arguments when we are reducing ground terms.
          Motivation: many instance implicit arguments are ground, and it does not make sense
          to reduce them if the parent term is not ground.
          -/
          mkCongrFun' e fr a
        else if !info.hasFwdDeps then
          mkCongr' e fr (← withPath (.appArgument i .simp) <| simp a)
        else if (← whnfD (← inferType f)).isArrow then
          mkCongr' e fr (← withPath (.appArgument i .simp) <| simp a)
        else
          mkCongrFun' e fr (← withPath (.appArgument i .dsimp) <| dsimp a)
      else if (← whnfD (← inferType f)).isArrow then
        mkCongr' e fr (← withPath (.appArgument i .simp) <| simp a)
      else
        mkCongrFun' e fr (← withPath (.appArgument i .dsimp) <| dsimp a)
  visit e numArgs


/--
Try to use automatically generated congruence theorems. See `mkCongrSimp?`.
-/
private def generatedCongruenceArgKind : CongrArgKind → GeneratedCongruenceArgKind
  | .fixed => .fixed
  | .fixedNoParam => .fixedNoParam
  | .eq => .eq
  | .cast => .cast
  | .heq => .heq
  | .subsingletonInst => .subsingletonInst

def tryAutoCongrTheorem? (e : Expr) (invocationOrdinal : Nat) : EngineM (Option Result) := do
  let f := e.getAppFn
  -- TODO: cache
  let some cgrThm ← Simp.mkCongrSimp? f | return none
  if cgrThm.argKinds.size != e.getAppNumArgs then return none
  let args := e.getAppArgs
  let infos := (← getFunInfoNArgs f args.size).paramInfo
  let config ← getConfig
  let mut childModes := #[]
  for h : i in *...cgrThm.argKinds.size do
    let kind := cgrThm.argKinds[i]
    let mode := if config.ground && i < infos.size && infos[i]!.isInstance then
      ChildMode.fixed
    else match kind with
      | .fixed => .dsimp
      | .eq => .simp
      | .cast | .subsingletonInst => .fixed
      | _ => .fixed
    childModes := childModes.push mode
  let theoremTypeFingerprint ← liftM (exprFingerprintHash cgrThm.type)
  let proofFingerprint ← liftM (exprStructuralFingerprintHash cgrThm.proof)
  let argumentKinds := cgrThm.argKinds.map generatedCongruenceArgKind
  let mut synthesizedAssignments := #[]
  let mut simplified := false
  let mut hasProof   := false
  let mut hasCast    := false
  let mut argsNew    := #[]
  let mut argResults := #[]
  let mut i          := 0 -- index at args
  for arg in args, kind in cgrThm.argKinds do
    if h : config.ground ∧ i < infos.size then
      if (infos[i]'h.2).isInstance then
        -- Do not visit instance implicit arguments when `ground := true`
        -- See comment at `congrArgs`
        argsNew := argsNew.push arg
        i := i + 1
        continue
    match kind with
    | CongrArgKind.fixed =>
      let argNew ← withPath (.autoCongrArgument i .dsimp) <| dsimp arg
      if arg != argNew then
        simplified := true
      argsNew := argsNew.push argNew
    | CongrArgKind.cast  => hasCast := true; argsNew := argsNew.push arg
    | CongrArgKind.subsingletonInst => argsNew := argsNew.push arg
    | CongrArgKind.eq =>
      let argResult ← withPath (.autoCongrArgument i .simp) <| simp arg
      argResults := argResults.push argResult
      argsNew    := argsNew.push argResult.expr
      if argResult.proof?.isSome then hasProof := true
      if arg != argResult.expr then simplified := true
    | _ => unreachable!
    i := i + 1
  if !simplified then
    emitStructural (.congruence invocationOrdinal
      (.generated theoremTypeFingerprint proofFingerprint argumentKinds childModes
        synthesizedAssignments))
    recordBranch "struct.congruence.generated"
    return some { expr := e }
  /-
    If `hasProof` is false, we used to return `mkAppN f argsNew` with `proof? := none`.
    However, this created a regression when we started using `proof? := none` for `rfl` theorems.
    Consider the following goal
    ```
    m n : Nat
    a : Fin n
    h₁ : m < n
    h₂ : Nat.pred (Nat.succ m) < n
    ⊢ Fin.succ (Fin.mk m h₁) = Fin.succ (Fin.mk m.succ.pred h₂)
    ```
    The term `m.succ.pred` is simplified to `m` using a `Nat.pred_succ` which is a `rfl` theorem.
    The auto generated theorem for `Fin.mk` has casts and if used here at `Fin.mk m.succ.pred h₂`,
    it produces the term `Fin.mk m (id (Eq.refl m) ▸ h₂)`. The key property here is that the
    proof `(id (Eq.refl m) ▸ h₂)` has type `m < n`. If we had just returned `mkAppN f argsNew`,
    the resulting term would be `Fin.mk m h₂` which is type correct, but later we would not be
    able to apply `eq_self` to
    ```lean
    Fin.succ (Fin.mk m h₁) = Fin.succ (Fin.mk m h₂)
    ```
    because we would not be able to establish that `m < n` and `Nat.pred (Nat.succ m) < n` are definitionally
    equal using `TransparencyMode.reducible` (`Nat.pred` is not reducible).
    Thus, we decided to return here only if the auto generated congruence theorem does not introduce casts.
  -/
  if !hasProof && !hasCast then
    emitStructural (.congruence invocationOrdinal
      (.generated theoremTypeFingerprint proofFingerprint argumentKinds childModes
        synthesizedAssignments))
    recordBranch "struct.congruence.generated"
    return some { expr := mkAppN f argsNew }
  let mut proof := cgrThm.proof
  let mut type  := cgrThm.type
  let mut j := 0 -- index at argResults
  let mut subst := #[]
  for arg in args, argNew in argsNew, kind in cgrThm.argKinds do
    proof := mkApp proof arg
    type := type.bindingBody!
    match kind with
    | CongrArgKind.fixed =>
      /-
      We use `argNew` here because `dsimp` may have simplified the fixed argument.
      See issue #4339
      -/
      subst := subst.push argNew
    | CongrArgKind.cast  =>
      subst := subst.push arg
    | CongrArgKind.subsingletonInst =>
      subst := subst.push arg
      let clsNew := type.bindingDomain!.instantiateRev subst
      let instNew ← if (← isDefEq (← inferType arg) clsNew) then
        pure arg
      else
        match (← trySynthInstance clsNew) with
        | LOption.some val => pure val
        | _ =>
          trace[Meta.Tactic.simp.congr] "failed to synthesize instance{indentExpr clsNew}"
          return none
      proof := mkApp proof instNew
      synthesizedAssignments := synthesizedAssignments.push
        (← liftM (exprFingerprintHash (← instantiateMVars instNew)))
      subst := subst.push instNew
      type := type.bindingBody!
    | CongrArgKind.eq =>
      subst := subst.push arg
      let argResult := argResults[j]!
      let argProof ← argResult.getProof' arg
      j := j + 1
      proof := mkApp2 proof argResult.expr argProof
      subst := subst.push argResult.expr |>.push argProof
      type := type.bindingBody!.bindingBody!
    | _ => unreachable!
  let some (_, _, rhs) := type.instantiateRev subst |>.eq? | unreachable!
  let rhs ← if hasCast then removeUnnecessaryCasts rhs else pure rhs
  emitStructural (.congruence invocationOrdinal
    (.generated theoremTypeFingerprint proofFingerprint argumentKinds childModes
      synthesizedAssignments))
  recordBranch "struct.congruence.generated"
  if hasProof then
    return some { expr := rhs, proof? := proof }
  else
    /- See comment above. This is reachable if `hasCast == true`. The `rhs` is not structurally equal to `mkAppN f argsNew` -/
    return some { expr := rhs }

def simpProj (e : Expr) : EngineM Result := do
  match (← withSimpMetaConfig <| reduceProj? e) with
  | some eNew =>
    let reduction := match e with
      | .proj structureName field _ => Reduction.projection structureName field
      | _ => unreachable!
    commitReduction "reduce.simpProjection" e eNew reduction
    return { expr := eNew }
  | none =>
    let s := e.projExpr!
    let motive? ← withLocalDeclD `s (← inferType s) fun s => do
      let p := e.updateProj! s
      if (← dependsOn (← inferType p) s.fvarId!) then
        return none
      else
        let motive ← mkLambdaFVars #[s] (← mkEq e p)
        if !(← isTypeCorrect motive) then
          return none
        else
          return some motive
    if let some motive := motive? then
      let .proj structureName field _ := e | unreachable!
      emitStructural (.projectionMajor structureName field .simp)
      recordBranch "struct.projectionMajor.simp"
      let r ← withPath (.projectionMajor .simp) <| simp s
      let eNew := e.updateProj! r.expr
      match r.proof? with
      | none => return { expr := eNew }
      | some h =>
        let hNew ← mkEqNDRec motive (← mkEqRefl e) h
        return { expr := eNew, proof? := some hNew }
    else
      let .proj structureName field _ := e | unreachable!
      emitStructural (.projectionMajor structureName field .dsimp)
      recordBranch "struct.projectionMajor.dsimp"
      return { expr := (← withPath (.projectionMajor .dsimp) <| dsimp e) }

def simpConst (e : Expr) : EngineM Result :=
  return { expr := (← reduce e) }

def simpLambda (e : Expr) : EngineM Result :=
  withParent e <| lambdaTelescopeDSimp e fun xs e => withNewLemmas xs do
    let r ← simp e
    r.addLambdas xs

def simpArrow (e : Expr) : EngineM Result := do
  trace[Debug.Meta.Tactic.simp] "arrow {e}"
  let p := e.bindingDomain!
  let q := e.bindingBody!
  let rp ← withPath .implicationDomain <| simp p
  trace[Debug.Meta.Tactic.simp] "arrow [{(← getConfig).contextual}] {p} [{← isProp p}] -> {q} [{← isProp q}]"
  if (← pure (← getConfig).contextual <&&> isProp p <&&> isProp q) then
    emitStructural (.forallBranch .implicationContextual)
    recordBranch "struct.forall.implicationContextual"
    trace[Debug.Meta.Tactic.simp] "ctx arrow {rp.expr} -> {q}"
    withLocalDeclD e.bindingName! rp.expr fun h => withNewLemmas #[h] do
      let rq ← withPath .implicationBody <| simp q
      match rq.proof? with
      | none    => mkImpCongr e rp rq
      | some hq =>
        let hq ← mkLambdaFVars #[h] hq
        /-
          We use the default reducibility setting at `mkImpDepCongrCtx` and `mkImpCongrCtx` because they use the theorems
          ```lean
          @implies_dep_congr_ctx : ∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
          @implies_congr_ctx : ∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p₁ → q₁) = (p₂ → q₂)
          ```
          And the proofs may be from `rfl` theorems which are now omitted. Moreover, we cannot establish that the two
          terms are definitionally equal using `withReducible`.
          TODO (better solution): provide the problematic implicit arguments explicitly. It is more efficient and avoids this
          problem.
          -/
        if rq.expr.containsFVar h.fvarId! then
          return { expr := (← mkForallFVars #[h] rq.expr), proof? := (← withDefault <| mkImpDepCongrCtx (← rp.getProof) hq) }
        else
          return { expr := e.updateForallE! rp.expr rq.expr, proof? := (← withDefault <| mkImpCongrCtx (← rp.getProof) hq) }
  else
    emitStructural (.forallBranch .implicationPlain)
    recordBranch "struct.forall.implicationPlain"
    mkImpCongr e rp (← withPath .implicationBody <| simp q)

def simpForall (e : Expr) : EngineM Result := withParent e do
  trace[Debug.Meta.Tactic.simp] "forall {e}"
  if e.isArrow then
    simpArrow e
  else if (← isProp e) then
    /- The forall is a proposition. -/
    let domain := e.bindingDomain!
    if (← isProp domain) then
      /-
      The domain of the forall is also a proposition, and we can use `forall_prop_domain_congr`
      IF we can simplify the domain.
      -/
      let rd ← withPath (.forallDomain 0) <| simp domain
      if let some h₁ := rd.proof? then
        emitStructural (.forallBranch .propositionDomainTransport)
        recordBranch "struct.forall.propositionDomainTransport"
        /- Using
        ```
        theorem forall_prop_domain_congr {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → Prop}
            (h₁ : p₁ = p₂)
            (h₂ : ∀ a : p₂, q₁ (h₁.substr a) = q₂ a)
            : (∀ a : p₁, q₁ a) = (∀ a : p₂, q₂ a)
        ```
        Remark: we should consider whether we want to add congruence lemma support for arbitrary `forall`-expressions.
        Then, the theorem above can be marked as `@[congr]` and the following code deleted.
        -/
        let p₁ := domain
        let p₂ := rd.expr
        let q₁ := mkLambda e.bindingName! e.bindingInfo! p₁ e.bindingBody!
        let result ← withLocalDecl e.bindingName! e.bindingInfo! p₂ fun a => withNewLemmas #[a] do
          let prop := mkSort Level.zero
          let h₁_substr_a := mkApp6 (mkConst ``Eq.substr [Level.one]) prop (mkLambda `x .default prop (mkBVar 0)) p₂ p₁ h₁ a
          let q_h₁_substr_a := e.bindingBody!.instantiate1 h₁_substr_a
          let rb ← withPath .forallBody <| simp q_h₁_substr_a
          let h₂ ← mkLambdaFVars #[a] (← rb.getProof)
          let q₂ ← mkLambdaFVars #[a] rb.expr
          let result ← mkForallFVars #[a] rb.expr
          let proof := mkApp6 (mkConst ``forall_prop_domain_congr) p₁ p₂ q₁ q₂ h₁ h₂
          return { expr := result, proof? := proof }
        return result
    emitStructural (.forallBranch .propositionDomainDSimp)
    recordBranch "struct.forall.propositionDomainDSimp"
    let domain ← withPath (.forallDomain 0) <| dsimp domain
    withLocalDecl e.bindingName! e.bindingInfo! domain fun x => withNewLemmas #[x] do
      let b := e.bindingBody!.instantiate1 x
      let rb ← withPath .forallBody <| simp b
      let eNew ← mkForallFVars #[x] rb.expr
      match rb.proof? with
      | none   => return { expr := eNew }
      | some h => return { expr := eNew, proof? := (← mkForallCongr (← mkLambdaFVars #[x] h)) }
  else
    emitStructural (.forallBranch .nonPropositionDSimp)
    recordBranch "struct.forall.nonPropositionDSimp"
    return { expr := (← dsimp e) }

/-- Adapter for `Meta.simpHaveTelescope` -/
def simpHaveTelescope (e : Expr) : EngineM Result := do
  -- **Note**: Eliminating unused-let declarations in a single pass may produce O(n^2) proofs.
  let zetaUnusedMode := if (← getConfig).zetaUnused then .singlePass else .no
  let info ← Meta.getHaveTelescopeInfo e
  let (fixed, usedRaw) ← info.computeFixedUsed
    (keepUnused := zetaUnusedMode matches .no | .twoPasses)
  let used := if usedRaw.isEmpty then Array.replicate info.haveInfo.size true else usedRaw
  emitStructural (.haveTelescope fixed used)
  recordBranch "struct.haveTelescope"
  let mut paths := #[]
  for index in *...info.haveInfo.size do
    if !used.getD index true then
      emitStructural (.dropUnusedHave index)
      recordBranch "struct.dropUnusedHave"
    else if fixed.getD index true then
      paths := paths.push (.haveValue index .dsimp)
    else
      paths := paths.push (.haveValue index .simp)
  paths := paths.push .haveBody
  modifyRecorderState fun state => { state with pendingMonadSimpPaths := paths }
  match (← Meta.simpHaveTelescope e zetaUnusedMode) with
  | .rfl =>
    modifyRecorderState fun state => { state with pendingMonadSimpPaths := #[] }
    return { expr := e }
  | .step e' h =>
    modifyRecorderState fun state => { state with pendingMonadSimpPaths := #[] }
    if debug.simp.check.have.get (← getOptions) then
      check e'
      check h
    return { expr := e', proof? := h }

/--
Routine for simplifying `let` expressions.

If it is a `have`, we use `simpHaveTelescope` to simplify entire telescopes at once, to avoid quadratic behavior
arising from locally nameless expression representations.

We assume that dependent `let`s are dependent,
but if `Config.letToHave` is enabled then we attempt to transform it into a `have`.
If that does not change it, then it is only `dsimp`ed.
-/
def simpLet (e : Expr) : EngineM Result := do
  withTraceNode `Debug.Meta.Tactic.simp (fun _ => return m!"let{indentExpr e}") do
    assert! e.isLet
    /-
    Recall: `simpLet` is called after `reduceStep` is applied, so `simpLet` is not responsible for zeta reduction.
    Hence, the expression is a `let` or `have` that is not reducible in the current configuration.
    -/
    if e.letNondep! then
      simpHaveTelescope e
    else
      /-
      When `cfg.letToHave` is true, we use `letToHave` to decide whether or not this `let` is dependent.
      If it becomes a `have`, then we can jump right into simplifying the `have` telescope.
      -/
      let e ←
        if (← getConfig).letToHave then
          let eNew ← letToHave e
          if eNew.isLet && eNew.letNondep! then
            trace[Debug.Meta.Tactic.simp] "letToHave ==>{indentExpr eNew}"
            emitStructural .letToHave
            recordBranch "struct.letToHave"
            return ← simpHaveTelescope eNew
          pure eNew
        else
          pure e
      /-
      The `let` is dependent.
      We fall back to doing only definitional simplification.

      Note that for `let x := v; b`, if we had a rewrite `h : b = b'` given `x := v` in the local context,
      we could abstract `x` to get `(let x := v; h) : (let x := v; b = b')` and then use the fact that
      this type is definitionally equal to `(let x := v; b) = (let x := v; b')`.
      -/
      return { expr := (← dsimp e) }

private def dsimpReduce : DSimproc := fun e => do
  let mut eNew ← reduce e
  if eNew.isFVar then
    eNew ← reduceFVar (← getConfig) (← getSimpTheorems) eNew
  if eNew != e then return .visit eNew else return .done e

/-- Auxiliary `dsimproc` for not visiting proof terms. -/
private def doNotVisitProofs : DSimproc := fun e => do
  if ← isProof e then
    if !backward.dsimp.proofs.get (← getOptions) then
      return .done e
    else
      return .continue e
  else
    return .continue e

/-- Helper `dsimproc` for `doNotVisitOfNat` and `doNotVisitOfScientific` -/
private def doNotVisit (pred : Expr → Bool) (declName : Name) : DSimproc := fun e => do
  if pred e then
    if (← readThe Simp.Context).isDeclToUnfold declName then
      return .continue e
    else
      -- Users may have added a `[simp]` rfl theorem for the literal
      match (← (← getMethods).dpost e) with
      | .continue none => return .done e
      | r => return r
  else
    return .continue e

/--
Auxiliary `dsimproc` for not visiting `OfNat.ofNat` application subterms.
This is the `dsimp` equivalent of the approach used at `visitApp`.
Recall that we fold orphan raw Nat literals.
-/
private def doNotVisitOfNat : DSimproc := doNotVisit isOfNatNatLit ``OfNat.ofNat

/--
Auxiliary `dsimproc` for not visiting `OfScientific.ofScientific` application subterms.
-/
private def doNotVisitOfScientific : DSimproc := doNotVisit isOfScientificLit ``OfScientific.ofScientific

/--
Auxiliary `dsimproc` for not visiting `Char` literal subterms.
-/
private def doNotVisitCharLit : DSimproc := doNotVisit isCharLit ``Char.ofNat

private partial def dsimpTransformWithCache (input : Expr) (initialCache : ExprStructMap Expr)
    (pre post : DSimproc) (usedLetOnly skipInstances : Bool) : EngineM (Expr × ExprStructMap Expr) := do
  emitStructural (.dsimpTransform usedLetOnly skipInstances)
  recordBranch "struct.dsimpTransform"
  visit input initialCache
where
  visit (e : Expr) (cache : ExprStructMap Expr) : EngineM (Expr × ExprStructMap Expr) := do
    let runtime ← getRuntime
    if runtime.mode == .replay then
      if let some expected ← peekReplayStructural? then
        if ← isCurrentReplayStructural expected then
          if let .dsimpCacheHit sourcePath sourceIndex := expected.witness then
            let state ← getRecorderState
            let provenance ← runtime.cacheProvenance.get
            let some actualPath := provenance.dsimpOrder[sourceIndex]?
              | throwError "replay_expected_dsimp_cache_hit: source={repr sourcePath}, path={repr state.path}, cached={provenance.dsimpOrder.size}"
            unless actualPath == sourcePath do
              throwError "replay_dsimp_cache_source_mismatch: source={repr sourcePath}, index={sourceIndex}"
            let some cachedResult := cache.get? { val := e }
              | throwError "replay_dsimp_cache_miss: source={repr sourcePath}, index={sourceIndex}"
            unless provenance.dsimpSources.get? { val := e } == some (sourcePath, sourceIndex) do
              throwError "replay_dsimp_cache_provenance_mismatch: source={repr sourcePath}, index={sourceIndex}"
            emitStructural (.dsimpCacheHit sourcePath sourceIndex)
            return (cachedResult, cache)
    else if let some result := cache.get? { val := e } then
      if runtime.mode == .record then
        let state ← getRecorderState
        let provenance ← runtime.cacheProvenance.get
        match provenance.dsimpSources.get? { val := e } with
        | some (sourcePath, sourceIndex) =>
            emitStructural (.dsimpCacheHit sourcePath sourceIndex)
            recordBranch "struct.dsimpCacheHit"
        | none =>
            let observations ← runtime.observations.get
            unless deferredBySimproc observations.deferred do
              throwError "record_dsimp_cache_source_missing: path={repr state.path}, input={e}"
            recordBranch "boundary.simprocOpaqueDSimpCache"
      return (result, cache)
    withIncRecDepth do
      checkSystem "transform"
      let (result, cache) ← visitUncached e cache
      let cache := cache.insert { val := e } result
      if runtime.mode != .reference then
        let path := (← getRecorderState).path
        runtime.cacheProvenance.modify fun provenance => {
          provenance with
            dsimpSources := provenance.dsimpSources.insert { val := e }
              (path, provenance.dsimpOrder.size)
            dsimpOrder := provenance.dsimpOrder.push path
        }
      return (result, cache)

  visitPost (e : Expr) (cache : ExprStructMap Expr) : EngineM (Expr × ExprStructMap Expr) := do
    match ← withPhase .dpost <| recordDPhaseStep e <| post e with
    | .done output => return (output, cache)
    | .visit output => visit output cache
    | .continue output? => return (output?.getD e, cache)

  visitLambda (fvars : Array Expr) (e : Expr) (cache : ExprStructMap Expr)
      : EngineM (Expr × ExprStructMap Expr) := do
    match e with
    | .lam name domain body binderInfo =>
      let index := fvars.size
      let (domain, cache) ← withPath (.lambdaDomain index) <|
        visit (domain.instantiateRev fvars) cache
      withLocalDecl name binderInfo domain fun x =>
        visitLambda (fvars.push x) body cache
    | expression =>
      let (body, cache) ← withPath .lambdaBody <|
        visit (expression.instantiateRev fvars) cache
      let result ← mkLambdaFVars (usedLetOnly := usedLetOnly) fvars body
      visitPost result cache

  visitForall (fvars : Array Expr) (e : Expr) (cache : ExprStructMap Expr)
      : EngineM (Expr × ExprStructMap Expr) := do
    match e with
    | .forallE name domain body binderInfo =>
      let index := fvars.size
      let (domain, cache) ← withPath (.forallDomain index) <|
        visit (domain.instantiateRev fvars) cache
      withLocalDecl name binderInfo domain fun x =>
        visitForall (fvars.push x) body cache
    | expression =>
      let (body, cache) ← withPath .forallBody <|
        visit (expression.instantiateRev fvars) cache
      let result ← mkForallFVars (usedLetOnly := usedLetOnly) fvars body
      visitPost result cache

  visitLet (fvars : Array Expr) (e : Expr) (cache : ExprStructMap Expr)
      : EngineM (Expr × ExprStructMap Expr) := do
    match e with
    | .letE name type value body nondep =>
      let index := fvars.size
      let (type, cache) ← withPath (.letType index) <|
        visit (type.instantiateRev fvars) cache
      let (value, cache) ← withPath (.letValue index .dsimp) <|
        visit (value.instantiateRev fvars) cache
      withLetDecl name type value (nondep := nondep) fun x =>
        visitLet (fvars.push x) body cache
    | expression =>
      let (body, cache) ← withPath .letBody <|
        visit (expression.instantiateRev fvars) cache
      let result ← mkLetFVars (usedLetOnly := usedLetOnly)
        (generalizeNondepLet := false) fvars body
      visitPost result cache

  visitApp (e : Expr) (cache : ExprStructMap Expr) : EngineM (Expr × ExprStructMap Expr) := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    let (fn, cache) ← withPath .appFunction <| visit fn cache
    let mut cache := cache
    let mut argsNew := args
    let infos ← if skipInstances then pure (← getFunInfoNArgs fn args.size).paramInfo else pure #[]
    for h : index in *...args.size do
      if skipInstances && index < infos.size && infos[index]!.isInstance then continue
      let (arg, cacheNew) ← withPath (.appArgument index .dsimp) <| visit args[index] cache
      argsNew := argsNew.setIfInBounds index arg
      cache := cacheNew
    visitPost (mkAppN fn argsNew) cache

  visitUncached (e : Expr) (cache : ExprStructMap Expr) : EngineM (Expr × ExprStructMap Expr) := do
    match ← withPhase .dpre <| recordDPhaseStep e <| pre e with
    | .done output => return (output, cache)
    | .visit output => visit output cache
    | .continue output? =>
      let expression := output?.getD e
      match expression with
      | .forallE .. => visitForall #[] expression cache
      | .lam .. => visitLambda #[] expression cache
      | .letE .. => visitLet #[] expression cache
      | .app .. => visitApp expression cache
      | .mdata metadata body =>
        recordBranch "struct.metadataBody"
        let (body, cache) ← withPath .metadataBody <| visit body cache
        visitPost (expression.updateMData! body) cache
      | .proj structureName field major =>
        let (major, cache) ← withPath (.projectionMajor .dsimp) <| visit major cache
        visitPost (.proj structureName field major) cache
      | _ => visitPost expression cache

set_option compiler.ignoreBorrowAnnotation true in
@[export explicit_lean_dsimp_engine]
private partial def dsimpImpl (e : Expr) : EngineM Expr := do
  let runtime ← getRuntime
  let invocationOrdinal := (← getRecorderState).dsimpInvocationOrdinal
  if runtime.mode != .reference then
    modifyRecorderState fun state => {
      state with dsimpInvocationOrdinal := state.dsimpInvocationOrdinal + 1 }
  withPath (.dsimpCall invocationOrdinal) do
    let cfg ← getConfig
    unless cfg.dsimp do
      return e
    let m ← getMethods
    -- Recording observes the complete upstream phase pipelines below, so a
    -- replay `dpre`/`dpost` already denotes their final recorded outcome.
    -- Appending the fixed stages again would execute literal guards and
    -- definitional reduction twice after every replayed phase.
    let pre := if runtime.mode == .replay then m.dpre else
      m.dpre >> doNotVisitOfNat >> doNotVisitOfScientific >> doNotVisitCharLit >> doNotVisitProofs
    let post := if runtime.mode == .replay then m.dpost else m.dpost >> dsimpReduce
    withInDSimpWithCache fun cache => do
      dsimpTransformWithCache e cache pre post
        (usedLetOnly := cfg.zeta || cfg.zetaUnused)
        (skipInstances := !cfg.instances)

def visitFn (e : Expr) : EngineM Result := do
  let f := e.getAppFn
  let fNew ← simp f
  if fNew.expr == f then
    return { expr := e }
  else
    let args := e.getAppArgs
    let eNew := mkAppN fNew.expr args
    if fNew.proof?.isNone then return { expr := eNew }
    let mut proof ← fNew.getProof
    for arg in args do
      proof ← Meta.mkCongrFun proof arg
    return { expr := eNew, proof? := proof }

private def recorderStateProgressed (before after : RecorderState) : EngineM Bool := do
  let provenance ← (← getRuntime).cacheProvenance.get
  return before.program.events.size != after.program.events.size ||
    before.program.structural.size != after.program.structural.size ||
    before.phaseInvocationOrdinal != after.phaseInvocationOrdinal ||
    before.congruenceInvocationOrdinal != after.congruenceInvocationOrdinal ||
    before.simpInvocationOrdinal != after.simpInvocationOrdinal ||
    before.dsimpInvocationOrdinal != after.dsimpInvocationOrdinal ||
    before.simpStepOrdinal != after.simpStepOrdinal ||
    before.savedSimpCacheProducerCount != provenance.simpOrder.size ||
    before.savedDSimpCacheProducerCount != provenance.dsimpOrder.size

private def expressionFingerprints (expressions : Array Expr) : EngineM (Array String) :=
  expressions.mapM fun expression => do
    liftM (exprFingerprintHash (← instantiateMVars expression))

private def beginPremiseProgram (type : Expr) (index : Nat)
    (expectedPremises? : Option (Array PremiseProgram)) : EngineM RecorderState := do
  let outer ← getRecorderState
  let runtime ← getRuntime
  if runtime.mode == .record then
    let fingerprint ← liftM (exprFingerprintHash type)
    runtime.state.set {
      outer with
      program := { initialFingerprint := fingerprint, finalFingerprint := fingerprint }
      path.steps := outer.path.steps.push (.premise index)
      lastPremiseTerminal := none
      phaseInvocationOrdinal := 0
      currentPhaseInvocationOrdinal := 0
      congruenceInvocationOrdinal := 0
      simpInvocationOrdinal := 0
      dsimpInvocationOrdinal := 0
      pathInvocationOrdinal := 0
      simpStepOrdinal := 0
    }
  else if runtime.mode == .replay then
    let premises ← match expectedPremises? with
      | some premises => pure premises
      | none => do
          let some event := outer.program.events[outer.eventCursor]?
            | throwError "replay_missing_parent_rewrite_for_premise"
          pure <| match event.operation with
            | .rewrite _ _ premises | .rewriteAttemptFailed _ _ premises => premises
            | _ => #[]
    if premises.isEmpty then
      throwError "replay_expected_parent_rewrite_for_premise"
    let some premise := premises[index]?
      | throwError "replay_missing_premise_program: {index}"
    let actualFingerprint ← liftM (exprFingerprintHash type)
    unless actualFingerprint == premise.propositionFingerprint do
      throwError "replay_premise_fingerprint_mismatch: expected {premise.propositionFingerprint}, got {actualFingerprint}"
    runtime.state.set {
      outer with
      program := premise.program
      eventCursor := 0
      structuralCursor := 0
      path.steps := outer.path.steps.push (.premise index)
      lastPremiseTerminal := none
      expectedPremiseTerminal := some premise.terminal
      phaseInvocationOrdinal := 0
      currentPhaseInvocationOrdinal := 0
      congruenceInvocationOrdinal := 0
      simpInvocationOrdinal := 0
      dsimpInvocationOrdinal := 0
      pathInvocationOrdinal := 0
      simpStepOrdinal := 0
    }
  return outer

private def finishPremiseProgram (outer : RecorderState) (type : Expr) : EngineM PremiseProgram := do
  let runtime ← getRuntime
  if runtime.mode == .record then
    let inner ← runtime.state.get
    runtime.state.set outer
    return {
      propositionFingerprint := ← liftM (exprFingerprintHash type)
      program := inner.program
      terminal := inner.lastPremiseTerminal.getD .isTrue
    }
  else if runtime.mode == .replay then
    let inner ← runtime.state.get
    liftM <| assertReplayProgramConsumed inner
    let actualFingerprint ← liftM (exprFingerprintHash type)
    let some terminal := inner.lastPremiseTerminal
      | throwError "replay_missing_premise_terminal"
    unless inner.expectedPremiseTerminal == some terminal do
      throwError "replay_premise_terminal_mismatch"
    if terminal matches .localAssumption _ | .equationHypothesis then
      unless inner.program.finalFingerprint == actualFingerprint do
        throwError "replay_premise_final_fingerprint_mismatch: expected {inner.program.finalFingerprint}, got {actualFingerprint}"
    runtime.state.set outer
    return {
      propositionFingerprint := actualFingerprint
      program := inner.program
      terminal
    }
  else
    return {
      propositionFingerprint := ""
      program := {}
      terminal := .isTrue
    }

private def setProgramFinal (expression : Expr) : EngineM Unit := do
  let fingerprint ← liftM (exprFingerprintHash expression)
  let runtime ← getRuntime
  if runtime.mode == .record then
    runtime.state.modify fun state => { state with program.finalFingerprint := fingerprint }
  else if runtime.mode == .replay then
    let state ← runtime.state.get
    unless state.program.finalFingerprint == fingerprint do
      throwError "replay_final_fingerprint_mismatch: expected {state.program.finalFingerprint}, got {fingerprint}"

private def dischargeRecorded? (_thmId : Origin) (x type : Expr)
    (premiseIndex : Nat) (expectedPremises? : Option (Array PremiseProgram)) :
    EngineM (Option (PremiseProgram × Bool)) := do
  let outer ← beginPremiseProgram type premiseIndex expectedPremises?
  let usedTheorems := (← get).usedTheorems
  let ctx ← getContext
  if ctx.dischargeDepth >= ctx.maxDischargeDepth then
    restoreRecorderState outer
    return none
  let methods ← getMethods
  if methods.customDischarger then
    deferRecording .customDischarger
    recordBranch "boundary.customDischarger"
  let proof? ← withIncDischargeDepth <| withPreservedCache <| methods.discharge? type
  let some proof := proof? | do
    modify fun state => { state with usedTheorems }
    setPremiseTerminal .failed
    return some (← finishPremiseProgram outer type, false)
  unless (← isDefEq x proof) do
    modify fun state => { state with usedTheorems }
    setPremiseTerminal .failed
    return some (← finishPremiseProgram outer type, false)
  recordBranch "rewrite.premise"
  return some (← finishPremiseProgram outer type, true)

private inductive ArgumentSynthesis where
  | success (premises : Array PremiseProgram)
  | failed (premises : Array PremiseProgram)

private def synthesizeRecordedArgs (thmId : Origin) (bis : Array BinderInfo)
    (xs : Array Expr) (expectedPremises? : Option (Array PremiseProgram) := none) :
    EngineM ArgumentSynthesis := do
  let skipAssignedInstances := tactic.skipAssignedInstances.get (← getOptions)
  let mut premises := #[]
  for x in xs, bi in bis do
    let type ← inferType x
    if !skipAssignedInstances && bi.isInstImplicit then
      unless (← synthesizeInstance x type) do return .failed premises
    if (← instantiateMVars x).isMVar then
      if (← isClass? type).isSome then
        if (← synthesizeInstance x type) then continue
      if (← isProp type) then
        let some (premise, succeeded) ← dischargeRecorded? thmId x type premises.size
            expectedPremises?
          | return .failed premises
        premises := premises.push premise
        unless succeeded do return .failed premises
  return .success premises
where
  synthesizeInstance (x type : Expr) : EngineM Bool := do
    match (← trySynthInstance type) with
    | .some value => withReducibleAndInstances <| isDefEq x value
    | _ => return false

partial def congrDefault (e : Expr) (invocationOrdinal : Nat) : EngineM Result := do
  if (← getRuntime).mode == .replay then
    let some choice ← findReplayCongruenceChoice? invocationOrdinal
      | let state ← getRecorderState
        throwError "replay_missing_congruence_choice: invocation={invocationOrdinal}, path={repr state.path}, structuralCursor={state.structuralCursor}"
    match choice with
    | .generated .. =>
        let some result ← tryAutoCongrTheorem? e invocationOrdinal
          | throwError "replay_generated_congruence_failed"
        return ← result.mkEqTrans (← visitFn result.expr)
    | .generic .. =>
        return ← withParent e <| simpAppUsingCongr e invocationOrdinal
    | .generatedAttemptFailed =>
        if (← tryAutoCongrTheorem? e invocationOrdinal).isSome then
          throwError "replay_expected_generated_congruence_failure"
        emitStructural (.congruence invocationOrdinal .generatedAttemptFailed)
        return ← congrDefault e invocationOrdinal
    | .user .. | .userAttemptFailed .. =>
        throwError "replay_user_congruence_reached_default"
  let recorderSaved ← saveRecorderState
  if let some result ← tryAutoCongrTheorem? e invocationOrdinal then
    result.mkEqTrans (← visitFn result.expr)
  else do
    let after ← getRecorderState
    if ← recorderStateProgressed recorderSaved after then
      emitStructural (.congruence invocationOrdinal .generatedAttemptFailed)
      recordBranch "struct.congruence.generatedAttemptFailed"
    else
      restoreRecorderState recorderSaved
    withParent e <| simpAppUsingCongr e invocationOrdinal

/-- Process the given congruence theorem hypothesis. Return true if it made "progress". -/
def processCongrHypothesis (h : Expr) (hType : Expr) : EngineM Bool := do
  forallTelescopeReducing hType fun xs hType => withNewLemmas xs do
    let lhs ← instantiateMVars hType.appFn!.appArg!
    let r ← simp lhs
    let rhs := hType.appArg!
    rhs.withApp fun m zs => do
      let val ← mkLambdaFVars zs r.expr
      unless (← withSimpMetaConfig <| isDefEq m val) do
        throwCongrHypothesisFailed
      let mut proof ← r.getProof
      if hType.isAppOf ``Iff then
        try proof ← mkIffOfEq proof
        catch _ => throwCongrHypothesisFailed
      unless (← isDefEq h (← mkLambdaFVars xs proof)) do
        throwCongrHypothesisFailed
      /- We used to return `false` if `r.proof? = none` (i.e., an implicit `rfl` proof) because we
          assumed `dsimp` would also be able to simplify the term, but this is not true
          for non-trivial user-provided theorems.
          Example:
          ```
          @[congr] theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a, mem a s → f a = g a) : image f s = image g s :=
          ...

          example {Γ: Set Nat}: (image (Nat.succ ∘ Nat.succ) Γ) = (image (fun a => a.succ.succ) Γ) := by
            simp only [Function.comp_apply]
          ```
          `Function.comp_apply` is a `rfl` theorem, but `dsimp` will not apply it because the composition
          is not fully applied. See comment at issue #1113

          Thus, we have an extra check now if `xs.size > 0`. TODO: refine this test.
      -/
      return r.proof?.isSome || (xs.size > 0 && lhs != r.expr)

private structure UserCongruenceAttempt where
  result? : Option Result
  theoremFingerprint : String
  matchEnvelope : MatchEnvelope
  premises : Array PremiseProgram

/-- Try to rewrite `e` children using the given congruence theorem. -/
private def trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr)
    (expectedPremises? : Option (Array PremiseProgram) := none)
    (replayExpectsSuccess : Bool := false) :
    EngineM (Option UserCongruenceAttempt) := withNewMCtxDepth do withParent e do
  recordCongrTheorem c.theoremName
  trace[Debug.Meta.Tactic.simp.congr] "{c.theoremName}, {e}"
  let thm ← mkConstWithFreshMVarLevels c.theoremName
  let thmType ← inferType thm
  let theoremFingerprint ← liftM (exprFingerprintHash thmType)
  let thmHasBinderNameHint := thmType.hasBinderNameHint
  let (xs, bis, type) ← forallMetaTelescopeReducing thmType
  let makeAttempt (result? : Option Result) (premises : Array PremiseProgram) :
      EngineM UserCongruenceAttempt := do
    let binderAssignments ← expressionFingerprints xs
    let instanceAssignments ← expressionFingerprints <|
      (xs.zip bis).foldl (init := #[]) fun assignments (x, bi) =>
        if bi.isInstImplicit then assignments.push x else assignments
    return {
      result?
      theoremFingerprint
      matchEnvelope := {
        binderAssignments
        instanceAssignments
        proofPresent := result?.bind (fun result => result.proof?) |>.isSome
      }
      premises
    }
  if c.hypothesesPos.any (· ≥ xs.size) then
    return none
  let isIff := type.isAppOf ``Iff
  let lhs := type.appFn!.appArg!
  let rhs := type.appArg!
  let numArgs := lhs.getAppNumArgs
  let mut e := e
  let mut extraArgs := #[]
  if e.getAppNumArgs > numArgs then
    let args := e.getAppArgs
    e := mkAppN e.getAppFn args[*...numArgs]
    extraArgs := args[numArgs...*].toArray
  if (← withSimpMetaConfig <| isDefEq lhs e) then
    let mut modified := false
    for i in c.hypothesesPos do
      let h := xs[i]!
      let hType ← instantiateMVars (← inferType h)
      let hType ← if thmHasBinderNameHint then hType.resolveBinderNameHint else pure hType
      try
        if (← withPath (.userCongrHypothesis c.theoremName i) <|
            processCongrHypothesis h hType) then
          modified := true
      catch ex =>
        -- Upstream treats any ordinary hypothesis-processing exception as a
        -- failed congruence candidate.  A certificate-selected successful
        -- candidate is no longer speculative, however: swallowing a nested
        -- replay validation error would disguise the real divergence as a
        -- later match-envelope mismatch.
        if replayExpectsSuccess then throw ex
        trace[Meta.Tactic.simp.congr] "processCongrHypothesis {c.theoremName} failed {hType}"
        -- Remark: we don't need to check ex.isMaxRecDepth anymore since `try .. catch ..`
        -- does not catch runtime exceptions by default.
        return some (← makeAttempt none #[])
    unless modified do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} not modified"
      return some (← makeAttempt none #[])
    let synthesis ← synthesizeRecordedArgs (.decl c.theoremName) bis xs expectedPremises?
    let premises := match synthesis with
      | .success premises | .failed premises => premises
    unless synthesis matches .success _ do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} synthesizeArgs failed"
      return some (← makeAttempt none premises)
    let eNew ← instantiateMVars rhs
    let mut proof ← instantiateMVars (mkAppN thm xs)
    if isIff then
      try proof ← mkAppM ``propext #[proof]
      catch _ => return some (← makeAttempt none premises)
    if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
      trace[Meta.Tactic.simp.congr] "{c.theoremName} has unassigned metavariables"
      return some (← makeAttempt none premises)
    let result ← congrArgs { expr := eNew, proof? := proof } extraArgs
    return some (← makeAttempt (some result) premises)
  else
    return none

private partial def replayCongruence (e : Expr) (invocationOrdinal : Nat) : EngineM Result := do
    let some choice ← findReplayCongruenceChoice? invocationOrdinal
      | let state ← getRecorderState
        throwError "replay_missing_congruence_choice: invocation={invocationOrdinal}, path={repr state.path}, structuralCursor={state.structuralCursor}"
    match choice with
    | .user theoremName priority hypotheses theoremFingerprint envelope premises =>
        let candidate ← mkSimpCongrTheorem theoremName priority
        unless candidate.hypothesesPos == hypotheses do
          throwError "replay_user_congruence_shape_mismatch: {theoremName}"
        let some attempt ← trySimpCongrTheorem? candidate e (some premises) true
          | throwError "replay_user_congruence_failed: {theoremName}"
        unless attempt.theoremFingerprint == theoremFingerprint &&
            attempt.matchEnvelope == envelope do
          throwError "replay_user_congruence_match_mismatch: {theoremName}; expectedTheorem={theoremFingerprint}; actualTheorem={attempt.theoremFingerprint}; expectedEnvelope={repr envelope}; actualEnvelope={repr attempt.matchEnvelope}"
        let some result := attempt.result?
          | throwError "replay_user_congruence_failed: {theoremName}"
        emitStructural (.congruence invocationOrdinal (.user theoremName priority hypotheses
          attempt.theoremFingerprint attempt.matchEnvelope attempt.premises))
        return result
    | .userAttemptFailed theoremName priority hypotheses theoremFingerprint envelope premises =>
        let candidate ← mkSimpCongrTheorem theoremName priority
        unless candidate.hypothesesPos == hypotheses do
          throwError "replay_user_congruence_shape_mismatch: {theoremName}"
        let some attempt ← trySimpCongrTheorem? candidate e (some premises)
          | throwError "replay_expected_user_congruence_attempt: {theoremName}"
        unless attempt.theoremFingerprint == theoremFingerprint &&
            attempt.matchEnvelope == envelope do
          throwError "replay_user_congruence_match_mismatch: {theoremName}; expectedTheorem={theoremFingerprint}; actualTheorem={attempt.theoremFingerprint}; expectedEnvelope={repr envelope}; actualEnvelope={repr attempt.matchEnvelope}"
        if attempt.result?.isSome then
          throwError "replay_expected_user_congruence_failure: {theoremName}"
        emitStructural (.congruence invocationOrdinal
          (.userAttemptFailed theoremName priority hypotheses attempt.theoremFingerprint
            attempt.matchEnvelope attempt.premises))
        replayCongruence e invocationOrdinal
    | _ => return ← congrDefault e invocationOrdinal

def congr (e : Expr) : EngineM Result := do
  let invocationOrdinal ← nextCongruenceInvocationOrdinal
  if (← getRuntime).mode == .replay then
    return ← replayCongruence e invocationOrdinal
  let f := e.getAppFn
  if f.isConst then
    let congrThms ← getSimpCongrTheorems
    let cs := congrThms.get f.constName!
    for c in cs do
      let recorderSaved ← saveRecorderState
      match (← trySimpCongrTheorem? c e) with
      | none =>
        restoreRecorderState recorderSaved
      | some attempt => match attempt.result? with
        | none =>
            let after ← getRecorderState
            if ← recorderStateProgressed recorderSaved after then
              emitStructural (.congruence invocationOrdinal
                (.userAttemptFailed c.theoremName c.priority c.hypothesesPos
                  attempt.theoremFingerprint attempt.matchEnvelope attempt.premises))
              recordBranch "struct.congruence.userAttemptFailed"
            else
              restoreRecorderState recorderSaved
        | some r =>
            emitStructural (.congruence invocationOrdinal
              (.user c.theoremName c.priority c.hypothesesPos
                attempt.theoremFingerprint attempt.matchEnvelope attempt.premises))
            recordBranch "struct.congruence.user"
            return r
    congrDefault e invocationOrdinal
  else
    congrDefault e invocationOrdinal

def simpApp (e : Expr) : EngineM Result := do
  if isOfNatNatLit e || isOfScientificLit e || isCharLit e then
    -- Recall that we fold "orphan" kernel Nat literals `n` into `OfNat.ofNat n`
    return { expr := e }
  else
    congr e

def simpStep (e : Expr) (simpStepOrdinal : Nat) : EngineM Result := do
  match e with
  | .mdata m e   =>
      recordBranch "struct.metadataBody"
      let r ← withPath .metadataBody <| simp e
      return { r with expr := mkMData m r.expr }
  | .proj ..     => simpProj e
  | .app ..      => simpApp e
  | .lam ..      => simpLambda e
  | .forallE ..  => simpForall e
  | .letE ..     => simpLet e
  | .const ..    => simpConst e
  | .bvar ..     => unreachable!
  | .sort ..     => return { expr := e }
  | .lit ..      => return { expr := e }
  | .mvar ..     =>
    let output ← instantiateMVars e
    if output == e then
      emitStructural (.unassignedMVarStop simpStepOrdinal)
      recordBranch "struct.unassignedMVarStop"
    else
      commitReduction "reduce.simpStep.instantiateMVars" e output .instantiateMVars
    return { expr := output }
  | .fvar ..     => return { expr := (← reduceFVar (← getConfig) (← getSimpTheorems) e) }

def cacheResult (e : Expr) (cfg : Config) (r : Result) : EngineM Result := do
  if cfg.memoize && r.cache then
    let runtime ← getRuntime
    modify fun s => { s with cache := s.cache.insert e r }
    if runtime.mode != .reference then
      let path := (← getRecorderState).path
      runtime.cacheProvenance.modify fun provenance => {
        provenance with
          simpSources := provenance.simpSources.insert e
            (path, provenance.simpOrder.size)
          simpOrder := provenance.simpOrder.push path
      }
  return r

partial def simpLoop (e : Expr) : EngineM Result := withIncRecDepth do
  let cfg ← getConfig
  let runtime ← getRuntime
  if cfg.memoize then
    let cache := (← get).cache
    if runtime.mode == .replay then
      if let some expected ← peekReplayStructural? then
        if ← isCurrentReplayStructural expected then
          if let .cacheHit sourcePath sourceIndex := expected.witness then
            let state ← getRecorderState
            let provenance ← runtime.cacheProvenance.get
            let some actualPath := provenance.simpOrder[sourceIndex]?
              | throwError "replay_expected_simp_cache_hit: source={repr sourcePath}, path={repr state.path}, cached={provenance.simpOrder.size}"
            unless actualPath == sourcePath do
              throwError "replay_simp_cache_source_mismatch: expectedPath={repr sourcePath}, actualPath={repr actualPath}, index={sourceIndex}"
            let some cachedResult := cache.find? e
              | throwError "replay_simp_cache_miss: source={repr sourcePath}, index={sourceIndex}"
            unless provenance.simpSources.find? e == some (sourcePath, sourceIndex) do
              throwError "replay_simp_cache_provenance_mismatch: source={repr sourcePath}, index={sourceIndex}"
            emitStructural (.cacheHit sourcePath sourceIndex)
            return cachedResult
    else if let some result := cache.find? e then
      if runtime.mode == .record then
        let state ← getRecorderState
        let provenance ← runtime.cacheProvenance.get
        match provenance.simpSources.find? e with
        | some (sourcePath, sourceIndex) =>
            recordBranch "struct.cacheHit"
            emitStructural (.cacheHit sourcePath sourceIndex)
        | none =>
            let observations ← runtime.observations.get
            unless deferredBySimproc observations.deferred do
              throwError "record_simp_cache_source_missing: path={repr state.path}, input={e}, cacheEntries={cache.toList.length}, sourceEntries={provenance.simpSources.toList.length}"
            recordBranch "boundary.simprocOpaqueCache"
      return result
  if (← get).numSteps > cfg.maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
  else
    checkSystem "simp"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    let pathOrdinal ← nextPathInvocationOrdinal
    match (← withPath (.preVisit pathOrdinal) <| withPhase .pre <|
        recordPhaseStep e <| pre e) with
    | .done r  => cacheResult e cfg r
    | .visit r => cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    | .continue none => visitPreContinue cfg { expr := e }
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Config) (r : Result) : EngineM Result := do
    let pathOrdinal ← nextPathInvocationOrdinal
    let eNew ← withPath (.reductionVisit pathOrdinal) <| reduceStep r.expr
    if eNew != r.expr then
      trace[Debug.Meta.Tactic.simp] "reduceStep (pre) {e} => {eNew}"
      let r := { r with expr := eNew }
      cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    else
      let runtime ← getRuntime
      let simpStepOrdinal := (← getRecorderState).simpStepOrdinal
      if runtime.mode != .reference then
        modifyRecorderState fun state => { state with simpStepOrdinal := state.simpStepOrdinal + 1 }
      if runtime.mode == .replay then
        if let some expected ← peekReplayStructural? then
          if ← isCurrentReplayStructural expected then
            if let .unassignedMVarStop expectedOrdinal := expected.witness then
              if expectedOrdinal == simpStepOrdinal then
                emitStructural (.unassignedMVarStop simpStepOrdinal)
                return ← visitPost cfg r
      let r ← r.mkEqTrans (← simpStep r.expr simpStepOrdinal)
      visitPost cfg r
  visitPost (cfg : Config) (r : Result) : EngineM Result := do
    match (← withPhase .post <| recordPhaseStep r.expr <| post r.expr) with
    | .done r' => cacheResult e cfg (← r.mkEqTrans r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkEqTrans r')
  visitPostContinue (cfg : Config) (r : Result) : EngineM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      let pathOrdinal ← nextPathInvocationOrdinal
      r ← r.mkEqTrans (← withPath (.postRestart pathOrdinal) <| simpLoop r.expr)
    cacheResult e cfg r

set_option compiler.ignoreBorrowAnnotation true in
@[export explicit_lean_simp_engine]
def simpImpl (e : Expr) : EngineM Result := withIncRecDepth do
  let runtime ← getRuntime
  let invocationOrdinal := (← getRecorderState).simpInvocationOrdinal
  if runtime.mode != .reference then
    modifyRecorderState fun state => {
      state with simpInvocationOrdinal := state.simpInvocationOrdinal + 1 }
  withPath (.simpCall invocationOrdinal) do
    let proofTerm ← isProof e
    if runtime.mode == .replay then
      if let some expected ← peekReplayStructural? then
        if ← isCurrentReplayStructural expected then
          if let .proofSkip expectedOrdinal typeFingerprint := expected.witness then
            if expectedOrdinal == invocationOrdinal then
              unless proofTerm do throwError "replay_expected_proof_skip"
              let actualType ← liftM (exprFingerprintHash (← inferType e))
              unless actualType == typeFingerprint do
                throwError "replay_proof_skip_type_mismatch: expected {typeFingerprint}, got {actualType}"
              emitStructural (.proofSkip invocationOrdinal typeFingerprint)
              return { expr := e }
      if proofTerm then throwError "replay_uncommanded_proof_skip"
    else if proofTerm then
      let typeFingerprint ← liftM (exprFingerprintHash (← inferType e))
      emitStructural (.proofSkip invocationOrdinal typeFingerprint)
      recordBranch "struct.proofSkip"
      return { expr := e }
    trace[Meta.Tactic.simp.heads] "{repr e.toHeadIndex}"
    simpLoop e

@[inline] def withCatchingRuntimeEx (x : EngineM α) : EngineM α := do
  if (← getConfig).catchRuntime then
    tryCatchRuntimeEx x
      fun ex => do
        reportDiag (← get).diag
        if ex.isRuntime then
          throwNestedTacticEx `simp ex
        else
          throw ex
  else
    x

/--
For `rfl` theorems and simprocs, there might not be an explicit reference in the proof term, so
we record (all non-builtin) usages explicitly.
-/
private def recordSimpUses (s : State) : MetaM Unit := do
  for (thm, _) in s.usedTheorems.map do
    if let .decl declName .. := thm then
      if !(← isBuiltinSimproc declName) then
        recordExtraModUseFromDecl (isMeta := false) declName

def mainCore (e : Expr) (ctx : Context) (s : State := {}) (methods : Methods := {}) : MetaM (Result × State) := do
  let (r, s) ← EngineM.run ctx s methods <| withCatchingRuntimeEx <| simp e
  recordSimpUses s
  return (r, s)

private def finishRecording (runtime : Runtime) (finalExpr : Expr) : MetaM Recording := do
  let finalFingerprint ← exprFingerprintHash finalExpr
  runtime.state.modify fun state => {
    state with program.finalFingerprint := finalFingerprint
  }
  let state ← runtime.state.get
  let observations ← runtime.observations.get
  return {
    program := state.program
    deferred := observations.deferred
    simprocs := { observations := observations.simprocs }
    coveredBranches := observations.coveredBranches
  }

def mainCoreRecording (e : Expr) (ctx : Context) (s : State := {})
    (methods : Methods := {}) : MetaM (Result × State × Recording) := do
  let initialFingerprint ← exprFingerprintHash e
  let runtime ← Runtime.record initialFingerprint
  let (result, state) ← EngineM.runWithRuntime runtime ctx s methods <|
    withCatchingRuntimeEx <| simp e
  recordSimpUses state
  return (result, state, ← finishRecording runtime result.expr)

def main (e : Expr) (ctx : Context) (stats : Stats := {}) (methods : Methods := {}) : MetaM (Result × Stats) := do
  let (r, s) ← mainCore e ctx { stats with } methods
  return (r, { s with })

def dsimpMainCore (e : Expr) (ctx : Context) (s : State := {}) (methods : Methods := {}) : MetaM (Expr × State) := do
  let (r, s) ← EngineM.run ctx s methods <| withCatchingRuntimeEx <| dsimp e
  recordSimpUses s
  return (r, s)

def dsimpMainCoreRecording (e : Expr) (ctx : Context) (s : State := {})
    (methods : Methods := {}) : MetaM (Expr × State × Recording) := do
  let runtime ← Runtime.record (← exprFingerprintHash e)
  let (result, state) ← EngineM.runWithRuntime runtime ctx s methods <|
    withCatchingRuntimeEx <| dsimp e
  recordSimpUses state
  return (result, state, ← finishRecording runtime result)

def dsimpMain (e : Expr) (ctx : Context) (stats : Stats := {}) (methods : Methods := {}) : MetaM (Expr × Stats) := do
  let (r, s) ← dsimpMainCore e ctx { stats with } methods
  return (r, { s with })

private def instrumentationSimpArgs? (stx : Syntax) : Option Syntax :=
  match stx.getKind.toString with
  | "Lean.Parser.Tactic.simpEngineReference"
  | "Lean.Parser.Tactic.simpEngineRecording"
  | "Lean.Parser.Tactic.simpEngineObserve"
  | "Lean.Parser.Tactic.simpEngineReplay" => some stx[1]
  | "Lean.Parser.Tactic.simpEngineSourceRecording"
  | "Lean.Parser.Tactic.simpEngineApply" => some stx[3]
  | _ => none

/-- Instrumented nested tactics remain semantically ordinary `simp` calls.
    Canonicalizing their parser wrappers makes explicit theorem origins stable
    between recording and materialized source without re-running ambient simp. -/
private def canonicalRuleSyntax (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun child =>
    if child.getKind == ``Lean.Parser.Tactic.simp then
      mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", child[1], child[2], child[3], child[4], child[5]]
    else
      match instrumentationSimpArgs? child with
      | none => child
      | some args => mkNode ``Lean.Parser.Tactic.simp #[
          mkAtom "simp", args[0], args[1], args[2], args[3], args[4]]

private def canonicalRuleSyntaxSource (stx : Syntax) : String :=
  let canonical := canonicalRuleSyntax stx
  canonical.reprint.getD (toString canonical.prettyPrint)

private def ruleOrigin (origin : Origin) (override? : Option RuleOrigin := none) :
    EngineM (RuleOrigin × String × Bool) := do
  if let some override := override? then
    return match override with
      | .equation declaration index =>
          (override, s!"equation:{declaration}:{index}", false)
      | .decl name => (override, toString name, false)
      | .syntax source => (override, source, false)
      | .local subject => (override, s!"local:{subject.contextIndex}", false)
      | .other name => (override, toString name, false)
  match origin with
  | .decl name _ inverse => return (.decl name, toString name, inverse)
  | .fvar fvarId =>
    let localDecl ← getFVarLocalDecl (.fvar fvarId)
    return (.local (← localRefOfDecl localDecl), s!"local:{localDecl.index}", false)
  | .stx _ ref =>
    let source := canonicalRuleSyntaxSource ref
    return (.syntax source, source, false)
  | .other name => return (.other name, toString name, false)

private def useImplicitDefEqProofRecorded (thm : SimpTheorem) : EngineM Bool := do
  if thm.rfl || (thm.backwardRfl && backward.defeqAttrib.useBackward.get (← getOptions)) then
    return (← getConfig).implicitDefEqProofs
  return false

private def ruleShape (thm : SimpTheorem) : EngineM (String × String) := do
  let saved ← Meta.saveState
  try
    let value ← thm.getValue
    let ruleFingerprint ← liftM (exprFingerprintHash (← inferType value))
    let type ← inferType value
    let (_, _, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    return (ruleFingerprint, ← liftM (exprFingerprintHash lhs))
  finally
    saved.restore

private def exactRuleVariant (preceding : Array SimpTheorem)
    (selected : SimpTheorem) : EngineM Nat := do
  let selectedShape ← ruleShape selected
  let mut ordinal := 0
  for candidate in preceding do
    if candidate.origin == selected.origin && (← ruleShape candidate) == selectedShape then
      ordinal := ordinal + 1
  return ordinal

private def tryTheoremCoreRecorded (lhs : Expr) (xs : Array Expr)
    (bis : Array BinderInfo) (value type e : Expr) (thm : SimpTheorem)
    (numExtraArgs : Nat) (variant : EngineM Nat) (indexMode : Bool)
    (originOverride? : Option RuleOrigin := none) : EngineM (Option Result) := do
  let recorderSaved ← saveRecorderState
  recordTriedSimpTheorem thm.origin
  let mut extraArgs := #[]
  let mut subject := e
  for _ in *...numExtraArgs do
    extraArgs := extraArgs.push subject.appArg!
    subject := subject.appFn!
  extraArgs := extraArgs.reverse
  unless (← withSimpMetaConfig <| isDefEq lhs subject) do
    restoreRecorderState recorderSaved
    return none
  let makeMetadata (proofPresent : Bool) : EngineM (RuleRef × MatchEnvelope) := do
    -- Matching assigns the theorem telescope metavariables. Certificate
    -- identity is the generic theorem shape used for candidate resolution,
    -- not this particular successful instantiation.
    let (ruleFingerprint, lhsFingerprint) ← ruleShape thm
    let (origin, source, inverse) ← ruleOrigin thm.origin originOverride?
    let state ← getRecorderState
    let binderAssignments ← expressionFingerprints xs
    let instanceAssignments ← expressionFingerprints <|
      (xs.zip bis).foldl (init := #[]) fun assignments (x, bi) =>
        if bi.isInstImplicit then assignments.push x else assignments
    return ({
      source
      origin
      inverse
      phase := state.phase
      variant := ← variant
      ruleFingerprint
      lhsFingerprint
      indexMode
    }, {
      binderAssignments
      instanceAssignments
      proofPresent
    })
  let failAttempt (premises : Array PremiseProgram) : EngineM (Option Result) := do
    let after ← getRecorderState
    if ← recorderStateProgressed recorderSaved after then
      let (rule, envelope) ← makeMetadata false
      recordBranch "rewrite.attemptFailed"
      emitEvent e e (.rewriteAttemptFailed rule envelope premises) .continueNone
    else
      restoreRecorderState recorderSaved
    return none
  let synthesis ← synthesizeRecordedArgs thm.origin bis xs
  let premises? := match synthesis with
    | .success premises => some premises
    | .failed _ => none
  let some premises := premises? | do
    let .failed premises := synthesis | unreachable!
    return ← failAttempt premises
  let proof? ← if (← useImplicitDefEqProofRecorded thm) then
    pure none
  else
    let proof ← instantiateMVars (mkAppN value xs)
    if (← hasAssignableMVar proof) then
      return ← failAttempt premises
    pure (some proof)
  let rhs := (← instantiateMVars type).appArg!
  if (← instantiateMVars subject) == rhs then
    return ← failAttempt premises
  if thm.perm then
    let ordered ← acLt rhs subject .reduceSimpleOnly
    unless ordered do return ← failAttempt premises
  let rhs ← if type.hasBinderNameHint then rhs.resolveBinderNameHint else pure rhs
  let mut result : Result := { expr := rhs, proof? }
  if (← hasAssignableMVar result.expr) then
    return ← failAttempt premises
  result ← result.addExtraArgs extraArgs
  recordSimpTheorem thm.origin
  let (rule, envelope) ← makeMetadata result.proof?.isSome
  recordBranch "rewrite.commit"
  emitEvent e result.expr (.rewrite rule envelope premises) .visit
  return some result

private def tryTheoremWithExtraArgsRecorded? (e : Expr) (thm : SimpTheorem)
    (numExtraArgs : Nat) (variant : EngineM Nat) (indexMode : Bool)
    (originOverride? : Option RuleOrigin := none) : EngineM (Option Result) :=
  withNewMCtxDepth do
    let value ← thm.getValue
    let type ← inferType value
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    tryTheoremCoreRecorded lhs xs bis value type e thm numExtraArgs variant indexMode
      originOverride?

private def tryTheoremRecorded? (e : Expr) (thm : SimpTheorem)
    (variant := 0) (indexMode := true)
    (originOverride? : Option RuleOrigin := none) : EngineM (Option Result) := do
  withNewMCtxDepth do
    let value ← thm.getValue
    let type ← inferType value
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    match ← tryTheoremCoreRecorded lhs xs bis value type e thm 0 (pure variant) indexMode
        originOverride? with
    | some result => return some result
    | none =>
      let lhsNumArgs := lhs.getAppNumArgs
      let eNumArgs := e.getAppNumArgs
      if eNumArgs > lhsNumArgs then
        tryTheoremCoreRecorded lhs xs bis value type e thm (eNumArgs - lhsNumArgs) (pure variant)
          indexMode originOverride?
      else
        return none

private def diagnoseWhenNoIndex (e : Expr) (theorems : SimpTheoremTree)
    (thm : SimpTheorem) : EngineM Unit := do
  if (← isDiagnosticsEnabled) then
    let candidates ← withSimpIndexConfig <| theorems.getMatchWithExtra e
    for (candidate, _) in candidates do
      if unsafe ptrEq thm candidate then return
    recordTheoremWithBadKeys thm

private def rewriteRecorded? (e : Expr) (theorems : SimpTheoremTree)
    (erased : PHashSet Origin) (rflOnly : Bool) : EngineM (Option Result) := do
  let indexMode := (← getConfig).index
  let useBackward := backward.defeqAttrib.useBackward.get (← getOptions)
  if indexMode then
    let candidates ← withSimpIndexConfig <| theorems.getMatchWithExtra e
    let candidates := candidates.insertionSort fun lhs rhs => lhs.1.priority > rhs.1.priority
    for h : candidateIndex in *...candidates.size do
      let (thm, numExtraArgs) := candidates[candidateIndex]
      let variant := exactRuleVariant
        ((candidates.extract 0 candidateIndex).map (·.1)) thm
      checkSystem "simp"
      if erased.contains thm.origin then continue
      if rflOnly && !(thm.rfl || (useBackward && thm.backwardRfl)) then continue
      if let some result ← tryTheoremWithExtraArgsRecorded? e thm numExtraArgs variant true then
        return some result
  else
    let (candidates, numArgs) ← withSimpIndexConfig <| theorems.getMatchLiberal e
    let candidates := candidates.insertionSort fun lhs rhs => lhs.priority > rhs.priority
    for h : candidateIndex in *...candidates.size do
      let thm := candidates[candidateIndex]
      let variant := exactRuleVariant (candidates.extract 0 candidateIndex) thm
      checkSystem "simp"
      unless erased.contains thm.origin ||
          (rflOnly && !(thm.rfl || (useBackward && thm.backwardRfl))) do
        let result? ← withNewMCtxDepth do
          let value ← thm.getValue
          let type ← inferType value
          let (xs, bis, type) ← forallMetaTelescopeReducing type
          let type ← whnf (← instantiateMVars type)
          let lhs := type.appFn!.appArg!
          tryTheoremCoreRecorded lhs xs bis value type e thm
            (numArgs - lhs.getAppNumArgs) variant false
        if let some result := result? then
          diagnoseWhenNoIndex e theorems thm
          return some result
  return none

private def phaseIsPost : Phase → Bool
  | .post | .dpost => true
  | .pre | .dpre => false

private def originMatchesRule (expected : RuleOrigin) (actual : Origin) : EngineM Bool := do
  match expected, actual with
  | .decl expectedName, .decl actualName _ _ => return expectedName == actualName
  | .equation declaration index, .decl actualName _ _ =>
      let some equations ← getEqnsFor? declaration | return false
      return equations[index]? == some actualName
  | .local expectedRef, .fvar fvarId =>
      let actualDecl ← getFVarLocalDecl (.fvar fvarId)
      return expectedRef == (← localRefOfDecl actualDecl)
  | .syntax expectedSource, .stx _ stx =>
      let actualSource := canonicalRuleSyntaxSource stx
      return expectedSource == actualSource
  | .other expectedName, .other actualName => return expectedName == actualName
  | _, _ => return false

private def ruleMatches (expected : RuleRef) (thm : SimpTheorem) : EngineM Bool := do
  -- Equation candidates are selected by matcher and equation index in
  -- `candidatesForRule`. Generated matcher names may change when the tactic
  -- head is materialized, so their theorem origin is validated structurally
  -- below instead of against the recording-time private name.
  unless expected.origin matches .equation .. do
    unless ← originMatchesRule expected.origin thm.origin do return false
  let (ruleFingerprint, lhsFingerprint) ← ruleShape thm
  return ruleFingerprint == expected.ruleFingerprint &&
    lhsFingerprint == expected.lhsFingerprint

private def explicitCandidates (e : Expr) (rule : RuleRef) : EngineM (Array SimpTheorem) := do
  let mut result := #[]
  let runtime ← getRuntime
  let sourceContext := runtime.ruleContext.getD (← getContext)
  for theorems in sourceContext.simpTheorems do
    let tree := if phaseIsPost rule.phase then theorems.post else theorems.pre
    if rule.indexMode then
      let candidates ← withSimpIndexConfig <| tree.getMatchWithExtra e
      for (thm, _) in candidates do
        if ← originMatchesRule rule.origin thm.origin then
          result := result.push thm
    else
      let (candidates, _) ← withSimpIndexConfig <| tree.getMatchLiberal e
      for thm in candidates do
        if ← originMatchesRule rule.origin thm.origin then
          result := result.push thm
  return result

private def candidatesForRule (e : Expr) (rule : RuleRef) : EngineM (Array SimpTheorem) := do
  match rule.origin with
  | .decl name =>
      mkSimpTheoremFromConst name (post := phaseIsPost rule.phase) (inv := rule.inverse)
  | .equation declaration index =>
      let equations? ← match e.getAppFn with
        | .const currentMatcher _ =>
            if ← isMatcher currentMatcher then
              pure (some (← Match.getEquationsFor currentMatcher).eqnNames)
            else
              getEqnsFor? declaration
        | _ => getEqnsFor? declaration
      let some equations := equations?
        | throwError "replay_equation_source_missing: {declaration}; currentHead={e.getAppFn}"
      let some equation := equations[index]?
        | throwError "replay_equation_index_missing: {declaration}:{index}"
      mkSimpTheoremFromConst equation (post := phaseIsPost rule.phase)
  | .local subject =>
      let mut found? : Option LocalDecl := none
      for localDecl in (← getLCtx) do
        if localDecl.index == subject.contextIndex then found? := some localDecl
      let some localDecl := found?
        | throwError "replay_local_rule_missing: {subject.contextIndex}"
      let actual ← localRefOfDecl localDecl
      unless actual == subject do
        throwError "replay_local_rule_mismatch: expected {repr subject}, got {repr actual}"
      mkSimpTheoremFromExpr (.fvar localDecl.fvarId) #[] localDecl.toExpr
        (post := phaseIsPost rule.phase)
  | .syntax _ | .other _ => explicitCandidates e rule

private def applyRecordedRule (e : Expr) (rule : RuleRef) : EngineM Result := do
  let candidates ← candidatesForRule e rule
  let mut matchingOrdinal := 0
  for thm in candidates do
    if ← ruleMatches rule thm then
      if matchingOrdinal != rule.variant then
        matchingOrdinal := matchingOrdinal + 1
        continue
      let override? := if rule.origin matches .equation .. then some rule.origin else none
      let some result ← tryTheoremRecorded? e thm rule.variant rule.indexMode override?
        | throwError "replay_recorded_rule_did_not_apply: {rule.source}"
      return result
  throwError "replay_recorded_rule_not_resolved: {rule.source}"

private def applyRecordedRuleAttempt (e : Expr) (rule : RuleRef) : EngineM Unit := do
  let candidates ← candidatesForRule e rule
  let mut matchingOrdinal := 0
  for thm in candidates do
    if ← ruleMatches rule thm then
      if matchingOrdinal != rule.variant then
        matchingOrdinal := matchingOrdinal + 1
        continue
      let cursor := (← getRecorderState).eventCursor
      let override? := if rule.origin matches .equation .. then some rule.origin else none
      if (← tryTheoremRecorded? e thm rule.variant rule.indexMode override?).isSome then
        throwError "replay_expected_failed_rule_attempt: {rule.source}"
      unless (← getRecorderState).eventCursor > cursor do
        throwError "replay_failed_rule_attempt_not_consumed: {rule.source}"
      return
  throwError "replay_recorded_rule_not_resolved: {rule.source}"

private def rewritePreRecorded (rflOnly := false) : Simproc := fun e => do
  for theorems in (← getContext).simpTheorems do
    if let some result ← rewriteRecorded? e theorems.pre theorems.erased rflOnly then
      return .visit result
  return .continue

private def rewritePostRecorded (rflOnly := false) : Simproc := fun e => do
  for theorems in (← getContext).simpTheorems do
    if let some result ← rewriteRecorded? e theorems.post theorems.erased rflOnly then
      return .visit result
  return .continue

private def drewritePreRecorded : DSimproc := fun e => do
  for theorems in (← getContext).simpTheorems do
    if let some result ← rewriteRecorded? e theorems.pre theorems.erased true then
      return .visit result.expr
  return .continue

private def drewritePostRecorded : DSimproc := fun e => do
  for theorems in (← getContext).simpTheorems do
    if let some result ← rewriteRecorded? e theorems.post theorems.erased true then
      return .visit result.expr
  return .continue

private def simprocCoreRecorded (postPhase : Bool) (tree : SimprocTree)
    (erased : PHashSet Name) (input : Expr) : EngineM Step := do
  let candidates ← withSimpIndexConfig <| tree.getMatchWithExtra input
  let mut expression := input
  let mut proof? : Option Expr := none
  let mut found := false
  let mut cache := true
  for (entry, numExtraArgs) in candidates do
    unless erased.contains entry.declName do
      let step ← liftSimpM (entry.try numExtraArgs expression)
      match step with
      | .visit result =>
        recordSimpTheorem (.decl entry.declName postPhase)
        observeSimproc entry.declName expression result.expr .visit false
        return .visit (← mkEqTransOptProofResult proof? cache result)
      | .done result =>
        recordSimpTheorem (.decl entry.declName postPhase)
        observeSimproc entry.declName expression result.expr .done false
        return .done (← mkEqTransOptProofResult proof? cache result)
      | .continue (some result) =>
        recordSimpTheorem (.decl entry.declName postPhase)
        observeSimproc entry.declName expression result.expr .continueSome false
        expression := result.expr
        proof? ← mkEqTrans? proof? result.proof?
        cache := cache && result.cache
        found := true
      | .continue none =>
        observeSimproc entry.declName expression expression .continueNone false
  if found then return .continue (some { expr := expression, proof?, cache })
  return .continue

private def dsimprocCoreRecorded (postPhase : Bool) (tree : SimprocTree)
    (erased : PHashSet Name) (input : Expr) : EngineM DStep := do
  let candidates ← withSimpIndexConfig <| tree.getMatchWithExtra input
  let mut expression := input
  let mut found := false
  for (entry, numExtraArgs) in candidates do
    unless erased.contains entry.declName do
      let step ← liftSimpM (entry.tryD numExtraArgs expression)
      match step with
      | .visit output =>
        recordSimpTheorem (.decl entry.declName postPhase)
        observeSimproc entry.declName expression output .visit true
        return .visit output
      | .done output =>
        recordSimpTheorem (.decl entry.declName postPhase)
        observeSimproc entry.declName expression output .done true
        return .done output
      | .continue (some output) =>
        recordSimpTheorem (.decl entry.declName postPhase)
        observeSimproc entry.declName expression output .continueSome true
        expression := output
        found := true
      | .continue none =>
        observeSimproc entry.declName expression expression .continueNone true
  if found then return .continue (some expression)
  return .continue

private def simprocArrayRecorded (postPhase : Bool) (sets : SimprocsArray)
    (input : Expr) : EngineM Step := do
  let mut found := false
  let mut expression := input
  let mut proof? : Option Expr := none
  let mut cache := true
  for set in sets do
    match ← simprocCoreRecorded postPhase (if postPhase then set.post else set.pre)
        set.erased expression with
    | .visit result => return .visit (← mkEqTransOptProofResult proof? cache result)
    | .done result => return .done (← mkEqTransOptProofResult proof? cache result)
    | .continue none => pure ()
    | .continue (some result) =>
      expression := result.expr
      proof? ← mkEqTrans? proof? result.proof?
      cache := cache && result.cache
      found := true
  if found then return .continue (some { expr := expression, proof?, cache })
  return .continue

private def dsimprocArrayRecorded (postPhase : Bool) (sets : SimprocsArray)
    (input : Expr) : EngineM DStep := do
  let mut found := false
  let mut expression := input
  for set in sets do
    match ← dsimprocCoreRecorded postPhase (if postPhase then set.post else set.pre)
        set.erased expression with
    | .visit output => return .visit output
    | .done output => return .done output
    | .continue none => pure ()
    | .continue (some output) => expression := output; found := true
  if found then return .continue (some expression)
  return .continue

private def userPreSimprocsRecorded (sets : SimprocsArray) : Simproc := fun e => do
  unless simprocs.get (← getOptions) do return .continue
  simprocArrayRecorded false sets e

private def userPostSimprocsRecorded (sets : SimprocsArray) : Simproc := fun e => do
  unless simprocs.get (← getOptions) do return .continue
  simprocArrayRecorded true sets e

private def userPreDSimprocsRecorded (sets : SimprocsArray) : DSimproc := fun e => do
  unless simprocs.get (← getOptions) do return .continue
  dsimprocArrayRecorded false sets e

private def userPostDSimprocsRecorded (sets : SimprocsArray) : DSimproc := fun e => do
  unless simprocs.get (← getOptions) do return .continue
  dsimprocArrayRecorded true sets e

private def dpreDefaultRecorded (sets : SimprocsArray) : DSimproc :=
  drewritePreRecorded >> userPreDSimprocsRecorded sets

private def dpostDefaultRecorded (sets : SimprocsArray) : DSimproc :=
  drewritePostRecorded >> userPostDSimprocsRecorded sets

private def emitBuiltin (branch : String) (input output : Expr) (builtin : Builtin)
    (disposition : StepDisposition) : EngineM Unit := do
  if input != output then
    recordBranch branch
    emitEvent input output (.builtin builtin) disposition

private def simpUsingDecideRecorded : Simproc := fun e => do
  unless (← getConfig).decide do return .continue
  if e.hasFVar || e.hasMVar || e.isTrue || e.isFalse then return .continue
  try
    let decision ← mkDecide e
    let result ← withDefault <| whnf decision
    if result.isConstOf ``true then
      let output := mkConst ``True
      emitBuiltin "builtin.decideTrue" e output .decideTrue .done
      return .done {
        expr := output
        proof? := mkAppN (mkConst ``eq_true_of_decide)
          #[e, decision.appArg!, (← mkEqRefl (mkConst ``true))]
      }
    if result.isConstOf ``false then
      let output := mkConst ``False
      emitBuiltin "builtin.decideFalse" e output .decideFalse .done
      return .done {
        expr := output
        proof? := mkAppN (mkConst ``eq_false_of_decide)
          #[e, decision.appArg!, (← mkEqRefl (mkConst ``false))]
      }
    return .continue
  catch _ => return .continue

private partial def natConstraintHandler (e : Expr) : ArithHandler :=
  if let some argument := e.not? then
    natConstraintHandler argument
  else if e.isEq || e.isAppOf ``Ne then
    .natEquality
  else
    .natRelation

private def divisibilityHandler (e : Expr) : ArithHandler :=
  match_expr e with
  | Dvd.dvd type _ _ _ => if type.isConstOf ``Nat then .natDivisibility else .intDivisibility
  | _ => .intDivisibility

private def simpArithRecorded (e : Expr) : EngineM Step := do
  unless (← getConfig).arith do return .continue
  if Arith.isLinearCnstr e then
    if let some (output, proof) ← Arith.Nat.simpCnstr? e then
      let handler := natConstraintHandler e
      emitBuiltin s!"builtin.arith.{repr handler}" e output (.arith handler) .visit
      return .visit { expr := output, proof? := proof }
    if let some (output, proof) ← Arith.Int.simpRel? e then
      emitBuiltin "builtin.arith.intRelation" e output (.arith .intRelation) .visit
      return .visit { expr := output, proof? := proof }
    if let some (output, proof) ← Arith.Int.simpEq? e then
      emitBuiltin "builtin.arith.intEquality" e output (.arith .intEquality) .visit
      return .visit { expr := output, proof? := proof }
    return .continue
  if let some type := Arith.isLinearTerm? e then
    if Arith.parentIsTarget (← getContext).parent? then
      return .continue (some { expr := e, cache := false })
    match_expr type with
    | Nat =>
      let some (output, proof) ← Arith.Nat.simpExpr? e | pure ()
      emitBuiltin "builtin.arith.natExpression" e output (.arith .natExpression) .visit
      return .visit { expr := output, proof? := proof }
    | Int =>
      let some (output, proof) ← Arith.Int.simpExpr? e | pure ()
      emitBuiltin "builtin.arith.intExpression" e output (.arith .intExpression) .visit
      return .visit { expr := output, proof? := proof }
    | _ => return .continue
  if Arith.isDvdCnstr e then
    let some (output, proof) ← Arith.Int.simpDvd? e | pure ()
    let handler := divisibilityHandler e
    emitBuiltin s!"builtin.arith.{repr handler}" e output (.arith handler) .visit
    return .visit { expr := output, proof? := proof }
  return .continue

def simpMatchDiscrs? (info : MatcherInfo) (e : Expr) : EngineM (Option Result) := do
  let recorderSaved ← saveRecorderState
  let numArgs := e.getAppNumArgs
  if numArgs < info.arity then
    return none
  let prefixSize := info.numParams + 1 /- motive -/
  let n     := numArgs - prefixSize
  let f     := e.stripArgsN n
  let infos := (← getFunInfoNArgs f n).paramInfo
  let args  := e.getAppArgsN n
  let mut r : Result := { expr := f }
  let mut modified := false
  emitStructural (.matchDiscriminants info.numDiscrs)
  recordBranch "struct.matchDiscriminants"
  let attemptBaseline ← saveRecorderState
  for i in *...info.numDiscrs do
    let arg := args[i]!
    if i < infos.size && !infos[i]!.hasFwdDeps then
      let argNew ← withPath (.matchDiscriminant i .simp) <| simp arg
      if argNew.expr != arg then modified := true
      r ← mkCongr r argNew
    else if (← whnfD (← inferType r.expr)).isArrow then
      let argNew ← withPath (.matchDiscriminant i .simp) <| simp arg
      if argNew.expr != arg then modified := true
      r ← mkCongr r argNew
    else
      let argNew ← withPath (.matchDiscriminant i .dsimp) <| dsimp arg
      if argNew != arg then modified := true
      r ← mkCongrFun r argNew
  unless modified do
    let after ← getRecorderState
    if ← recorderStateProgressed attemptBaseline after then
      emitStructural (.matchDiscriminantsAttemptFailed info.numDiscrs)
      recordBranch "struct.matchDiscriminantsAttemptFailed"
    else
      restoreRecorderState recorderSaved
    return none
  for h : i in info.numDiscrs...args.size do
    let arg := args[i]
    r ← mkCongrFun r arg
  return some r

def simpMatchCore (matcherName : Name) (e : Expr) : EngineM Step := do
  let equations := (← Match.getEquationsFor matcherName).eqnNames
  for h : equationIndex in *...equations.size do
    let matchEq := equations[equationIndex]
    -- Try lemma
    match (← withReducible <| tryTheoremRecorded? e {
        origin := .decl matchEq
        proof := mkConst matchEq
        rfl := (← isRflTheorem matchEq)
        backwardRfl := (← isBackwardRflTheorem matchEq)
      } 0 (originOverride? := some (.equation matcherName equationIndex))) with
    | none   => pure ()
    | some r => return .visit r
  return .continue

def simpMatch : Simproc := fun e => do
  unless (← getConfig).iota do
    return .continue
  if let some eNew ← withSimpMetaConfig <| reduceRecMatcher? e then
    commitReduction "reduce.matchIota" e eNew .iota .visit
    return .visit { expr := eNew }
  let .const declName _ := e.getAppFn
    | return .continue
  let some info ← getMatcherInfo? declName
    | return .continue
  if let some r ← simpMatchDiscrs? info e then
    return .visit r
  simpMatchCore declName e

/--
Discharge procedure for the ground/symbolic evaluator.
-/
def dischargeGround (e : Expr) : EngineM (Option Expr) := do
  let r ← simp e
  if r.expr.isTrue then
    try
      setPremiseTerminal .isTrue
      setProgramFinal r.expr
      return some (← mkOfEqTrue (← r.getProof))
    catch _ =>
      return none
  else
    return none

/--
Try to unfold ground term in the ground/symbolic evaluator.
-/
def sevalGround : Simproc := fun e => do
  -- `e` is not a ground term.
  unless !e.hasExprMVar && !e.hasFVar do return .continue
  -- Check whether `e` is a constant application
  let f := e.getAppFn
  let .const declName lvls := f | return .continue
  -- If declaration has been marked to not be unfolded, return none.
  let ctx ← getContext
  if ctx.simpTheorems.isErased (.decl declName) then return .continue
  -- Matcher applications should have been reduced before we get here.
  if (← isMatcher declName) then return .continue
  if let some eqns ← withDefault <| getEqnsFor? declName then
    -- `declName` has equation theorems associated with it.
    for h : equationIndex in *...eqns.size do
      let eqn := eqns[equationIndex]
      -- TODO: cache SimpTheorem to avoid calls to `isRflTheorem`
      if let some result ← tryTheoremRecorded? e {
          origin := .decl eqn
          proof := mkConst eqn
          rfl := (← isRflTheorem eqn)
          backwardRfl := (← isBackwardRflTheorem eqn)
        } 0 (originOverride? := some (.equation declName equationIndex)) then
        trace[Meta.Tactic.simp.ground] "unfolded, {e} => {result.expr}"
        return .visit result
    return .continue
  -- `declName` does not have equation theorems associated with it.
  if e.isConst then
    -- We don't unfold constants that take arguments
    if let .forallE .. ← whnfD (← inferType e) then
      return .continue
  let info ← getConstInfo declName
  unless info.hasValue && info.levelParams.length == lvls.length do return .continue
  let fBody ← instantiateValueLevelParams info lvls
  let eNew := fBody.betaRev e.getAppRevArgs (useZeta := true)
  trace[Meta.Tactic.simp.ground] "delta, {e} => {eNew}"
  commitReduction "ground.delta" e eNew (.delta declName .ground) .visit
  return .visit { expr := eNew }

partial def preSEval (s : SimprocsArray) : Simproc :=
  rewritePreRecorded >>
  simpMatch >>
  userPreSimprocsRecorded s

def postSEval (s : SimprocsArray) : Simproc :=
  rewritePostRecorded >>
  userPostSimprocsRecorded s >>
  sevalGround

def mkSEvalMethods : CoreM Methods := do
  let s ← getSEvalSimprocs
  let base ← Simp.mkSEvalMethods
  return {
    pre        := preSEval #[s]
    post       := postSEval #[s]
    dpre       := dpreDefaultRecorded #[s]
    dpost      := dpostDefaultRecorded #[s]
    discharge? := dischargeGround
    wellBehavedDischarge := true
    base
  }

def mkSEvalContext : MetaM Context := do
  let s ← getSEvalTheorems
  let c ← Meta.getSimpCongrTheorems
  mkContext
    (simpTheorems := #[s])
    (congrTheorems := c)
    (config := { ground := true })

/--
Invoke ground/symbolic evaluator from `simp`.
It uses the `seval` theorems and simprocs.
-/
def seval (e : Expr) : EngineM Result := do
  let m ← mkSEvalMethods
  let ctx ← mkSEvalContext
  let usedTheoremsSaved := (← get).usedTheorems
  try
    withFreshCache do
      withReader (fun _ => m.toMethodsRef) do
      withTheReader Simp.Context (fun _ => ctx) do
      modify fun s => { s with usedTheorems := {} }
      recordBranch "struct.ground"
      withPath .ground <| simp e
  finally
    modify fun s => { s with usedTheorems := usedTheoremsSaved }

/--
Try to unfold ground term in the ground/symbolic evaluator.
-/
def simpGround : Simproc := fun e => do
  -- Ground term unfolding is disabled.
  unless (← getConfig).ground do return .continue
  -- `e` is not a ground term.
  unless !e.hasExprMVar && !e.hasFVar do return .continue
  -- Check whether `e` is a constant application
  let f := e.getAppFn
  let .const declName _ := f | return .continue
  -- If declaration has been marked to not be unfolded, return none.
  let ctx ← getContext
  if ctx.simpTheorems.isErased (.decl declName) then return .continue
  -- Matcher applications should have been reduced before we get here.
  if (← isMatcher declName) then return .continue
  let r ← withTraceNode `Meta.Tactic.simp.ground (fun
      | .ok r => return m!"seval: {e} => {r.expr}"
      | .error err => return m!"seval: {e} => {err.toMessageData}") do
    seval e
  return .done r

def preDefault (s : SimprocsArray) : Simproc :=
  rewritePreRecorded >>
  simpMatch >>
  userPreSimprocsRecorded s >>
  simpUsingDecideRecorded

def postDefault (s : SimprocsArray) : Simproc :=
  rewritePostRecorded >>
  userPostSimprocsRecorded s >>
  simpGround >>
  simpArithRecorded >>
  simpUsingDecideRecorded

partial def isEqnThmHypothesis (e : Expr) : Bool :=
  e.isForall && go e
where
  go (e : Expr) : Bool :=
    match e with
    | .forallE _ d b _ => (d.isEq || d.isHEq || b.hasLooseBVar 0) && go b
    | _ => e.isFalse

private def dischargeUsingAssumption? (e : Expr) : EngineM (Option Expr) := do
  let lctxInitIndices := (← readThe Simp.Context).lctxInitIndices
  let contextual := (← getConfig).contextual
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    -- The following test is needed to ensure `dischargeUsingAssumption?` is a
    -- well-behaved discharger. See comment at `Methods.wellBehavedDischarge`
    else if !contextual && localDecl.index >= lctxInitIndices then
      return none
    else if (← withSimpMetaConfig <| isDefEq e localDecl.type) then
      setPremiseTerminal (.localAssumption localDecl.index)
      return some localDecl.toExpr
    else
      return none

/--
  Tries to solve `e` using `unifyEq?`.
  It assumes that `isEqnThmHypothesis e` is `true`.
-/
partial def dischargeEqnThmHypothesis? (e : Expr) : MetaM (Option Expr) := do
  assert! isEqnThmHypothesis e
  let mvar ← mkFreshExprSyntheticOpaqueMVar e
  withCanUnfoldPred canUnfoldAtMatcher do
    if let .none ← go? mvar.mvarId! then
      instantiateMVars mvar
    else
      return none
where
  go? (mvarId : MVarId) : MetaM (Option MVarId) :=
    try
      let (fvarId, mvarId) ← mvarId.intro1
      mvarId.withContext do
        let localDecl ← fvarId.getDecl
        if localDecl.type.isEq || localDecl.type.isHEq then
          if let some { mvarId, .. } ← unifyEq? mvarId fvarId {} then
            go? mvarId
          else
            return none
        else
          go? mvarId
    catch _  =>
      return some mvarId

/--
Discharges assumptions of the form `∀ …, a = b` using `rfl`. This is particularly useful for higher
order assumptions of the form `∀ …, e = ?g x y` to instantiate a parameter `g` even if that does not
appear on the lhs of the rule.
-/
def dischargeRfl (e : Expr) : EngineM (Option Expr) := do
  forallTelescope e fun xs e => do
    let some (t, a, b) := e.eq? | return .none
    unless a.getAppFn.isMVar || b.getAppFn.isMVar do return .none
    if (← withSimpMetaConfig <| isDefEq a b) then
      trace[Meta.Tactic.simp.discharge] "Discharging with rfl: {e}"
      let u ← getLevel t
      let proof := mkApp2 (.const ``rfl [u]) t a
      let proof ← mkLambdaFVars xs proof
      return .some proof
    return .none


def dischargeDefault? (e : Expr) : EngineM (Option Expr) := do
  let e := e.cleanupAnnotations
  if isEqnThmHypothesis e then
    if let some r ← dischargeUsingAssumption? e then return some r
    if let some r ← dischargeEqnThmHypothesis? e then
      setPremiseTerminal .equationHypothesis
      return some r
  let r ← simp e
  if let some p ← dischargeRfl r.expr then
    setPremiseTerminal .dischargeRfl
    setProgramFinal r.expr
    return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) e r.expr (← r.getProof) p)
  else if r.expr.isTrue then
    setPremiseTerminal .isTrue
    setProgramFinal r.expr
    return some (← mkOfEqTrue (← r.getProof))
  else
    setPremiseTerminal .failed
    setProgramFinal r.expr
    return none

private def resultStep (result : Result) : StepDisposition → EngineM Step
  | .done => return .done result
  | .visit => return .visit result
  | .continueSome => return .continue (some result)
  | .continueNone => throwError "replay_invalid_changing_continue_none"

private def expressionStep (output : Expr) : StepDisposition → EngineM DStep
  | .done => return .done output
  | .visit => return .visit output
  | .continueSome => return .continue (some output)
  | .continueNone => throwError "replay_invalid_changing_continue_none"

private def assertReplayEventInput (e : Expr) (expected : Event) : EngineM Unit := do
  let actual ← liftM (exprFingerprintHash e)
  unless actual == expected.inputFingerprint do
    throwError "replay_event_input_mismatch: expected {expected.inputFingerprint}, got {actual}; input={e}; operation={repr expected.operation}"

private def executeRecordedDecide (e : Expr) (expected : Builtin) : EngineM Result := do
  unless (← getConfig).decide && !e.hasFVar && !e.hasMVar && !e.isTrue && !e.isFalse do
    throwError "replay_decide_ineligible"
  let decision ← mkDecide e
  let value ← withDefault <| whnf decision
  match expected with
  | .decideTrue =>
      unless value.isConstOf ``true do throwError "replay_decide_true_failed"
      return {
        expr := mkConst ``True
        proof? := mkAppN (mkConst ``eq_true_of_decide)
          #[e, decision.appArg!, (← mkEqRefl (mkConst ``true))]
      }
  | .decideFalse =>
      unless value.isConstOf ``false do throwError "replay_decide_false_failed"
      return {
        expr := mkConst ``False
        proof? := mkAppN (mkConst ``eq_false_of_decide)
          #[e, decision.appArg!, (← mkEqRefl (mkConst ``false))]
      }
  | .arith _ => throwError "replay_expected_arithmetic_builtin"

private def executeRecordedArith (e : Expr) (handler : ArithHandler) : EngineM Result := do
  unless (← getConfig).arith do throwError "replay_arithmetic_ineligible"
  let selected? ← if Arith.isLinearCnstr e then
    if let some (output, proof) ← Arith.Nat.simpCnstr? e then
      pure <| some (natConstraintHandler e, output, proof)
    else if let some (output, proof) ← Arith.Int.simpRel? e then
      pure <| some (.intRelation, output, proof)
    else if let some (output, proof) ← Arith.Int.simpEq? e then
      pure <| some (.intEquality, output, proof)
    else
      pure none
  else if let some type := Arith.isLinearTerm? e then
    if Arith.parentIsTarget (← getContext).parent? then
      throwError "replay_arithmetic_parent_is_target"
    match_expr type with
    | Nat =>
        let result? ← Arith.Nat.simpExpr? e
        pure <| result?.map fun (output, proof) => (.natExpression, output, proof)
    | Int =>
        let result? ← Arith.Int.simpExpr? e
        pure <| result?.map fun (output, proof) => (.intExpression, output, proof)
    | _ => pure none
  else if Arith.isDvdCnstr e then
    let result? ← Arith.Int.simpDvd? e
    pure <| result?.map fun (output, proof) => (divisibilityHandler e, output, proof)
  else
    pure none
  let some (selected, output, proof) := selected?
    | throwError "replay_arithmetic_failed: {repr handler}"
  unless selected == handler do
    throwError "replay_arithmetic_handler_mismatch: expected {repr handler}, got {repr selected}"
  return { expr := output, proof? := proof }

private def executeRecordedBuiltin (e : Expr) : Builtin → EngineM Result
  | builtin@(.decideTrue) => executeRecordedDecide e builtin
  | builtin@(.decideFalse) => executeRecordedDecide e builtin
  | .arith handler => executeRecordedArith e handler

private def validateBuiltinDisposition (builtin : Builtin)
    (disposition : StepDisposition) : EngineM Unit := do
  let valid : Bool := match builtin with
    | .decideTrue | .decideFalse => disposition == .done
    | .arith _ => disposition == .visit
  unless valid do
    throwError "replay_builtin_disposition_mismatch: {repr builtin}, {repr disposition}"

private def pathHasChild (path parent : ExecutionPath) (child : PathStep) : Bool :=
  path.steps.size > parent.steps.size &&
    path.steps.extract 0 parent.steps.size == parent.steps &&
    path.steps[parent.steps.size]? == some child

private def replayHasGroundChild : EngineM Bool := do
  let state ← getRecorderState
  if let some event ← peekReplayEvent? then
    if pathHasChild event.path state.path .ground then return true
  if let some structural ← peekReplayStructural? then
    if pathHasChild structural.path state.path .ground then return true
  return false

private def replayGround (e : Expr) : EngineM Result := do
  let ctx ← mkContext (simpTheorems := {}) (congrTheorems := {})
    (config := { ground := true })
  let usedTheoremsSaved := (← get).usedTheorems
  try
    withFreshCache do
      withTheReader Simp.Context (fun _ => ctx) do
      modify fun state => { state with usedTheorems := {} }
      withPath .ground <| simp e
  finally
    modify fun state => { state with usedTheorems := usedTheoremsSaved }

private def consumeReplayPhaseOutcome (input : Expr)
    (actual? : Option Step := none) : EngineM Step := do
  let state ← getRecorderState
  let some expected := state.program.structural[state.structuralCursor]?
    | throwError "replay_missing_phase_outcome: phase={repr state.phase}, path={repr state.path}"
  unless expected.path == state.path do
    throwError "replay_phase_outcome_path_mismatch: expected {repr expected.path}, got {repr state.path}"
  let .phaseOutcome phase invocationOrdinal disposition outputFingerprint proofPresent :=
      expected.witness
    | throwError "replay_expected_phase_outcome: got {repr expected.witness}"
  unless phase == state.phase && invocationOrdinal == state.currentPhaseInvocationOrdinal do
    throwError "replay_phase_outcome_identity_mismatch"
  let actual ← match actual? with
    | some actual => pure actual
    | none => do
        let inputFingerprint ← liftM (exprFingerprintHash input)
        unless outputFingerprint == inputFingerprint && !proofPresent do
          throwError "replay_phase_outcome_requires_operation: {repr expected.witness}; input={inputFingerprint}"
        pure <| match disposition with
          | .done => .done { expr := input }
          | .visit => .visit { expr := input }
          | .continueNone => .continue none
          | .continueSome => .continue (some { expr := input })
  let (actualDisposition, output, actualProofPresent) := match actual with
    | .done result => (.done, result.expr, result.proof?.isSome)
    | .visit result => (.visit, result.expr, result.proof?.isSome)
    | .continue none => (.continueNone, input, false)
    | .continue (some result) => (.continueSome, result.expr, result.proof?.isSome)
  unless actualDisposition == disposition && actualProofPresent == proofPresent do
    throwError "replay_phase_outcome_shape_mismatch: expected {repr expected.witness}"
  let actualFingerprint ← liftM (exprFingerprintHash output)
  unless actualFingerprint == outputFingerprint do
    throwError "replay_phase_outcome_fingerprint_mismatch: expected {outputFingerprint}, got {actualFingerprint}"
  emitStructural (.phaseOutcome phase invocationOrdinal disposition outputFingerprint proofPresent)
  return actual

private def consumeReplayDPhaseOutcome (input : Expr)
    (actual? : Option DStep := none) : EngineM DStep := do
  let state ← getRecorderState
  let some expected := state.program.structural[state.structuralCursor]?
    | throwError "replay_missing_dphase_outcome: phase={repr state.phase}, path={repr state.path}"
  unless expected.path == state.path do
    throwError "replay_dphase_outcome_path_mismatch: expected {repr expected.path}, got {repr state.path}"
  let .phaseOutcome phase invocationOrdinal disposition outputFingerprint proofPresent :=
      expected.witness
    | throwError "replay_expected_dphase_outcome: got {repr expected.witness}"
  unless phase == state.phase && invocationOrdinal == state.currentPhaseInvocationOrdinal &&
      !proofPresent do
    throwError "replay_dphase_outcome_identity_mismatch"
  let actual ← match actual? with
    | some actual => pure actual
    | none => do
        let inputFingerprint ← liftM (exprFingerprintHash input)
        unless outputFingerprint == inputFingerprint do
          throwError "replay_dphase_outcome_requires_operation: {repr expected.witness}"
        pure <| match disposition with
          | .done => .done input
          | .visit => .visit input
          | .continueNone => .continue none
          | .continueSome => .continue (some input)
  let (actualDisposition, output) := match actual with
    | .done output => (.done, output)
    | .visit output => (.visit, output)
    | .continue none => (.continueNone, input)
    | .continue (some output) => (.continueSome, output)
  unless actualDisposition == disposition do
    throwError "replay_dphase_outcome_shape_mismatch: expected {repr expected.witness}"
  let actualFingerprint ← liftM (exprFingerprintHash output)
  unless actualFingerprint == outputFingerprint do
    throwError "replay_dphase_outcome_fingerprint_mismatch: expected {outputFingerprint}, got {actualFingerprint}"
  emitStructural (.phaseOutcome phase invocationOrdinal disposition outputFingerprint false)
  return actual

private def composePhaseStep (accumulated? : Option Result) (step : Step) : EngineM Step :=
  match accumulated? with
  | none => pure step
  | some accumulated => liftM (mkEqTransResultStep accumulated step)

private def finishAccumulatedPhaseOutcome (origin : Expr)
    (accumulated? : Option Result) : EngineM Step := do
  let some accumulated := accumulated?
    | return ← consumeReplayPhaseOutcome origin
  let some expected ← peekReplayStructural?
    | throwError "replay_missing_accumulated_phase_outcome"
  let .phaseOutcome _ _ disposition _ _ := expected.witness
    | throwError "replay_expected_accumulated_phase_outcome"
  let step : Step ← match disposition with
    | .done => pure (.done accumulated)
    | .visit => pure (.visit accumulated)
    | .continueSome => pure (.continue (some accumulated))
    | .continueNone => throwError "replay_invalid_accumulated_continue_none"
  consumeReplayPhaseOutcome origin (some step)

private partial def replayPhaseStepCore (origin current : Expr)
    (accumulated? : Option Result) : EngineM Step := do
  -- `simpMatch` emits its discriminant marker before it tries the generated
  -- equation theorem.  Events and structural witnesses have separate
  -- cursors, so prefer this enclosing structural operation when both streams
  -- are poised at the same phase path; `simpMatch` will consume the equation
  -- event itself if one succeeds.
  if let some expected ← peekReplayStructural? then
    if ← isCurrentReplayStructural expected then
      match expected.witness with
      | .matchDiscriminants _ | .matchDiscriminantsAttemptFailed _ =>
          let step ← composePhaseStep accumulated? (← simpMatch current)
          match step with
          | .continue none => return ← replayPhaseStepCore origin current accumulated?
          | .continue (some accumulated) =>
              return ← replayPhaseStepCore origin accumulated.expr (some accumulated)
          | step => return ← consumeReplayPhaseOutcome origin (some step)
      | _ => pure ()
  if let some expected ← peekReplayEvent? then
    if ← isCurrentReplayEvent expected then
      assertReplayEventInput current expected
      match expected.operation with
      | .rewrite rule _ _ =>
          let result ← applyRecordedRule current rule
          let step ← composePhaseStep accumulated?
            (← resultStep result expected.stepDisposition)
          match step with
          | .continue none => return ← replayPhaseStepCore origin current accumulated?
          | .continue (some accumulated) =>
              return ← replayPhaseStepCore origin accumulated.expr (some accumulated)
          | step => return ← consumeReplayPhaseOutcome origin (some step)
      | .rewriteAttemptFailed rule _ _ =>
          applyRecordedRuleAttempt current rule
          return ← replayPhaseStepCore origin current accumulated?
      | .reduce reduction =>
          validateReductionDisposition reduction expected.stepDisposition
          let some output ← executeRecordedReduction current reduction
            | throwError "replay_phase_reduction_failed: {repr reduction}"
          emitEvent current output (.reduce reduction) expected.stepDisposition
          let step ← composePhaseStep accumulated?
            (← resultStep { expr := output } expected.stepDisposition)
          match step with
          | .continue none => return ← replayPhaseStepCore origin current accumulated?
          | .continue (some accumulated) =>
              return ← replayPhaseStepCore origin accumulated.expr (some accumulated)
          | step => return ← consumeReplayPhaseOutcome origin (some step)
      | .builtin builtin =>
          validateBuiltinDisposition builtin expected.stepDisposition
          let result ← executeRecordedBuiltin current builtin
          emitEvent current result.expr (.builtin builtin) expected.stepDisposition
          let step ← composePhaseStep accumulated?
            (← resultStep result expected.stepDisposition)
          match step with
          | .continue none => return ← replayPhaseStepCore origin current accumulated?
          | .continue (some accumulated) =>
              return ← replayPhaseStepCore origin accumulated.expr (some accumulated)
          | step => return ← consumeReplayPhaseOutcome origin (some step)
  if let some expected ← peekReplayStructural? then
    if ← isCurrentReplayStructural expected then
      match expected.witness with
      | .phaseOutcome .. =>
          return ← finishAccumulatedPhaseOutcome origin accumulated?
      | _ => pure ()
  if ← replayHasGroundChild then
    let result ← replayGround current
    let step ← composePhaseStep accumulated? (.done result)
    return ← consumeReplayPhaseOutcome origin (some step)
  let state ← getRecorderState
  throwError "replay_missing_phase_operation_or_outcome: phase={repr state.phase}, path={repr state.path}, eventCursor={state.eventCursor}/{state.program.events.size}, nextEvent={repr state.program.events[state.eventCursor]?}, structuralCursor={state.structuralCursor}/{state.program.structural.size}, nextStructural={repr state.program.structural[state.structuralCursor]?}"

private partial def replayDPhaseStepCore (origin current : Expr)
    (hasAccumulated : Bool) : EngineM DStep := do
  if let some expected ← peekReplayEvent? then
    if ← isCurrentReplayEvent expected then
      assertReplayEventInput current expected
      match expected.operation with
      | .rewrite rule _ _ =>
          let result ← applyRecordedRule current rule
          let step ← expressionStep result.expr expected.stepDisposition
          match step with
          | .continue none => return ← replayDPhaseStepCore origin current hasAccumulated
          | .continue (some output) => return ← replayDPhaseStepCore origin output true
          | step => return ← consumeReplayDPhaseOutcome origin (some step)
      | .rewriteAttemptFailed rule _ _ =>
          applyRecordedRuleAttempt current rule
          return ← replayDPhaseStepCore origin current hasAccumulated
      | .reduce reduction =>
          validateReductionDisposition reduction expected.stepDisposition
          let some output ← executeRecordedReduction current reduction
            | throwError "replay_dphase_reduction_failed: {repr reduction}"
          emitEvent current output (.reduce reduction) expected.stepDisposition
          let step ← expressionStep output expected.stepDisposition
          match step with
          | .continue none => return ← replayDPhaseStepCore origin current hasAccumulated
          | .continue (some output) => return ← replayDPhaseStepCore origin output true
          | step => return ← consumeReplayDPhaseOutcome origin (some step)
      | .builtin builtin =>
          throwError "replay_builtin_in_dsimp_phase: {repr builtin}"
  if hasAccumulated then
    let some expected ← peekReplayStructural?
      | throwError "replay_missing_accumulated_dphase_outcome"
    if let .phaseOutcome _ _ .continueNone _ _ := expected.witness then
      throwError "replay_invalid_accumulated_dcontinue_none"
  return ← consumeReplayDPhaseOutcome current

private def replayPhaseStep (e : Expr) : EngineM Step :=
  replayPhaseStepCore e e none

private def replayDPhaseStep (e : Expr) : EngineM DStep :=
  replayDPhaseStepCore e e false

private def replayDischarge? (e : Expr) : EngineM (Option Expr) := do
  let some terminal := (← getRecorderState).expectedPremiseTerminal
    | throwError "replay_missing_expected_premise_terminal"
  match terminal with
  | .localAssumption contextIndex =>
      for localDecl in (← getLCtx) do
        if localDecl.index == contextIndex &&
            (← withSimpMetaConfig <| isDefEq e localDecl.type) then
          setPremiseTerminal terminal
          return some localDecl.toExpr
      throwError "replay_local_premise_missing: {contextIndex}"
  | .equationHypothesis =>
      let some proof ← dischargeEqnThmHypothesis? e
        | throwError "replay_equation_premise_failed"
      setPremiseTerminal terminal
      return some proof
  | .dischargeRfl =>
      let result ← simp e
      let some proof ← dischargeRfl result.expr
        | throwError "replay_rfl_premise_failed"
      setPremiseTerminal terminal
      setProgramFinal result.expr
      return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) e result.expr
        (← result.getProof) proof)
  | .isTrue =>
      let result ← simp e
      unless result.expr.isTrue do throwError "replay_true_premise_failed"
      setPremiseTerminal terminal
      setProgramFinal result.expr
      return some (← mkOfEqTrue (← result.getProof))
  | .failed =>
      let result ← simp e
      if result.expr.isTrue || (← dischargeRfl result.expr).isSome then
        throwError "replay_expected_failed_premise"
      setPremiseTerminal terminal
      setProgramFinal result.expr
      return none

private def replayMethods : Methods := {
  pre := replayPhaseStep
  post := replayPhaseStep
  dpre := replayDPhaseStep
  dpost := replayDPhaseStep
  discharge? := replayDischarge?
  wellBehavedDischarge := true
  customDischarger := false
  base := {}
}

private def closedReplayContext (ctx : Context) : MetaM Context :=
  mkContext (config := ctx.config) (simpTheorems := {})
    (congrTheorems := {}) (userConfig := ctx.userConfig)

private def finishReplay (runtime : Runtime) (result : Expr) : MetaM Unit := do
  let state ← runtime.state.get
  assertReplayProgramConsumed state
  let finalFingerprint ← exprFingerprintHash result
  unless state.program.finalFingerprint == finalFingerprint do
    throwError "replay_final_fingerprint_mismatch: expected {state.program.finalFingerprint}, got {finalFingerprint}"

def mainCoreReplay (e : Expr) (sourceCtx : Context) (config : ReplayConfig)
    (program : Program) (s : State := {}) : MetaM (Result × State) := do
  let actualConfig ← replayConfigOfContext sourceCtx
  unless actualConfig == config do throwError "replay_configuration_mismatch"
  let initialFingerprint ← exprFingerprintHash e
  unless initialFingerprint == program.initialFingerprint do
    throwError "replay_initial_fingerprint_mismatch: expected {program.initialFingerprint}, got {initialFingerprint}"
  let runtime ← Runtime.replay program (some sourceCtx)
  let ctx ← closedReplayContext sourceCtx
  let (result, state) ← EngineM.runWithRuntime runtime ctx s replayMethods <|
    withCatchingRuntimeEx <| simp e
  finishReplay runtime result.expr
  recordSimpUses state
  return (result, state)

def dsimpMainCoreReplay (e : Expr) (sourceCtx : Context) (config : ReplayConfig)
    (program : Program) (s : State := {}) : MetaM (Expr × State) := do
  let actualConfig ← replayConfigOfContext sourceCtx
  unless actualConfig == config do throwError "replay_configuration_mismatch"
  let initialFingerprint ← exprFingerprintHash e
  unless initialFingerprint == program.initialFingerprint do
    throwError "replay_initial_fingerprint_mismatch: expected {program.initialFingerprint}, got {initialFingerprint}"
  let runtime ← Runtime.replay program (some sourceCtx)
  let ctx ← closedReplayContext sourceCtx
  let (result, state) ← EngineM.runWithRuntime runtime ctx s replayMethods <|
    withCatchingRuntimeEx <| dsimp e
  finishReplay runtime result
  recordSimpUses state
  return (result, state)

def mkMethods (s : SimprocsArray) (dischargeBase : Expr → SimpM (Option Expr))
    (wellBehavedDischarge : Bool) : Methods := {
  pre        := preDefault s
  post       := postDefault s
  dpre       := dpreDefaultRecorded s
  dpost      := dpostDefaultRecorded s
  discharge? := fun e => liftSimpM (dischargeBase e)
  wellBehavedDischarge
  customDischarger := true
  base := Simp.mkMethods s dischargeBase wellBehavedDischarge
}

def mkDefaultMethodsCore (simprocs : SimprocsArray) : Methods :=
  {
    pre := preDefault simprocs
    post := postDefault simprocs
    dpre := dpreDefaultRecorded simprocs
    dpost := dpostDefaultRecorded simprocs
    discharge? := dischargeDefault?
    wellBehavedDischarge := true
    base := Simp.mkDefaultMethodsCore simprocs
  }

def mkDefaultMethods : CoreM Methods := do
  if simprocs.get (← getOptions) then
    return mkDefaultMethodsCore #[(← getSimprocs)]
  else
    return mkDefaultMethodsCore {}

end Simp.Engine
end Lean.Meta
