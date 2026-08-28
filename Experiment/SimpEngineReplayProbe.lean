import ExplicitLean.SimpEngine.Replay

set_option simprocs false

open Lean Meta Elab Tactic

def replayDelta (n : Nat) : Nat := n + 0

opaque ReplayHolds : Prop → Prop
axiom replayHoldsTrue : ReplayHolds True

opaque replayMetadataIdentity : Prop → Prop
axiom replayMetadataRule {p : Prop} (_ : p) : replayMetadataIdentity p = True

opaque ReplaySeeProp : Prop → Prop
opaque ReplaySeeFin {n : Nat} : Fin n → Prop
opaque ReplayDepends {p : Prop} : p → Prop
inductive ReplayGroundBox where
  | value
opaque ReplaySeeGroundBox : ReplayGroundBox → Prop
def replayGroundValue : ReplayGroundBox :=
  let box := ReplayGroundBox.value
  box
axiom replaySeePropTrue : ReplaySeeProp (∀ x : True, ReplayDepends x)
axiom replaySeeArrow (p q : Prop) : ReplaySeeProp (p → q)
axiom replaySeeGroundValue : ReplaySeeGroundBox .value

private def programUsesMetadataBody (program : Simp.Engine.Program) : Bool :=
  program.events.any (fun event => event.path.steps.contains .metadataBody) ||
    program.structural.any (fun witness => witness.path.steps.contains .metadataBody)

private def programUsesPathStep (program : Simp.Engine.Program)
    (step : Simp.Engine.PathStep) : Bool :=
  program.events.any (fun event => event.path.steps.contains step) ||
    program.structural.any (fun witness => witness.path.steps.contains step)

elab "check_shared_expression_fingerprint" : tactic => withMainContext do
  let mut expression := mkConst ``True
  for _ in [0:40] do
    expression := mkApp2 (mkConst ``And) expression expression
  let fingerprint ← Simp.Engine.exprFingerprint expression
  let hashOnly ← Simp.Engine.exprFingerprintHash expression
  unless fingerprint.fingerprint == hashOnly && hashOnly.startsWith "expr-v2:" do
    throwError "shared expression fingerprint paths disagree: {fingerprint.fingerprint} != {hashOnly}"
  let size ← Simp.Engine.exprSize expression
  unless size.treeNodesCapped && size.treeNodes == Simp.Engine.exprTreeSizeLimit &&
      size.dagNodes == 82 do
    throwError "shared expression size was not DAG-bounded: {repr size}"

elab "check_simproc_trace_roundtrip" : tactic => withMainContext do
  let observation : Simp.Engine.SimprocObservation := {
    path := { steps := #[.appFunction] }
    name := `traceFixture
    phase := .post
    inputFingerprint := "input"
    outputFingerprint := "output"
    outputChanged := true
    stepDisposition := .visit
    definitional := false
    procedureKind := .simp
    numExtraArgs := 2
    executed := true
    proofPresent := true
    cache := some false
    outputSize := some { treeNodes := 7, treeNodesCapped := false, dagNodes := 5 }
  }
  let trace : Simp.Engine.SimprocTrace := {
    observations := #[observation, observation, { observation with phase := .pre }]
  }
  let encoded := Lean.toJson trace
  let decoded : Simp.Engine.SimprocTrace ←
    match Lean.fromJson? encoded with
    | .ok decoded => pure decoded
    | .error message => throwError "simproc trace failed to decode: {message}"
  unless decoded == trace do
    throwError "simproc trace dictionary encoding changed invocation order"
  let dictionary ← match encoded.getObjValAs? (Array Simp.Engine.SimprocObservation)
      "dictionary" with
    | .ok dictionary => pure dictionary
    | .error message => throwError "simproc trace omitted its dictionary: {message}"
  unless dictionary.size == 2 do
    throwError "simproc trace did not dictionary repeated observations: {dictionary.size}"

elab "check_semantic_fold_roundtrip" : tactic => withMainContext do
  let inputRef : Simp.Engine.InputSubtermRef := {
    path := #[.appFunction, .metadataBody]
    fingerprint := "input-subterm"
  }
  let localRef : Simp.Engine.LocalRef := {
    contextIndex := 3
    binderDepth := 1
    typeFingerprint := "Nat"
    valueFingerprint := some "local-value"
  }
  let witness : Simp.Engine.InstanceWitness := {
    term := .application `Nat.add #[] #[
      .input inputRef,
      .local localRef,
      .literal (.nat 7)]
    typeFingerprint := "Nat → Nat → Nat"
  }
  let derivation : Simp.Engine.NatBinaryDerivation := {
    operator := .add
    lhs := 3
    rhs := 4
    result := 7
    lhsView := .raw inputRef 3 1
    rhsView := .ofNat inputRef 4 2 witness
    operatorInstance := witness
  }
  let candidate : Simp.Engine.SimprocCandidateEvent := {
    declaration := `Nat.reduceAdd
    procedureKind := .dsimp
    semantics := .canonicalValue (.natBinary derivation)
    setIndex := 2
    registryPost := true
    inputFingerprint := "raw-input"
    peeledInputFingerprint := "peeled-input"
    extraArgumentFingerprints := #["extra-0", "extra-1"]
    procedureOutputFingerprint := "procedure-output"
    outputFingerprint := "candidate-output"
    numExtraArgs := 2
    disposition := .done
    proofPresent := false
    cache := none
  }
  let fold : Simp.Engine.SimprocFold := {
    phase := .dpost
    candidates := #[candidate]
    finalOutputFingerprint := "final-output"
    finalDisposition := .done
    finalProofPresent := false
    finalCache := none
  }
  let operation : Simp.Engine.Operation := .semanticSimproc fold
  let program : Simp.Engine.Program := {
    initialFingerprint := "program-input"
    finalFingerprint := "program-output"
    events := #[{
      path := { steps := #[.simprocInternal 0 0 0] }
      phase := .dpost
      invocationOrdinal := 0
      operation
      inputFingerprint := "program-input"
      outputFingerprint := "program-output"
      stepDisposition := .done
    }]
  }
  let nested : Simp.Engine.NestedProgram := {
    program := {
      initialFingerprint := "nested-input"
      finalFingerprint := "nested-output"
    }
    simprocs := {}
    statePolicy := .isolatedStats
    configPolicy := .defaultSimp
    dischargeDepthIncrement := 1
  }
  let decodedFold : Simp.Engine.SimprocFold ←
    match Lean.fromJson? (Lean.toJson fold) with
    | .ok decoded => pure decoded
    | .error message => throwError "semantic fold failed to decode: {message}"
  unless decodedFold == fold do
    throwError "semantic fold JSON roundtrip mismatch"
  let decodedProgram : Simp.Engine.Program ←
    match Lean.fromJson? (Lean.toJson program) with
    | .ok decoded => pure decoded
    | .error message => throwError "semantic program failed to decode: {message}"
  unless decodedProgram == program do
    throwError "semantic program JSON roundtrip mismatch"
  let decodedNested : Simp.Engine.NestedProgram ←
    match Lean.fromJson? (Lean.toJson nested) with
    | .ok decoded => pure decoded
    | .error message => throwError "nested semantic program failed to decode: {message}"
  unless decodedNested == nested do
    throwError "nested semantic policy JSON roundtrip mismatch"
  match (Lean.fromJson? (Json.str "not-a-nested-program") :
      Except String Simp.Engine.NestedProgram) with
  | .ok _ => throwError "malformed nested semantic program JSON was accepted"
  | .error _ => pure ()

elab "check_engine_terminals_replay" : tactic => withMainContext do
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let methods := Simp.Engine.mkDefaultMethodsCore {}
  let proofExpression := mkConst ``True.intro
  let (_, _, proofRecording) ←
    Simp.Engine.mainCoreRecording proofExpression ctx (methods := methods)
  unless proofRecording.coveredBranches.contains "struct.proofSkip" do
    throwError "proof fixture missed its structural terminal"
  let config ← Simp.Engine.replayConfigOfContext ctx
  let _ ← Simp.Engine.mainCoreReplay proofExpression ctx config proofRecording.program
  let mvarExpression ← mkFreshExprMVar (mkConst ``Nat)
  let (_, _, mvarRecording) ←
    Simp.Engine.mainCoreRecording mvarExpression ctx (methods := methods)
  unless mvarRecording.coveredBranches.contains "struct.unassignedMVarStop" do
    throwError "unassigned mvar fixture missed its structural terminal"
  let _ ← Simp.Engine.mainCoreReplay mvarExpression ctx config mvarRecording.program
  let metadataExpression := mkMData MData.empty (mkConst ``True)
  let (_, _, metadataRecording) ←
    Simp.Engine.mainCoreRecording metadataExpression ctx (methods := methods)
  unless programUsesMetadataBody metadataRecording.program do
    throwError "simp metadata fixture did not qualify its recursive path"
  let _ ← Simp.Engine.mainCoreReplay metadataExpression ctx config metadataRecording.program
  let (_, _, metadataDSimpRecording) ←
    Simp.Engine.dsimpMainCoreRecording metadataExpression ctx (methods := methods)
  unless programUsesMetadataBody metadataDSimpRecording.program do
    throwError "dsimp metadata fixture did not qualify its recursive path"
  let _ ← Simp.Engine.dsimpMainCoreReplay metadataExpression ctx config
    metadataDSimpRecording.program
  let lambdaExpression := mkLambda `x .default (mkConst ``Nat) <|
    mkLambda `y .default (mkConst ``Nat) (mkBVar 1)
  let (_, _, lambdaRecording) ←
    Simp.Engine.dsimpMainCoreRecording lambdaExpression ctx (methods := methods)
  unless programUsesPathStep lambdaRecording.program (.lambdaDomain 0) &&
      programUsesPathStep lambdaRecording.program (.lambdaDomain 1) &&
      !programUsesPathStep lambdaRecording.program (.forallDomain 0) do
    throwError "dsimp lambda fixture recorded an incorrect binder-domain path"
  let _ ← Simp.Engine.dsimpMainCoreReplay lambdaExpression ctx config lambdaRecording.program
  let forallExpression := mkForall `x .default (mkConst ``Nat) <|
    mkForall `y .default (mkConst ``Nat) (mkSort 1)
  let (_, _, forallRecording) ←
    Simp.Engine.dsimpMainCoreRecording forallExpression ctx (methods := methods)
  unless programUsesPathStep forallRecording.program (.forallDomain 0) &&
      programUsesPathStep forallRecording.program (.forallDomain 1) &&
      !programUsesPathStep forallRecording.program (.lambdaDomain 0) do
    throwError "dsimp forall fixture recorded an incorrect binder-domain path"
  let _ ← Simp.Engine.dsimpMainCoreReplay forallExpression ctx config forallRecording.program
  let branches := proofRecording.coveredBranches ++ mvarRecording.coveredBranches ++
    metadataRecording.coveredBranches ++ metadataDSimpRecording.coveredBranches ++
    lambdaRecording.coveredBranches ++ forallRecording.coveredBranches
  logInfo m!"SIMP_ENGINE_REPLAY branches={String.intercalate "," branches.toList}"

opaque replayPairAdd : Nat → Nat → Nat
axiom replayTwoPremises {a b : Nat} (ha : a = 0) (hb : b = 0) :
  replayPairAdd a b = 0

opaque replayVariantFirst : Nat → Nat
opaque replayVariantSecond : Nat → Nat
axiom replayConjoinedVariants (n : Nat) :
  replayVariantFirst n = n ∧ replayVariantSecond n = n

@[congr] theorem ReplayHolds.congr {p q : Prop} (h : p = q)
    (_side : True) : ReplayHolds p = ReplayHolds q :=
  congrArg ReplayHolds h

elab "check_user_congruence_premise_replay" : tactic => withMainContext do
  let registered := (← getSimpCongrTheorems).get ``ReplayHolds
  unless registered.any (fun entry => entry.theoremName == ``ReplayHolds.congr) do
    throwError "user congruence fixture theorem is not registered: {repr registered}"
  let simpStx ← `(tactic| simp)
  let recording ← ExplicitLean.SimpEngine.Recording.recordCertificate simpStx.raw
  let mut found := false
  let mut observations : Array String := #[]
  for subject in recording.certificate.subjects do
    for witness in subject.program.structural do
      if let .congruence _ (.user theoremName _ _ _ _ premises) := witness.witness then
        observations := observations.push s!"{theoremName}:{premises.size}"
        if theoremName == ``ReplayHolds.congr && !premises.isEmpty then found := true
  unless found do
    throwError "user congruence fixture did not record its side-premise program: registered={repr registered}, observed={observations}"
  ExplicitLean.SimpEngine.Replay.replayCertificate recording
  logInfo m!"SIMP_ENGINE_REPLAY branches={String.intercalate "," recording.branches.toList}"

elab "check_metadata_discharge_replay" : tactic => withMainContext do
  let metadataTrue := mkMData MData.empty (mkConst ``True)
  let target := mkApp (mkConst ``replayMetadataIdentity) metadataTrue
  let simpStx ← `(tactic| simp only [replayMetadataRule])
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  let (recording, replayed) ← dischargeWrapper.with fun discharge? => do
    let methods := match discharge? with
      | none => Simp.Engine.mkDefaultMethodsCore simprocs
      | some discharge => Simp.Engine.mkMethods simprocs discharge
          (wellBehavedDischarge := false)
    let (_, _, recording) ←
      Simp.Engine.mainCoreRecording target ctx (methods := methods)
    let config ← Simp.Engine.replayConfigOfContext ctx
    let (replayed, _) ← Simp.Engine.mainCoreReplay target ctx config recording.program
    pure (recording, replayed)
  let mut foundPremise := false
  for event in recording.program.events do
    match event.operation with
    | .rewrite rule _ premises =>
        if rule.origin == .decl ``replayMetadataRule then
          for premise in premises do
            if premise.terminal == .isTrue then
              foundPremise := true
    | _ => pure ()
  unless foundPremise do
    throwError "metadata fixture did not record a default-discharge premise"
  unless replayed.expr.isTrue do
    throwError "metadata fixture closed replay did not reach True: {replayed.expr}"
  logInfo m!"SIMP_ENGINE_REPLAY metadataDischarge=closed"

elab "check_ground_equation_replay" : tactic => withMainContext do
  let simpStx ← `(tactic| simp (config := { zeta := false }) +ground)
  let recording ← ExplicitLean.SimpEngine.Recording.recordCertificate simpStx.raw
  let found := recording.certificate.subjects.any fun subject =>
    subject.program.events.any fun event =>
      event.path.steps.contains .ground &&
        match event.operation with
        | .rewrite rule _ _ => match rule.origin with
          | .equation declaration _ => declaration == ``replayGroundValue
          | _ => false
        | _ => false
  unless found do
    throwError "ground fixture did not record a stable source-declaration equation origin"
  ExplicitLean.SimpEngine.Replay.replayCertificate recording
  logInfo m!"SIMP_ENGINE_REPLAY branches={String.intercalate "," recording.branches.toList}"

example (xs : List Nat) : xs ++ [] = xs := by
  simp_engine_replay only [List.append_nil]

example (x : Nat) : (fun y => y) x = x := by
  simp_engine_replay only

example (x : Nat) : replayDelta x = x := by
  simp_engine_replay only [replayDelta, Nat.add_zero]

example (x : Nat) : x = x := by
  let requestedLocal := x
  have unfolded : requestedLocal = x := by
    simp_engine_replay only [requestedLocal]
  exact unfolded

example (x : Nat) : (x + 0, x + 0) = (x, x) := by
  simp_engine_replay only [Nat.add_zero]

example (n : Nat) : (match some n with | some k => k + 0 | none => 0) = n := by
  simp_engine_replay

example (p : Nat × Nat) : (p.1, p.2) = p := by
  simp_engine_replay

example (p : Nat × Nat) : Prod.fst p = p.1 := by
  simp_engine_replay

example (p q : Prop) (h : p → q) : p → q := by
  simp_engine_replay (config := { contextual := true }) only [h]
  intro
  trivial

example : True := by
  check_shared_expression_fingerprint
  check_simproc_trace_roundtrip
  check_semantic_fold_roundtrip
  check_engine_terminals_replay
  trivial

example : (fun y : Nat => y + 0) = fun y => y := by
  simp_engine_replay

example (P : Nat → Prop) : (∀ n, P n ∧ True) ↔ ∀ n, P n := by
  simp_engine_replay

example (p q : Prop) : ReplaySeeProp (p ∧ True → q) := by
  simp_engine_replay only [and_true]
  exact replaySeeArrow p q

example (p q : Prop) (h : p) (hpq : p → q) : q := by
  simp_engine_replay only [hpq, h]

example (a b : Nat) (ha : a = 0) (hb : b = 0) : replayPairAdd a b = 0 := by
  simp_engine_replay only [replayTwoPremises, ha, hb]

example (n : Nat) : replayVariantSecond n = n := by
  simp_engine_replay only [replayConjoinedVariants]

example : ReplayHolds (True ∧ True) := by
  check_user_congruence_premise_replay
  exact replayHoldsTrue

example : True := by
  check_metadata_discharge_replay
  trivial

example (h : ReplaySeeProp (∀ x : True ∧ True, ReplayDepends x)) :
    ReplaySeeProp (∀ x : True ∧ True, ReplayDepends x) := by
  simp_engine_replay
  exact replaySeePropTrue

example {n : Nat} (a : Fin n) (h : ReplaySeeFin (Fin.mk a.val a.isLt)) :
    ReplaySeeFin (Fin.mk a.val a.isLt) := by
  simp_engine_replay
  exact h

example (x : Nat) : (have y := x + 0; y) = x := by
  simp_engine_replay (config := { zeta := false }) only [Nat.add_zero]
  rfl

example (p : Prop) (h : p) : (have hp : p := h; True) := by
  simp_engine_replay (config := { zeta := false, zetaUnused := true })

example (x : Nat) (h : x + 0 = x) : True := by
  simp_engine_replay at h ⊢

example (h : False) : True := by
  simp_engine_replay at h

example : (20 : Nat) < 30 := by
  simp_engine_replay +decide

example (x : Int) : x + x + 0 = 2 * x := by
  simp_engine_replay +arith

example : ReplaySeeGroundBox replayGroundValue := by
  check_ground_equation_replay
  exact replaySeeGroundValue
