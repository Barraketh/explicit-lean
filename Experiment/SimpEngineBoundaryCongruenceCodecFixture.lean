import ExplicitLean.SimpEngine.Boundary.CongruenceCodec

open Lean Meta ExplicitLean.SimpEngine.Boundary

def CongruenceCodecProbe.anchor (n : Nat) : Nat := n
def CongruenceCodecProbe.directAnchor (n : Nat) : Nat := n

private def capturedTheorem (name : Name) : TheoremVal := {
  name
  levelParams := []
  type := mkConst ``True
  value := mkConst ``True.intro
  all := []
}

private def rawPayload (anchor : Name) (theoremSource : String) (kinds : Json) : String :=
  (Json.arr #[.str "boundary_congruence_v1", encodeBoundaryName anchor,
    .str theoremSource, kinds]).compress

private def expectFailure (action : MetaM Unit) : MetaM Unit := do
  let failed ← try
    action
    pure false
  catch _ => pure true
  unless failed do throwError "expected congruence codec failure"

private def namespaces (env : Environment) : Array Name :=
  env.getNamespaces.toArray.qsort Name.quickLt

private def checkRealized (name : Name) (kinds : Array CongrArgKind) : MetaM Unit := do
  let some (.thmInfo thm) := (← getEnv).find? name (skipRealize := true)
    | throwError "captured theorem was not realized"
  unless thm.type == mkConst ``True && thm.value == mkConst ``True.intro do
    throwError "capture was replaced by a generated congruence theorem"
  unless thm.all.isEmpty && thm.levelParams.isEmpty do
    throwError "captured theorem metadata changed"
  unless congrKindsExt.find? (← getEnv) name == some kinds do
    throwError "captured argument kinds are unavailable"

run_meta do
  let anchor := ``CongruenceCodecProbe.anchor
  let name := Name.str anchor "congr_simp"
  let kinds : Array CongrArgKind :=
    #[.fixed, .fixedNoParam, .eq, .cast, .heq, .subsingletonInst]
  let envBefore ← getEnv
  unless envBefore.areRealizationsEnabledForConst anchor do
    throwError "fixture anchor did not enable realizations"
  unless !(envBefore.find? name (skipRealize := true)).isSome do
    throwError "fresh-process fixture theorem already exists"
  unless !envBefore.isNamespace anchor do
    throwError "fixture namespace check would be vacuous"
  let namespacesBefore := namespaces envBefore

  -- A manually constructed, closed capture deliberately unlike stock
  -- congruence output proves that the fresh realization executes our closure.
  -- No theorem generator is invoked anywhere in this fixture.
  let source ← encodeBoundaryCongruence anchor (capturedTheorem name) kinds
  executeBoundaryCongruence name source
  checkRealized name kinds
  unless namespaces (← getEnv) == namespacesBefore do
    throwError "fresh realization changed namespaces"

  -- Exercise both an already-present declaration and the shared cache from
  -- the environment that preceded realization; neither can skip validation.
  executeBoundaryCongruence name source
  setEnv envBefore
  executeBoundaryCongruence name source
  checkRealized name kinds
  unless namespaces (← getEnv) == namespacesBefore do
    throwError "cached realization changed namespaces"

  let wrongKinds ← encodeBoundaryCongruence anchor (capturedTheorem name) #[.eq]
  setEnv envBefore
  expectFailure (executeBoundaryCongruence name wrongKinds)
  checkRealized name kinds
  let wrongAll ← encodeBoundaryCongruence anchor
    { capturedTheorem name with all := [name] } kinds
  expectFailure (executeBoundaryCongruence name wrongAll)
  let falseValue := mkLambda `impossible .default (mkConst ``False) (mkBVar 0)
  let otherTheorem := { capturedTheorem name with
    type := mkForall `impossible .default (mkConst ``False) (mkConst ``False)
    value := falseValue }
  let wrongType ← encodeBoundaryCongruence anchor otherTheorem kinds
  expectFailure (executeBoundaryCongruence name wrongType)
  let foreignTheoremSource ← encodeBoundaryTheorem (capturedTheorem (Name.str anchor "hcongr_2"))
  expectFailure (executeBoundaryCongruence name
    (rawPayload anchor foreignTheoremSource (.arr #[])))
  checkRealized name kinds

  -- The other supported reserved suffix, including an empty argument vector.
  let hcongrName := Name.str anchor "hcongr_0"
  let hcongrSource ← encodeBoundaryCongruence anchor (capturedTheorem hcongrName) #[]
  executeBoundaryCongruence hcongrName hcongrSource
  checkRealized hcongrName #[]
  unless namespaces (← getEnv) == namespacesBefore do
    throwError "heterogeneous realization changed namespaces"

  -- Imported anchors use Lean's import-time realization environment instead
  -- of the current-module environment captured by their elaborator.
  let importedAnchor := ``Nat.succ
  let importedName := Name.str importedAnchor "hcongr_37"
  unless !(← getEnv).containsOnBranch importedName do
    throwError "imported anchor fixture theorem already exists"
  let importedSource ← encodeBoundaryCongruence importedAnchor
    (capturedTheorem importedName) #[.heq]
  executeBoundaryCongruence importedName importedSource
  checkRealized importedName #[.heq]
  unless namespaces (← getEnv) == namespacesBefore do
    throwError "imported-anchor realization changed namespaces"

  let theoremSource ← encodeBoundaryTheorem (capturedTheorem name)
  for kindJson in [Json.arr #[.str "unknown"], .arr #[.num 0], .str "eq"] do
    expectFailure (executeBoundaryCongruence name (rawPayload anchor theoremSource kindJson))
  for malformed in ["[]", "null", "[\"boundary_congruence_v0\"]"] do
    expectFailure (executeBoundaryCongruence name malformed)
  expectFailure (executeBoundaryCongruence ``True source)
  expectFailure (executeBoundaryCongruence (Name.num anchor 0) source)
  expectFailure (executeBoundaryCongruence
    (Name.str ``CongruenceCodecProbe.directAnchor "congr_simp") source)
  for suffix in ["other", "hcongr", "hcongr_", "hcongr_x", "hcongr_1x"] do
    let badName := Name.str anchor suffix
    expectFailure (executeBoundaryCongruence badName source)
    expectFailure (discard <| encodeBoundaryCongruence anchor (capturedTheorem badName) #[])

  -- A reserved but absent anchor must stay absent: anchor validation must not
  -- invoke the stock reserved-name generator even to test its existence.
  let missingAnchor := Name.str ``Nat.succ "hcongr_38"
  let missingName := Name.str missingAnchor "congr_simp"
  unless !(← getEnv).containsOnBranch missingAnchor do
    throwError "missing anchor negative control already exists"
  let missingTheoremSource ← encodeBoundaryTheorem (capturedTheorem missingName)
  expectFailure (executeBoundaryCongruence missingName
    (rawPayload missingAnchor missingTheoremSource (.arr #[])))
  expectFailure (discard <| encodeBoundaryCongruence missingAnchor (capturedTheorem missingName) #[])
  unless !(← getEnv).containsOnBranch missingAnchor do
    throwError "anchor validation invoked reserved-name generation"

  -- A directly added declaration has no captured kinds. This also establishes
  -- that direct addDecl would fail our earlier namespace-invariance checks.
  let directAnchor := ``CongruenceCodecProbe.directAnchor
  let directName := Name.str directAnchor "congr_simp"
  let directSource ← encodeBoundaryCongruence directAnchor (capturedTheorem directName) #[]
  addDecl (.thmDecl (capturedTheorem directName))
  unless (← getEnv).isNamespace directAnchor do
    throwError "direct declaration did not trigger namespace negative control"
  expectFailure (executeBoundaryCongruence directName directSource)
  unless (congrKindsExt.find? (← getEnv) directName).isNone do
    throwError "missing congruence metadata was silently filled"

  -- A raw declaration does not carry an elaborator's realization context.
  -- The executor must fail, not enable it with the current environment.
  let unenabledAnchor := `CongruenceCodecProbe.unenabledAnchor
  addDecl (.thmDecl (capturedTheorem unenabledAnchor))
  unless !(← getEnv).areRealizationsEnabledForConst unenabledAnchor do
    throwError "unenabled anchor negative control enabled realizations"
  let unenabledName := Name.str unenabledAnchor "congr_simp"
  let unenabledSource ← encodeBoundaryCongruence unenabledAnchor
    (capturedTheorem unenabledName) #[]
  expectFailure (executeBoundaryCongruence unenabledName unenabledSource)
  unless !(← getEnv).areRealizationsEnabledForConst unenabledAnchor &&
      !(← getEnv).containsOnBranch unenabledName do
    throwError "executor silently enabled realizations"
