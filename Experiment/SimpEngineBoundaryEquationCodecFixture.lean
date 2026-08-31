import ExplicitLean.SimpEngine.Boundary.EquationCodec

open Lean Meta ExplicitLean.SimpEngine.Boundary

def EquationCodecProbe.anchor (n : Nat) : Nat := n
def EquationCodecProbe.otherAnchor (n : Nat) : Nat := n

private def capturedTheorem (name : Name) : TheoremVal := {
  name
  levelParams := []
  type := mkConst ``True
  value := mkConst ``True.intro
  all := []
}

private def rawPayload (anchor : Name) (theoremSource : String)
    (defeqTag backwardTag registerEqn : Json) : String :=
  (Json.arr #[.str "boundary_equation_v1", encodeBoundaryName anchor,
    .str theoremSource, defeqTag, backwardTag, registerEqn]).compress

private def expectFailure (action : MetaM Unit) : MetaM Unit := do
  let failed ← try
    action
    pure false
  catch _ => pure true
  unless failed do throwError "expected equation codec failure"

private def namespaces (env : Environment) : Array Name :=
  env.getNamespaces.toArray.qsort Name.quickLt

private def checkRealized (anchor name : Name)
    (defeqTag backwardTag registerEqn : Bool) : MetaM Unit := do
  let env ← getEnv
  let some (.thmInfo thm) := env.find? name (skipRealize := true)
    | throwError "captured equation theorem was not realized"
  unless thm.type == mkConst ``True && thm.value == mkConst ``True.intro do
    throwError "capture was replaced by a generated equation theorem"
  unless thm.all.isEmpty && thm.levelParams.isEmpty do
    throwError "captured equation theorem metadata changed"
  unless defeqAttr.hasTag env name == defeqTag &&
      backwardDefeqAttr.hasTag env name == backwardTag do
    throwError "captured equation tags changed"
  let expected? := if registerEqn then some anchor else none
  unless (eqnsExt.getState env).mapInv.find? name == expected? do
    throwError "captured equation registration changed"

run_meta do
  let anchor := ``EquationCodecProbe.anchor
  let name := Name.str anchor "eq_1"
  let envBefore ← getEnv
  unless envBefore.areRealizationsEnabledForConst anchor do
    throwError "fixture anchor did not enable realizations"
  unless !(envBefore.find? name (skipRealize := true)).isSome do
    throwError "fresh-process fixture equation already exists"
  unless !envBefore.isNamespace anchor do
    throwError "fixture namespace check would be vacuous"
  let namespacesBefore := namespaces envBefore

  -- The fabricated True theorem is deliberately unlike equation-generator
  -- output and would fail attribute validation. Only direct captured replay
  -- can add this checked proof and its exact tags.
  let source ← encodeBoundaryEquation anchor (capturedTheorem name) true true true
  executeBoundaryEquation name source
  checkRealized anchor name true true true
  unless namespaces (← getEnv) == namespacesBefore do
    throwError "fresh equation realization changed namespaces"
  executeBoundaryEquation name source

  -- The shared realization cache carries tags, but not the caller-local
  -- equation mapping. Replay must restore the mapping after the cache hit.
  setEnv envBefore
  unless ((eqnsExt.getState (← getEnv)).mapInv.find? name).isNone do
    throwError "equation registration escaped its caller branch"
  executeBoundaryEquation name source
  checkRealized anchor name true true true
  unless namespaces (← getEnv) == namespacesBefore do
    throwError "cached equation realization changed namespaces"

  let wrongDefeq ← encodeBoundaryEquation anchor (capturedTheorem name) false true true
  setEnv envBefore
  expectFailure (executeBoundaryEquation name wrongDefeq)
  unless ((eqnsExt.getState (← getEnv)).mapInv.find? name).isNone do
    throwError "failed tag validation registered an equation"
  executeBoundaryEquation name source
  let wrongBackward ← encodeBoundaryEquation anchor (capturedTheorem name) true false true
  expectFailure (executeBoundaryEquation name wrongBackward)
  let wrongAll ← encodeBoundaryEquation anchor
    { capturedTheorem name with all := [name] } true true true
  expectFailure (executeBoundaryEquation name wrongAll)
  let otherTheorem := { capturedTheorem name with
    type := mkForall `impossible .default (mkConst ``False) (mkConst ``False)
    value := mkLambda `impossible .default (mkConst ``False) (mkBVar 0) }
  let wrongType ← encodeBoundaryEquation anchor otherTheorem true true true
  expectFailure (executeBoundaryEquation name wrongType)
  let wrongRegistration ← encodeBoundaryEquation anchor (capturedTheorem name) true true false
  expectFailure (executeBoundaryEquation name wrongRegistration)
  checkRealized anchor name true true true

  let envRegistered ← getEnv
  let otherAnchor := ``EquationCodecProbe.otherAnchor
  modifyEnv fun env => eqnsExt.modifyState env fun state =>
    { state with mapInv := state.mapInv.insert name otherAnchor }
  expectFailure (executeBoundaryEquation name source)
  unless (eqnsExt.getState (← getEnv)).mapInv.find? name == some otherAnchor do
    throwError "conflicting registration was overwritten"
  setEnv envRegistered

  -- Cover every supported suffix family, independent exact tag bits, and a
  -- decimal index containing the separators accepted by pinned Lean.isNat.
  for (suffix, defeqTag, backwardTag) in
      [("eq_def", false, false), ("eq_unfold", false, true), ("eq_1_0", true, false)] do
    let otherName := Name.str anchor suffix
    let otherSource ← encodeBoundaryEquation anchor (capturedTheorem otherName)
      defeqTag backwardTag false
    executeBoundaryEquation otherName otherSource
    checkRealized anchor otherName defeqTag backwardTag false
  unless namespaces (← getEnv) == namespacesBefore do
    throwError "equation suffix realization changed namespaces"

  -- Imported definitions realize against their import-time environment.
  let importedAnchor := ``Nat.add
  let importedName := Name.str importedAnchor "eq_37"
  unless !(← getEnv).containsOnBranch importedName do
    throwError "imported equation fixture theorem already exists"
  let importedSource ← encodeBoundaryEquation importedAnchor (capturedTheorem importedName)
    false true true
  executeBoundaryEquation importedName importedSource
  checkRealized importedAnchor importedName false true true
  unless namespaces (← getEnv) == namespacesBefore do
    throwError "imported equation realization changed namespaces"

  let theoremSource ← encodeBoundaryTheorem (capturedTheorem name)
  for malformed in ["[]", "null", "[\"boundary_equation_v0\"]"] do
    expectFailure (executeBoundaryEquation name malformed)
  for (defeqTag, backwardTag, registerEqn) in
      [(Json.num 1, .bool true, .bool true), (.bool true, .str "true", .bool true),
       (.bool true, .bool true, .null)] do
    expectFailure (executeBoundaryEquation name
      (rawPayload anchor theoremSource defeqTag backwardTag registerEqn))
  let foreignTheoremSource ← encodeBoundaryTheorem (capturedTheorem (Name.str anchor "eq_2"))
  expectFailure (executeBoundaryEquation name
    (rawPayload anchor foreignTheoremSource (.bool true) (.bool true) (.bool true)))
  expectFailure (executeBoundaryEquation ``True source)
  expectFailure (executeBoundaryEquation (Name.num anchor 1) source)
  expectFailure (executeBoundaryEquation (Name.str otherAnchor "eq_1") source)
  for suffix in ["other", "congr_simp", "eq_", "eq_x", "eq_1__0", "eq_1_"] do
    let badName := Name.str anchor suffix
    expectFailure (executeBoundaryEquation badName source)
    expectFailure (discard <| encodeBoundaryEquation anchor (capturedTheorem badName)
      false false false)

  let missingAnchor := Name.str ``Nat.add "eq_38"
  let missingName := Name.str missingAnchor "eq_1"
  unless !(← getEnv).containsOnBranch missingAnchor do
    throwError "missing equation anchor negative control already exists"
  let missingTheoremSource ← encodeBoundaryTheorem (capturedTheorem missingName)
  expectFailure (executeBoundaryEquation missingName
    (rawPayload missingAnchor missingTheoremSource (.bool false) (.bool false) (.bool false)))
  unless !(← getEnv).containsOnBranch missingAnchor do
    throwError "equation anchor validation invoked reserved generation"

  let privateAnchor := mkPrivateName (← getEnv) anchor
  let privateName := Name.str privateAnchor "eq_1"
  expectFailure (discard <| encodeBoundaryEquation privateAnchor (capturedTheorem privateName)
    false false false)

  -- Do not replace an absent elaborator realization context with a later one.
  let unenabledAnchor := `EquationCodecProbe.unenabledAnchor
  addDecl (.thmDecl (capturedTheorem unenabledAnchor))
  unless !(← getEnv).areRealizationsEnabledForConst unenabledAnchor do
    throwError "unenabled equation anchor control enabled realizations"
  let unenabledName := Name.str unenabledAnchor "eq_1"
  let unenabledSource ← encodeBoundaryEquation unenabledAnchor (capturedTheorem unenabledName)
    false false false
  expectFailure (executeBoundaryEquation unenabledName unenabledSource)
  unless !(← getEnv).areRealizationsEnabledForConst unenabledAnchor &&
      !(← getEnv).containsOnBranch unenabledName do
    throwError "equation executor silently enabled realizations"
