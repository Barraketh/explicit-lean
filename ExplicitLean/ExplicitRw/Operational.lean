module
prelude

public meta import ExplicitLean.ExplicitRw.Tactic
public meta import ExplicitLean.ExplicitRw.LocalHandles
public meta import Lean.Elab.Tactic.Rewrite
public meta import Lean.Meta.Eqns

public meta section

/-!
# Operational rewrite steps

This is a closed, readable source form for one exact non-simproc rewrite
operation.  A global rule names its declaration; a local rule names either a
local identifier or an exact `local_ref` context index.  Each step also names
its direction, recorded pre/post phase, variant, extra-argument count, and raw
expression-child path.

The interpreter delegates equation matching, instance synthesis, side-goal
discharge, and positional congruence rebuilding to existing `ExplicitRw.Impl`
primitives. Variants are identity metadata, equation origins resolve through
Lean's exact declaration/index table, and `extra n` extends the raw path by `n`
function-child steps. It never calls `Lean.Meta.Simp`, discovers a rule, or
searches another path. Side goals use the existing closed side-proof grammar.
A `simproc` marker is recognized only to produce a direct rejection; it is
never executed or reconstructed.

The `with [...]` and `then ...` proof operations are term-free: `rfl`,
`true_intro`, `assumption h`, and `assumption local_ref n`.

Examples:

```
explicit_rw_v2 [rule Nat.add_zero variant 0 phase pre fwd extra 0 at [0, 1] with []]
explicit_rw_v2 [equation myDef index 0 variant 1 phase dpre fwd extra 0 at [0, 1] with []]
explicit_rw_v2 [local local_ref 4 variant 0 phase dpost rev extra 0 at [1] with []]
explicit_rw_v2 [beta at [0], instantiate at [1], iota at [2], proj at [3], zeta at [4]]
```
-/

namespace ExplicitLean.ExplicitRw

open Lean Elab Tactic Meta

namespace Operational

private def parsePos (stx : Syntax) : Pos :=
  Impl.parsePos stx

private def validateRuleMetadata
    (idx : Nat) (phaseStx directionStx : Syntax) :
    TacticM Bool := do
  -- The selected declaration/equation identity is authoritative. Variants
  -- distinguish recorder provenance but do not trigger simp-table lookup.
  let phaseName := phaseStx.getId.toString
  unless phaseName == "pre" || phaseName == "post" ||
      phaseName == "dpre" || phaseName == "dpost" do
    stepError idx m!"rewrite phase must be `pre`, `post`, `dpre`, or `dpost`, got `{phaseName}`."
  -- The direction parser is an alternation, so its token is one child below
  -- the anonymous choice node.
  let directionName := directionStx[0].getAtomVal
  unless directionName == "fwd" || directionName == "rev" do
    stepError idx m!"rewrite direction must be `fwd` or `rev`, got `{directionName}`."
  return directionName == "rev"

private def withExtra (pos : Pos) (extraStx : Syntax) : Pos :=
  pos ++ List.replicate (extraStx.isNatLit?.getD 0) 0

private def sideProofs (withStx : Syntax) : Array Syntax :=
  withStx[2].getSepArgs

private def lowerProof (stx : Syntax) : TacticM Syntax := do
  match stx.getKind with
  | ``explicitRwOperationalProofAtom =>
    match stx[0].getId.toString with
    | "rfl" => return (← `(explicitRwSideTac| rfl)).raw
    | "true_intro" => return (← `(explicitRwSideTac| close [True.intro])).raw
    | "equation_hypothesis" => return stx
    | atom => throwError "explicit_rw_v2: unknown closed proof operation `{atom}`"
  | ``explicitRwOperationalProofAssumption => do
    let hyp : Ident := ⟨stx[1]⟩
    let _ ← getFVarId hyp.raw
    return (← `(explicitRwSideTac| exact $hyp:ident)).raw
  | ``explicitRwOperationalProofAssumptionRef => do
    let localIndex : TSyntax `num := ⟨stx[2]⟩
    return (← `(explicitRwSideTac| exact local_ref $localIndex:num)).raw
  | ``explicitRwOperationalProofIntro =>
    -- `Impl.runSideProofOn` introduces the exact recorded binder count and
    -- recurses into the same closed operational proof grammar.
    return stx
  | ``explicitRwOperationalProofNested =>
    -- The nested v2 grammar is already closed. Preserve it for
    -- `Impl.runSideProofOn`, which runs it against exactly the premise goal.
    return stx
  | k => throwError "explicit_rw_v2: internal error: unknown closed proof operation `{k}`"

private def lowerProofs (withStx : Syntax) : TacticM (Array Syntax) :=
  (sideProofs withStx).mapM lowerProof

private def ruleConclusionMatchesPropCore (idx : Nat) (term : Term) (sub : Expr) :
    TacticM (Option Bool) := do
  -- Classify an equality/Iff theorem before considering proposition rules.
  -- Whether its left side matches is the actual rewrite step's job; treating a
  -- mismatching equation as proposition evidence produces misleading failures.
  let isEquation ← withoutModifyingMCtx do
    try
      let _ ← Impl.elabEquation idx term
      pure true
    catch _ => pure false
  if isEquation then return none
  -- This inspects only the named theorem's type. Opening its binders lets the
  -- exact selected proposition determine ordinary parameters; assignments
  -- made by this classification probe are discarded.
  let proof ←
    if let some name ← Impl.resolveBareConst? term then
      let info ← getConstInfo name
      let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      pure (mkConst name levels)
    else
      Impl.elabStrict (some idx) "the named proposition rule" term
        (allowMVars := true) (synthesize := false)
  let proofType ← inferType proof
  let (_, _, conclusion) ← forallMetaTelescope proofType
  withoutModifyingMCtx do
    let subType ← inferType sub
    let subIsBool ← isDefEq subType (mkConst ``Bool)
    let proposition? ←
      if subIsBool then
        some <$> mkAppM ``Eq #[sub, mkConst ``true]
      else if ← isProp sub then
        pure (some sub)
      else
        pure none
    let some proposition := proposition? | return none
    if ← isDefEq conclusion proposition then return some true
    if ← isDefEq conclusion (mkApp (mkConst ``Not) proposition) then return some false
    return none

private def ruleConclusionMatchesProp (idx : Nat) (term : Term) (sub : Expr) :
    TacticM (Option Bool) := do
  let saved ← Tactic.saveState
  try
    ruleConclusionMatchesPropCore idx term sub
  finally
    saved.restore

private def runPropRule (idx : Nat) (e : Expr) (pos : Pos) (term : Term)
    (truth : Bool) (sideTacs : Array Syntax) : TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let (proof, mvars) ← Impl.elabProposition idx term sub truth
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      synthesizeInstanceMVars idx m!"`{term}`" mvars sub
      let propMVars ← unassignedRewritePropMVars mvars
      if sideTacs.size > propMVars.size then
        stepError idx m!"the `with` clause supplies {sideTacs.size} proof(s) but proposition rule \
          `{term}` has {propMVars.size} undetermined hypothesis(es) at this position."
      for h : i in [0 : sideTacs.size] do
        let .mvar mid := ← instantiateMVars propMVars[i]! | pure ()
        Impl.runSideProofOn idx (some i) sideTacs[i] mid
      Term.synthesizeSyntheticMVarsNoPostponing
      closeLemmaMVars idx m!"`{term}`" mvars
      let proof ← instantiateMVars proof
      let subType ← inferType sub
      let subIsBool ← isDefEq subType (mkConst ``Bool)
      let (replacement, equality) ←
        if subIsBool then
          if truth then
            pure (mkConst ``true, proof)
          else
            pure (mkConst ``false, ← mkAppM ``Bool.of_not_eq_true #[proof])
        else
          let equality ←
            if truth then mkAppM ``eq_true #[proof] else mkAppM ``eq_false #[proof]
          pure (if truth then mkConst ``True else mkConst ``False, equality)
      Impl.checkNoLevelMVars idx m!"`{term}`" #[equality]
      return Replacement.eq replacement equality)
    (fun pfx child sub => badPosError idx pos pfx child sub)

private def runNamedRule (idx : Nat) (e : Expr) (pos : Pos) (term : Term)
    (reverse : Bool) (sideTacs : Array Syntax) : TacticM Replacement := do
  let isPropRef ← IO.mkRef (none : Option Bool)
  let _ ← rewriteAt e pos
    (fun sub => do
      isPropRef.set (← ruleConclusionMatchesProp idx term sub)
      return Replacement.defeq sub)
    (fun pfx child sub => badPosError idx pos pfx child sub)
  if let some truth := ← isPropRef.get then
    if reverse then
      stepError idx m!"a proposition-valued rule is only supported in the forward direction."
    runPropRule idx e pos term truth sideTacs
  else
    Impl.runRwStep idx e pos term reverse sideTacs

/--
Replay a nontrivial source operand through Lean's ordinary rewrite elaborator,
but only at the already selected expression. This matters for applications such
as `apply_ite Nat.cast`: the result carrier of the function argument is fixed
by matching the rewrite theorem, so elaborating it as a standalone equation
would try to synthesize `NatCast ?R` too early. `rw` deliberately elaborates
and matches in one transaction for exactly this reason.
-/
private def runElaboratedSourceRule (idx : Nat) (e : Expr) (pos : Pos) (term : Term)
    (reverse : Bool) (sideTacs : Array Syntax) : TacticM Replacement := do
  -- This is the exact source operand of the original `simp` call, not a
  -- serialized proof term. It is emitted visibly as ordinary Lean and the
  -- renderer rejects every simp-family token before producing this syntax.
  -- Thus an ordinary proof block such as `by omega` remains readable source.
  -- Its result is still elaborated without recovery, checked for `sorry`, and
  -- confined to the already-recorded root position.
  rewriteAt e pos
    (fun sub => do
      let syntheticsBefore := (← getThe Term.State).syntheticMVars
      -- `rewriteAt` may have opened binders on the path to `sub`. The main
      -- tactic goal predates those locals, so use a temporary goal created in
      -- the *current* context when asking Lean's rewrite elaborator to build
      -- the equation proof. Otherwise a rule below a forall can leak the
      -- opened binder as an unknown free variable.
      let contextGoalExpr ← mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
      let contextGoal := contextGoalExpr.mvarId!
      let result ← Term.withSynthesize do
        Tactic.elabRewrite contextGoal sub term.raw reverse
          (config := { occs := .pos [1] })
      contextGoal.assign (mkConst ``True.intro)
      -- `rewrite` numbers matching occurrences, not expression paths. Since it
      -- runs on the already selected subexpression, occurrence 1 must be its
      -- root. Reject a congruence motive here rather than silently accepting a
      -- nested match when the recorded source rule does not match that root.
      let equality ← instantiateMVars result.eqProof
      let args := equality.getAppArgs
      let rootRewrite :=
        equality.getAppFn.constName? == some ``congrArg &&
          match args[4]? with
          | some motive =>
            match motive with
            | .lam _ _ body _ => body == .bvar 0
            | _ => false
          | none => false
      unless rootRewrite do
        stepError idx m!"source rule `{term}` does not rewrite the root of the recorded \
          subexpression at position {Pos.render pos}."
      let mvars := result.mvarIds.toArray.map Expr.mvar
      let propMVars ← unassignedRewritePropMVars mvars
      if sideTacs.size > propMVars.size then
        stepError idx m!"the `with` clause supplies {sideTacs.size} proof(s) but source rule \
          `{term}` has {propMVars.size} undetermined hypothesis(es) at this position."
      for h : i in [0 : sideTacs.size] do
        let .mvar mid := ← instantiateMVars propMVars[i]! | pure ()
        Impl.runSideProofOn idx (some i) sideTacs[i] mid
      Term.synthesizeSyntheticMVarsNoPostponing
      closeLemmaMVars idx m!"`{term}`" mvars
      let replacement ← instantiateMVars result.eNew
      let equality ← instantiateMVars result.eqProof
      if replacement.hasSorry || replacement.hasSyntheticSorry ||
          equality.hasSorry || equality.hasSyntheticSorry then
        stepError idx m!"source rule `{term}` elaborated with an invalid recovery term."
      -- Every synthetic created by the source operand has been forced and all
      -- returned metavariables have been closed above. Do not let its resolved
      -- elaboration records escape a binder opened only while navigating this
      -- position; such a record would retain the temporary free-variable IDs.
      modifyThe Term.State fun state => { state with syntheticMVars := syntheticsBefore }
      return Replacement.eq replacement equality)
    (fun pfx child sub => badPosError idx pos pfx child sub)

private def materializeSourceReplacement (idx : Nat) (term : Term)
    (replacement : Replacement) : TacticM Replacement := do
  let newExpr ← instantiateMVars replacement.newExpr
  let proof? ← replacement.proof?.mapM instantiateMVars
  if newExpr.hasExprMVar || newExpr.hasLevelMVar ||
      proof?.any fun proof => proof.hasExprMVar || proof.hasLevelMVar then
    stepError idx m!"source rule `{term}` retained an unassigned metavariable after replay."
  return { newExpr, proof? }

/--
Source operands have two ordinary Lean elaboration shapes. Most can be opened
as an equation and matched directly, which is also safe below binders. A source
application with a postponed instance whose carrier is fixed only by rewrite
matching needs Lean's transactional `rw` elaborator instead. Both branches use
the same written source operand at the same exact root; neither selects another
lemma or position.
-/
private def runSourceRule (idx : Nat) (e : Expr) (pos : Pos) (term : Term)
    (reverse : Bool) (sideTacs : Array Syntax) : TacticM Replacement := do
  let saved ← Tactic.saveState
  try
    let result ← runNamedRule idx e pos term reverse sideTacs
    let result ← materializeSourceReplacement idx term result
    saved.restore
    return result
  catch _ =>
    saved.restore
    let fallbackSaved ← Tactic.saveState
    let result ← runElaboratedSourceRule idx e pos term reverse sideTacs
    let newExpr ← instantiateMVars result.newExpr
    let proof? ← result.proof?.mapM instantiateMVars
    if newExpr.hasExprMVar || proof?.any (·.hasExprMVar) then
      fallbackSaved.restore
      stepError idx m!"source rule `{term}` retained an unassigned expression metavariable after replay."
    let result := { newExpr, proof? }
    if newExpr.hasLevelMVar || proof?.any (·.hasLevelMVar) then
      -- This is the same ordinary `rw` elaboration path used for declaration
      -- rules.  A universe may be fixed only when the reconstructed equality
      -- is unified with the enclosing declaration target, so keep precisely
      -- those assignments live for the caller instead of prematurely
      -- requiring a standalone universe solution.
      return result
    fallbackSaved.restore
    return result

private def elabDeclarationEquation (idx : Nat) (name : Name) :
    TacticM (Expr × Expr × Expr × Array Expr) := do
  let info ← getConstInfo name
  let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let proof := mkConst name levels
  let type ← inferType proof
  let (mvars, _, conclusion) ← forallMetaTelescopeReducing type
  let proof := mkAppN proof mvars
  let (lhs, rhs, equality) ← asEquation idx m!"`{name}`" proof conclusion
  return (lhs, rhs, equality, mvars)

private def runDeclarationRule (idx : Nat) (e : Expr) (pos : Pos) (name : Name)
    (term : Term) (sideTacs : Array Syntax) : TacticM Replacement := do
  let probeSaved ← Tactic.saveState
  let equationMatchesRef ← IO.mkRef false
  try
    let _ ← rewriteAt e pos
      (fun sub => do
        let (lhs, _, _, _) ← elabDeclarationEquation idx name
        equationMatchesRef.set (← matchRewriteSource lhs sub)
        return Replacement.defeq sub)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  catch _ => pure ()
  probeSaved.restore
  let equationMatches ← equationMatchesRef.get
  if !equationMatches then
    return ← runNamedRule idx e pos term false sideTacs
  rewriteAt e pos
    (fun sub => do
      let (lhs, rhs, equality, mvars) ← elabDeclarationEquation idx name
      unless ← matchRewriteSource lhs sub do
        stepError idx m!"lemma `{name}` does not match the subterm at position {Pos.render pos}."
      synthesizeInstanceMVars idx m!"`{term}`" mvars sub
      let propMVars ← unassignedRewritePropMVars mvars
      if sideTacs.size > propMVars.size then
        stepError idx m!"the `with` clause supplies too many proofs for `{term}`."
      for h : proofIndex in [0 : sideTacs.size] do
        let .mvar mid := ← instantiateMVars propMVars[proofIndex]! | pure ()
        Impl.runSideProofOn idx (some proofIndex) sideTacs[proofIndex] mid
      closeLemmaMVars idx m!"`{term}`" mvars
      let rhs ← instantiateMVars rhs
      let equality ← instantiateMVars equality
      if rhs.hasLevelMVar || equality.hasLevelMVar then
        stepError idx m!"lemma `{term}` retains an unassigned universe level."
      return Replacement.eq rhs equality)
    (fun pfx child sub => badPosError idx pos pfx child sub)

private def runDeclarationRuleWithFallback (idx : Nat) (e : Expr) (pos : Pos)
    (name : Name) (term : Term) (sideTacs : Array Syntax) : TacticM Replacement := do
  let saved ← Tactic.saveState
  try
    runDeclarationRule idx e pos name term sideTacs
  catch ex =>
    let message ← ex.toMessageData.toString
    saved.restore
    unless message.contains "retains an unassigned universe level" do
      throw ex
    -- This is exactly Lean's ordinary `rw` elaboration path. Keep its
    -- metavariable state live so the enclosing declaration elaborator can
    -- resolve universe levels in the same way it does for a handwritten `rw`.
    runElaboratedSourceRule idx e pos term false sideTacs

private def runCongruenceRule (idx : Nat) (e : Expr) (pos : Pos) (term : Term)
    (indexedProofs : Array (Nat × Syntax)) : TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let (lhs, rhs, eqProof, mvars) ← Impl.elabEquation idx term
      unless ← matchRewriteSource lhs sub do
        stepError idx m!"congruence theorem `{term}` does not match the subterm at position \
          {Pos.render pos}."
      -- A congruence theorem may have target-side parameters, and therefore
      -- instances, that are determined only by its recorded equality premises.
      -- Replay those exact premises first; only then synthesize the instances
      -- fixed by the source match plus those proofs.
      for h : proofIndex in [0 : indexedProofs.size] do
        let (argumentIndex, proofStx) := indexedProofs[proofIndex]
        let some argument := mvars[argumentIndex]? | do
          stepError idx m!"congruence theorem `{term}` has no argument {argumentIndex}."
        let .mvar mid := ← instantiateMVars argument | do
          stepError idx m!"congruence theorem `{term}` argument {argumentIndex} was already \
            determined before its recorded side proof."
        unless ← isProp (← instantiateMVars (← mid.getType)) do
          stepError idx m!"congruence theorem `{term}` argument {argumentIndex} is not a proposition."
        Impl.runSideProofOn idx (some proofIndex) proofStx mid
      Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      synthesizeInstanceMVars idx m!"`{term}`" mvars sub
      Term.synthesizeSyntheticMVarsNoPostponing
      closeLemmaMVars idx m!"`{term}`" mvars
      let eqProof ← instantiateMVars eqProof
      let rhs ← instantiateMVars rhs
      if eqProof.hasLevelMVar || rhs.hasLevelMVar then
        stepError idx m!"congruence theorem `{term}` retains an unassigned universe level."
      return Replacement.eq rhs eqProof)
    (fun pfx child sub => badPosError idx pos pfx child sub)

mutual

private partial def runOne (idx : Nat) (e : Expr) (step : Syntax) : TacticM Replacement := do
  match step.getKind with
  | ``explicitRwOperationalRule => do
    let reverse ← validateRuleMetadata idx step[5] step[6]
    let sideTacs ← lowerProofs step[10]
    let decl : Ident := ⟨step[1]⟩
    -- Resolve as a global constant up front.  In particular, `rule h` cannot
    -- silently switch to a local variable when a declaration is missing.
    let declaration ← realizeGlobalConstNoOverloadWithInfo decl
    let termStx ← `(explicitRwTerm| $decl:ident)
    let term ← Impl.toTerm termStx.raw
    if reverse then
      runNamedRule idx e (withExtra (parsePos step[9]) step[8]) term reverse sideTacs
    else
      runDeclarationRuleWithFallback idx e (withExtra (parsePos step[9]) step[8])
        declaration term sideTacs
  | ``explicitRwOperationalSource => do
    let reverse ← validateRuleMetadata idx step[5] step[6]
    let sideTacs ← lowerProofs step[10]
    let term ← Impl.toTerm step[1]
    runSourceRule idx e (withExtra (parsePos step[9]) step[8]) term reverse sideTacs
  | ``explicitRwOperationalEquation => do
    let reverse ← validateRuleMetadata idx step[7] step[8]
    let sideTacs ← lowerProofs step[12]
    let decl : Ident := ⟨step[1]⟩
    let declaration ← realizeGlobalConstNoOverloadWithInfo decl
    let some equations ← getEqnsFor? declaration
      | stepError idx m!"declaration `{declaration}` has no equation theorems."
    let equationIndex := step[3].isNatLit?.getD 0
    let some theoremName := equations[equationIndex]?
      | stepError idx m!"equation index {equationIndex} is out of range for `{declaration}`."
    let theoremIdent : Ident := ⟨mkIdent theoremName⟩
    let termStx ← `(explicitRwTerm| $theoremIdent:ident)
    let term ← Impl.toTerm termStx.raw
    runNamedRule idx e
      (withExtra (parsePos step[11]) step[10]) term reverse sideTacs
  | ``explicitRwOperationalLocal => do
    let reverse ← validateRuleMetadata idx step[5] step[6]
    let sideTacs ← lowerProofs step[10]
    let hyp : Ident := ⟨step[1]⟩
    -- `getFVarId` elaborates precisely the identifier and rejects a global
    -- theorem here.  The resulting source term still carries the readable
    -- local identity; no type- or target-based context search is performed.
    let _ ← getFVarId hyp.raw
    let termStx ← `(explicitRwTerm| $hyp:ident)
    let term ← Impl.toTerm termStx.raw
    runNamedRule idx e (withExtra (parsePos step[9]) step[8]) term reverse sideTacs
  | ``explicitRwOperationalLocalRef => do
    let reverse ← validateRuleMetadata idx step[6] step[7]
    let sideTacs ← lowerProofs step[11]
    let localIndex : TSyntax `num := ⟨step[2]⟩
    let termStx ← `(explicitRwTerm| local_ref $localIndex:num)
    let term ← Impl.toTerm termStx.raw
    runNamedRule idx e (withExtra (parsePos step[10]) step[9]) term reverse sideTacs
  | ``explicitRwOperationalBeta => do
    let pos := parsePos step[1]
    Impl.runDefeqStep idx e pos m!"`beta`" fun sub => do
      let reduced := sub.headBeta
      if reduced == sub then
        stepError idx m!"`beta` at this position: the subterm is not a beta-redex."
      return reduced
  | ``explicitRwOperationalInstantiate => do
    let pos := parsePos step[1]
    -- `instantiateMVars` is itself a recorded simplifier operation. Replaying
    -- it at the exact recorded node preserves that operational boundary; it
    -- does not search for a redex or choose a theorem.
    Impl.runDefeqStep idx e pos m!"`instantiate`" instantiateMVars
  | ``explicitRwOperationalIota => do
    let pos : TSyntax ``ExplicitLean.ExplicitRw.explicitRwPos := ⟨step[1]⟩
    let legacyStep ← `(explicitRwStep| iota $pos)
    Impl.runStep idx e legacyStep.raw
  | ``explicitRwOperationalProj => do
    let pos : TSyntax ``ExplicitLean.ExplicitRw.explicitRwPos := ⟨step[1]⟩
    let legacyStep ← `(explicitRwStep| proj $pos)
    Impl.runStep idx e legacyStep.raw
  | ``explicitRwOperationalZeta => do
    let pos : TSyntax ``ExplicitLean.ExplicitRw.explicitRwPos := ⟨step[1]⟩
    let legacyStep ← `(explicitRwStep| zeta $pos)
    Impl.runStep idx e legacyStep.raw
  | ``explicitRwOperationalZetaLocal => do
    let reason := step[3].getId.toString
    unless reason == "zetaDelta" || reason == "requested" ||
        reason == "implementationDetail" do
      stepError idx m!"unknown local-definition reduction reason `{reason}`."
    let localIndex : TSyntax `num := ⟨step[2]⟩
    let pos : TSyntax ``ExplicitLean.ExplicitRw.explicitRwPos := ⟨step[4]⟩
    let legacyStep ← `(explicitRwStep| zeta_local local_ref $localIndex:num $pos)
    Impl.runStep idx e legacyStep.raw
  | ``explicitRwOperationalFoldNatLit => do
    let pos := parsePos step[1]
    Impl.runDefeqStep idx e pos m!"`fold_nat_lit`" fun sub => do
      let some value := sub.rawNatLit?
        | stepError idx m!"`fold_nat_lit` at this position requires a raw natural-number literal."
      return toExpr value
  | ``explicitRwOperationalUnfold => do
    let c ← realizeGlobalConstNoOverloadWithInfo step[1]
    let pos := parsePos step[2]
    Impl.runDefeqStep idx e pos m!"`unfold {c}`" (Impl.unfoldConst idx c)
  | ``explicitRwOperationalCached => do
    let steps := step[2].getSepArgs
    if steps.isEmpty then
      stepError idx m!"a changed simp cache result must name its producing operations."
    let pos := parsePos step[4]
    rewriteAt e pos
      (fun sub => runOperationsAt steps sub)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwOperationalCongruence => do
    let decl : Ident := ⟨step[1]⟩
    let _ ← realizeGlobalConstNoOverloadWithInfo decl
    let termStx ← `(explicitRwTerm| $decl:ident)
    let term ← Impl.toTerm termStx.raw
    let pos := parsePos step[2]
    let mut indexedProofs : Array (Nat × Syntax) := #[]
    for entry in step[5].getSepArgs do
      let argumentIndex := entry[1].isNatLit?.getD 0
      if indexedProofs.any (·.1 == argumentIndex) then
        stepError idx m!"congruence theorem `{decl.getId}` repeats argument {argumentIndex}."
      indexedProofs := indexedProofs.push (argumentIndex, ← lowerProof entry[2])
    indexedProofs := indexedProofs.qsort fun a b => a.1 < b.1
    runCongruenceRule idx e pos term indexedProofs
  | ``explicitRwOperationalAutoCongruence => do
    let pos := parsePos step[1]
    let mut indexedSteps : Array (Nat × Array Syntax) := #[]
    for entry in step[4].getSepArgs do
      let argumentIndex := entry[1].isNatLit?.getD 0
      if indexedSteps.any (·.1 == argumentIndex) then
        stepError idx m!"automatic congruence repeats argument {argumentIndex}."
      indexedSteps := indexedSteps.push (argumentIndex, entry[3].getSepArgs)
    indexedSteps := indexedSteps.qsort fun a b => a.1 < b.1
    rewriteAt e pos
      (fun sub => do
        let fn := sub.getAppFn
        let args := sub.getAppArgs
        let some congrThm ← Lean.Meta.mkCongrSimp? fn
          | stepError idx m!"`auto_congr`: no simp congruence theorem could be generated for the head{indentExpr fn}"
        unless congrThm.argKinds.size == args.size do
          stepError idx m!"`auto_congr`: the generated theorem has {congrThm.argKinds.size} argument kind(s), but the selected application has {args.size} argument(s)."
        let mut argsNew := args
        let mut replacements : Array (Nat × Replacement) := #[]
        for (argumentIndex, childSteps) in indexedSteps do
          let some kind := congrThm.argKinds[argumentIndex]?
            | stepError idx m!"`auto_congr`: the selected application has no argument {argumentIndex}."
          unless kind == .fixed || kind == .eq do
            stepError idx m!"`auto_congr`: argument {argumentIndex} has generated congruence kind `{repr kind}`, which has no recursive operation program."
          let replacement ← runOperationsAt childSteps args[argumentIndex]!
          argsNew := argsNew.set! argumentIndex (← instantiateMVars replacement.newExpr)
          replacements := replacements.push (argumentIndex, replacement)
        let replacementAt? (argumentIndex : Nat) : Option Replacement :=
          (replacements.find? fun item => item.1 == argumentIndex).map (·.2)
        let mut proof := congrThm.proof
        let mut type := congrThm.type
        let mut subst : Array Expr := #[]
        for h : argumentIndex in [0 : args.size] do
          let argument := args[argumentIndex]
          let argumentNew := argsNew[argumentIndex]!
          let kind := congrThm.argKinds[argumentIndex]!
          proof := mkApp proof argument
          type := type.bindingBody!
          match kind with
          | .fixed =>
            subst := subst.push argumentNew
          | .cast =>
            subst := subst.push argument
          | .subsingletonInst =>
            subst := subst.push argument
            let clsNew := type.bindingDomain!.instantiateRev subst
            let instNew ← if ← isDefEq (← inferType argument) clsNew then
              pure argument
            else
              match ← trySynthInstance clsNew with
              | LOption.some value => pure value
              | _ => stepError idx m!"`auto_congr`: failed to synthesize the transported subsingleton instance for argument {argumentIndex}."
            proof := mkApp proof instNew
            subst := subst.push instNew
            type := type.bindingBody!
          | .eq =>
            subst := subst.push argument
            let argProof ← match replacementAt? argumentIndex with
              | some replacement => match replacement.proof? with
                | some equality => instantiateMVars equality
                | none => mkEqRefl argument
              | none => mkEqRefl argument
            proof := mkApp2 proof argumentNew argProof
            subst := subst.push argumentNew |>.push argProof
            type := type.bindingBody!.bindingBody!
          | other =>
            stepError idx m!"`auto_congr`: the generated theorem uses unsupported argument kind `{repr other}` at argument {argumentIndex}."
        let some (_, _, rhs) := type.instantiateRev subst |>.eq?
          | stepError idx m!"`auto_congr`: the generated theorem did not produce an equality."
        let rhs ← Simp.removeUnnecessaryCasts rhs
        let proofFinal ← instantiateMVars proof
        let rhs ← instantiateMVars rhs
        let proofType ← inferType proofFinal
        let expected ← mkEq sub rhs
        unless ← isDefEq proofType expected do
          stepError idx m!"`auto_congr`: the generated congruence proof does not establish the reconstructed application equality."
        return Replacement.eq rhs proofFinal)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwOperationalForallCongruence => do
    let pos := parsePos step[1]
    let domainSteps := step[4].getSepArgs
    let bodySteps := step[8].getSepArgs
    rewriteAt e pos
      (fun sub => do
        let .forallE binderName binderType binderBody binderInfo := sub
          | stepError idx m!"`forall_congr` at position {Pos.render pos} requires a `∀`"
        let domainReplacement ← runOperationsAt domainSteps binderType
        let newDomain ← instantiateMVars domainReplacement.newExpr
        match domainReplacement.proof? with
        | some domainEquality =>
          withLocalDecl `__explicit_rw_v2_forall_bound binderInfo newDomain fun x => do
            let castArg ← mkAppM ``Eq.mp #[← mkEqSymm domainEquality, x]
            let bodySeed := binderBody.instantiate1 castArg
            let bodyReplacement ← runOperationsAt bodySteps bodySeed
            dependentForallTransport binderName binderInfo binderType binderBody
              domainReplacement (some x) (some bodyReplacement)
        | none =>
          withLocalDecl `__explicit_rw_v2_forall_bound binderInfo newDomain fun x => do
            let bodyReplacement ←
              runOperationsAt bodySteps (binderBody.instantiate1 x)
            let bodyLambda ← mkLambdaFVars #[x] bodyReplacement.newExpr
            let .lam _ _ newBody _ := bodyLambda
              | stepError idx m!"`forall_congr` failed to abstract its body"
            let newForall := .forallE binderName newDomain newBody binderInfo
            match bodyReplacement.proof? with
            | none => return Replacement.defeq newForall
            | some bodyEquality =>
              let proofLambda ← mkLambdaFVars #[x] bodyEquality
              return Replacement.eq newForall (← mkForallCongr proofLambda))
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwOperationalSimproc =>
    throwError "explicit_rw_v2: simproc `{step[1].getId}` is not a rewrite-rule operation."
  | k =>
    throwError "explicit_rw_v2: internal error: unexpected operation kind `{k}`"

private partial def runOperationsAt (steps : Array Syntax) (e : Expr) : TacticM Replacement := do
  let mut current := e
  let mut proof? : Option Expr := none
  for h : idx in [0 : steps.size] do
    let step := steps[idx]
    let replacement ←
      try
        runOne idx current step
      catch ex => do
        let msg ← ex.toMessageData.toString
        if msg.startsWith "explicit_rw_v2:" then
          throw ex
        else if msg.startsWith "explicit_rw:" then
          throwError "explicit_rw_v2:{msg.drop 12}"
        else
          throwError "explicit_rw_v2: step {idx + 1}: {msg}"
    let newE ← instantiateMVars replacement.newExpr
    match proof?, replacement.proof? with
    | none, p => proof? := p
    | some p, none => pure ()
    | some p, some q => proof? := some (← mkEqTrans p (← instantiateMVars q))
    current := newE
  return { newExpr := current, proof? := proof? }

end

private structure Target where
  fvarId : FVarId

private def runOperations (steps : Array Syntax) (target : Option Target)
    (closeLocalFalse : Bool) :
    TacticM (Option Target) := do
  let goal ← getMainGoal
  goal.withContext do
    let initial ← match target with
      | none => instantiateMVars (← goal.getType)
      | some target => instantiateMVars (← target.fvarId.getType)
    let replacement ← runOperationsAt steps initial
    let newExpr ← instantiateMVars replacement.newExpr
    if closeLocalFalse then
      let some target := target
        | throwError "explicit_rw_v2: `false_elim` requires a hypothesis location."
      unless newExpr.isFalse do
        throwError "explicit_rw_v2: `false_elim` expected the selected hypothesis to simplify to False."
      let falseProof ← match replacement.proof? with
        | none => pure (mkFVar target.fvarId)
        | some proof => mkEqMP (← instantiateMVars proof) (mkFVar target.fvarId)
      goal.assign (← mkFalseElim (← goal.getType) falseProof)
      replaceMainGoal []
      return none
    match target, replacement.proof? with
    | none, none =>
      replaceMainGoal [← goal.replaceTargetDefEq newExpr]
      return none
    | none, some proof =>
      replaceMainGoal [← goal.replaceTargetEq newExpr (← instantiateMVars proof)]
      return none
    | some target, none =>
      replaceMainGoal [← goal.replaceLocalDeclDefEq target.fvarId newExpr]
      return some target
    | some target, some proof =>
      let proof ← instantiateMVars proof
      -- Use Lean's dependency-aware local rewrite primitive. Constructing a
      -- replacement proof and calling `MVarId.replace` directly leaves later
      -- local declarations referring to the retired free-variable identity
      -- after sequential `at *` subjects.
      let result ← goal.replaceLocalDecl target.fvarId newExpr proof
      replaceMainGoal [result.mvarId]
      return some { target with fvarId := result.fvarId }

private def resolveTarget (locStx : Syntax) : TacticM (Option Target) := do
  if locStx.isNone then return none
  let loc := locStx[0]
  match loc.getKind with
  | ``explicitRwOperationalLocationIdent => do
    let fvarId ← getFVarId loc[1]
    return some { fvarId }
  | ``explicitRwOperationalLocationRef =>
    let index ← Impl.checkedHandle loc[2] "location local_ref index"
    return some { fvarId := (← Impl.indexedLocalDecl index).fvarId }
  | kind =>
    throwError "explicit_rw_v2: internal error: unknown location `{kind}`."

private def runTerminal (stx : Syntax) (target : Option Target) : TacticM Unit := do
  let close := stx[0]
  match close.getKind with
  | ``explicitRwOperationalClose =>
    if target.isSome then
      throwError "explicit_rw_v2: this terminal operation applies only to the goal, not a hypothesis."
    let closer ← lowerProof close[1]
    Impl.runCloser closer
  | kind =>
    throwError "explicit_rw_v2: internal error: unknown terminal operation `{kind}`."

private def isFalseElimTerminal (stx : Syntax) : Bool :=
  if stx.isNone then
    false
  else
    let close := stx[0]
    close.getKind == ``explicitRwOperationalCloseFalseElim ||
      (close.getNumArgs > 0 && close[0].getKind == ``explicitRwOperationalCloseFalseElim) ||
      (close.getNumArgs > 1 && close[1].getKind == ``explicitRwOperationalCloseFalseElim)

end Operational

@[tactic explicitRwOperational]
public meta def evalExplicitRwOperational : Tactic := fun stx => do
  let steps := stx[2].getSepArgs
  let target ← Operational.resolveTarget stx[4]
  let closeLocalFalse := Operational.isFalseElimTerminal stx[5]
  let target ← Operational.runOperations steps target closeLocalFalse
  unless stx[5].isNone do
    unless closeLocalFalse do
      Operational.runTerminal stx[5] target

@[tactic explicitRwOperationalGoals]
public meta def evalExplicitRwOperationalGoals : Tactic := fun stx => do
  let programs := stx[2].getSepArgs
  let goals ← getGoals
  unless programs.size == goals.length do
    throwError "explicit_rw_v2_goals: recorded {programs.size} invocation(s), but the preceding tactic produced {goals.length} goal(s)."
  let mut remaining : Array MVarId := #[]
  for h : i in [0 : programs.size] do
    let program := programs[i]
    unless program.getKind == ``explicitRwOperationalProofNested do
      throwError "explicit_rw_v2_goals: internal error: expected a closed explicit_rw_v2 program."
    let nested : TSyntax `tactic := ⟨mkNode ``explicitRwOperational #[
      program[0], program[1], program[2], program[3], mkNullNode #[], program[4]
    ]⟩
    remaining := remaining ++ (← Tactic.run goals[i]! (evalTactic nested))
  setGoals remaining.toList

end ExplicitLean.ExplicitRw
