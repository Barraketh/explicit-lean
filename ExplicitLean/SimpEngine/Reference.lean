module

public meta import ExplicitLean.SimpEngine

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

syntax simpEngineReferenceArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?

syntax (name := simpEngineReference)
  "simp_engine_reference" simpEngineReferenceArgs : tactic

syntax (name := simpEngineReferenceAssignedMVar)
  "simp_engine_reference_assigned_mvar" : tactic

syntax dsimpEngineReferenceArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpErase <|> simpLemma),*,?) "]")? (location)?

syntax (name := dsimpEngineReference)
  "dsimp_engine_reference" dsimpEngineReferenceArgs : tactic

end Lean.Parser.Tactic

namespace ExplicitLean.SimpEngine.Reference

private def originKey : Origin → MetaM String
  | .decl name post inverse => return s!"decl:{name}:{post}:{inverse}"
  | .fvar fvarId => do
      if let some decl := (← getLCtx).find? fvarId then
        return s!"fvar:ambient:{decl.index}"
      else
        return "fvar:scoped"
  | .stx id ref => return s!"stx:{id}:{toString ref.prettyPrint}"
  | .other name => return s!"other:{name}"

private def originCounterKey (counter : PHashMap Origin Nat) : MetaM (Array String) := do
  let entries ← counter.toArray.mapM fun (origin, count) => do
    return s!"{← originKey origin}:{count}"
  return entries.qsort (· < ·)

private def nameCounterKey (counter : PHashMap Name Nat) : Array String :=
  counter.toArray.map (fun (name, count) => s!"{name}:{count}")
    |>.qsort (· < ·)

private def theoremArrayKey (theorems : Simp.UsedSimps) : MetaM (Array String) := do
  let entries ← theorems.toArray.mapM originKey
  return entries.qsort (· < ·)

private structure ReferenceSummary where
  expr : Expr
  proofPresent : Bool
  cache : Bool
  numSteps : Nat
  cacheEntries : Nat
  congrCacheEntries : Nat
  dsimpCacheEntries : Nat
  badKeyCount : Nat
  usedTheorems : Array String
  triedTheorems : Array String
  usedTheoremCounts : Array String
  congrTheorems : Array String

private def summarize (target : Expr) (result : Simp.Result)
    (state : Simp.State) : MetaM ReferenceSummary := do
  let expr ← instantiateMVars result.expr
  unless ← isTypeCorrect expr do
    throwError "pinned simp engine produced an ill-typed expression{indentExpr expr}"
  if expr.hasMVar then
    throwError "pinned simp engine result retained metavariables{indentExpr expr}"
  if let some proof := result.proof? then
    let proof ← instantiateMVars proof
    unless ← isTypeCorrect proof do
      throwError "pinned simp engine produced an ill-typed proof{indentExpr proof}"
    if proof.hasMVar then
      throwError "pinned simp engine proof retained metavariables{indentExpr proof}"
    let proofType ← inferType proof
    let expectedType ← mkEq target expr
    unless ← isDefEq proofType expectedType do
      throwError "pinned simp engine proof has the wrong type\nactual:{indentExpr proofType}\nexpected:{indentExpr expectedType}"
  return {
    expr
    proofPresent := result.proof?.isSome
    cache := result.cache
    numSteps := state.numSteps
    cacheEntries := state.cache.toList.length
    congrCacheEntries := state.congrCache.size
    dsimpCacheEntries := state.dsimpCache.size
    badKeyCount := state.diag.thmsWithBadKeys.size
    usedTheorems := ← theoremArrayKey state.usedTheorems
    triedTheorems := ← originCounterKey state.diag.triedThmCounter
    usedTheoremCounts := ← originCounterKey state.diag.usedThmCounter
    congrTheorems := nameCounterKey state.diag.congrThmCounter
  }

private def assertReferenceEqual (upstream fork : ReferenceSummary) : TacticM Unit := do
  unless Expr.equal upstream.expr fork.expr do
    throwError "pinned simp engine expression mismatch\nupstream:{indentExpr upstream.expr}\nfork:{indentExpr fork.expr}"
  unless upstream.proofPresent == fork.proofPresent do
    throwError "pinned simp engine proof-presence mismatch: upstream={upstream.proofPresent}, fork={fork.proofPresent}"
  unless upstream.cache == fork.cache do
    throwError "pinned simp engine cache-flag mismatch: upstream={upstream.cache}, fork={fork.cache}"
  unless upstream.numSteps == fork.numSteps do
    throwError "pinned simp engine step-count mismatch: upstream={upstream.numSteps}, fork={fork.numSteps}"
  unless upstream.cacheEntries == fork.cacheEntries do
    throwError "pinned simp engine result-cache mismatch: upstream={upstream.cacheEntries}, fork={fork.cacheEntries}"
  unless upstream.congrCacheEntries == fork.congrCacheEntries do
    throwError "pinned simp engine congruence-cache mismatch: upstream={upstream.congrCacheEntries}, fork={fork.congrCacheEntries}"
  unless upstream.dsimpCacheEntries == fork.dsimpCacheEntries do
    throwError "pinned simp engine dsimp-cache mismatch: upstream={upstream.dsimpCacheEntries}, fork={fork.dsimpCacheEntries}"
  unless upstream.badKeyCount == fork.badKeyCount do
    throwError "pinned simp engine bad-index-key mismatch: upstream={upstream.badKeyCount}, fork={fork.badKeyCount}"
  unless upstream.usedTheorems == fork.usedTheorems do
    throwError "pinned simp engine used-theorem mismatch\nupstream={upstream.usedTheorems}\nfork={fork.usedTheorems}"
  unless upstream.triedTheorems == fork.triedTheorems do
    throwError "pinned simp engine tried-theorem mismatch\nupstream={upstream.triedTheorems}\nfork={fork.triedTheorems}"
  unless upstream.usedTheoremCounts == fork.usedTheoremCounts do
    throwError "pinned simp engine theorem-count mismatch\nupstream={upstream.usedTheoremCounts}\nfork={fork.usedTheoremCounts}"
  unless upstream.congrTheorems == fork.congrTheorems do
    throwError "pinned simp engine congruence-count mismatch\nupstream={upstream.congrTheorems}\nfork={fork.congrTheorems}"

private def checkReferenceTarget (simpStx : Syntax) (target : Expr) : TacticM Unit := do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  let initialMeta ← Meta.saveState
  let initialGoals ← getGoals
  let (upstream, fork) ← dischargeWrapper.with fun discharge? => do
    let upstreamMethods := match discharge? with
      | none => Simp.mkDefaultMethodsCore simprocs
      | some discharge => Simp.mkMethods simprocs discharge (wellBehavedDischarge := false)
    let forkMethods := match discharge? with
      | none => Simp.Engine.mkDefaultMethodsCore simprocs
      | some discharge => Simp.Engine.mkMethods simprocs discharge (wellBehavedDischarge := false)
    let upstreamResult ← withOptions (·.setBool `diagnostics true) do
      let (result, state) ← Simp.mainCore target ctx (methods := upstreamMethods)
      summarize target result state
    initialMeta.restore
    setGoals initialGoals
    let forkResult ← withOptions (·.setBool `diagnostics true) do
      let (result, state) ← Simp.Engine.mainCore target ctx (methods := forkMethods)
      summarize target result state
    return (upstreamResult, forkResult)
  initialMeta.restore
  setGoals initialGoals
  assertReferenceEqual upstream fork

private def checkReference (simpStx : Syntax) : TacticM Unit := withMainContext do
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  checkReferenceTarget simpStx target

private def checkDSimpReference (dsimpStx : Syntax) : TacticM Unit := withMainContext do
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext dsimpStx (eraseLocal := false)
  let initialMeta ← Meta.saveState
  let initialGoals ← getGoals
  let (upstream, fork) ← dischargeWrapper.with fun discharge? => do
    let upstreamMethods := match discharge? with
      | none => Simp.mkDefaultMethodsCore simprocs
      | some discharge => Simp.mkMethods simprocs discharge (wellBehavedDischarge := false)
    let forkMethods := match discharge? with
      | none => Simp.Engine.mkDefaultMethodsCore simprocs
      | some discharge => Simp.Engine.mkMethods simprocs discharge (wellBehavedDischarge := false)
    let upstreamResult ← withOptions (·.setBool `diagnostics true) do
      let (expr, state) ← Simp.dsimpMainCore target ctx (methods := upstreamMethods)
      summarize target { expr } state
    initialMeta.restore
    setGoals initialGoals
    let forkResult ← withOptions (·.setBool `diagnostics true) do
      let (expr, state) ← Simp.Engine.dsimpMainCore target ctx (methods := forkMethods)
      summarize target { expr } state
    return (upstreamResult, forkResult)
  initialMeta.restore
  setGoals initialGoals
  assertReferenceEqual upstream fork

elab_rules : tactic
  | `(tactic| simp_engine_reference $args:simpEngineReferenceArgs) => do
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      checkReference inner
      evalTactic inner
  | `(tactic| simp_engine_reference_assigned_mvar) => withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let assigned ← mkFreshExprMVar (mkSort .zero)
      assigned.mvarId!.assign target
      let inner ← `(tactic| simp)
      checkReferenceTarget inner assigned
  | `(tactic| dsimp_engine_reference $args:dsimpEngineReferenceArgs) => do
      let inner := mkNode ``Lean.Parser.Tactic.dsimp #[
        mkAtom "dsimp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      checkDSimpReference inner
      evalTactic inner

end ExplicitLean.SimpEngine.Reference
