/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Pinned reference fork for Explicit Lean.
Upstream: Lean 4.32.2, f3b06c705e6c85f5314019d5d3baab0fec5b580c.
-/
module
prelude
public import Lean.Elab.Tactic.Simp
import Lean.Meta.HaveTelescope
public section
namespace Lean.Meta
namespace Simp.Engine

open Simp

/- Nesting the fork under `Lean.Meta.Simp` preserves upstream unqualified-name
   resolution while giving every copied execution function a distinct name. -/

set_option compiler.ignoreBorrowAnnotation true in
@[extern "explicit_lean_simp_engine"]
opaque simp (e : Expr) : SimpM Result

set_option compiler.ignoreBorrowAnnotation true in
@[extern "explicit_lean_dsimp_engine"]
opaque dsimp (e : Expr) : SimpM Expr

/-- Return true if `e` is of the form `ofNat n` where `n` is a kernel Nat literal -/
def isOfNatNatLit (e : Expr) : Bool :=
  e.isAppOf ``OfNat.ofNat && e.getAppNumArgs >= 3 && (e.getArg! 1).isRawNatLit

/--
If `e` is a raw Nat literal and `OfNat.ofNat` is not in the list of declarations to unfold,
return an `OfNat.ofNat`-application.
-/
def foldRawNatLit (e : Expr) : SimpM Expr := do
  match e.rawNatLit? with
  | some n =>
    /- If `OfNat.ofNat` is marked to be unfolded, we do not pack orphan nat literals as `OfNat.ofNat` applications
        to avoid non-termination. See issue #788.  -/
    if (← readThe Simp.Context).isDeclToUnfold ``OfNat.ofNat then
      return e
    else
      return toExpr n
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

private def reduceProjFn? (e : Expr) : SimpM (Option Expr) := do
  matchConst e.getAppFn (fun _ => pure none) fun cinfo _ => do
    match (← getProjectionFnInfo? cinfo.name) with
    | none => return none
    | some projInfo =>
      /- Helper function for applying `reduceProj?` to the result of `unfoldDefinition?` -/
      let reduceProjCont? (e? : Option Expr) : SimpM (Option Expr) := do
        match e? with
        | none   => pure none
        | some e =>
          match (← withSimpMetaConfig <| reduceProj? e.getAppFn) with
          | some f => return some (mkAppN f e.getAppArgs)
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
          return e?
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
            unfoldDefinitionAny? e
          else
            reduceProjCont? (← unfoldDefinitionAny? e)
      else
        -- `structure` projections
        reduceProjCont? (← unfoldDefinition? e)

private def reduceFVar (cfg : Config) (thms : SimpTheoremsArray) (e : Expr) : SimpM Expr := do
  let localDecl ← getFVarLocalDecl e
  if cfg.zetaDelta || thms.isLetDeclToUnfold e.fvarId! || localDecl.isImplementationDetail then
    if !cfg.zetaDelta && thms.isLetDeclToUnfold e.fvarId! then
      recordSimpTheorem (.fvar localDecl.fvarId)
    let some v := localDecl.value? | return e
    return v
  else
    return e

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
private def unfold? (e : Expr) : SimpM (Option Expr) := do
  let f := e.getAppFn
  if !f.isConst then
    return none
  let fName := f.constName!
  let ctx ← getContext
  let rec unfoldDeclToUnfold? : SimpM (Option Expr) := do
    let options ← getOptions
    let cfg ← getConfig
    -- Support for issue #2042
    if cfg.unfoldPartialApp -- If we are unfolding partial applications, ignore issue #2042
       -- When smart unfolding is enabled, and `f` supports it, we don't need to worry about issue #2042
       || (smartUnfolding.get options && (← getEnv).contains (mkSmartUnfoldingNameFor fName)) then
      unfoldDefinitionAny? e
    else
      -- We are not unfolding partial applications, and `fName` does not have smart unfolding support.
      -- Thus, we must check whether the arity of the function >= number of arguments.
      let some cinfo := (← getEnv).find? fName | return none
      let some value := cinfo.value? | return none
      let arity := value.getNumHeadLambdas
      -- Partially applied function, return `none`. See issue #2042
      if arity > e.getAppNumArgs then return none
      unfoldDefinitionAny? e
  if (← isProjectionFn fName) then
    return none -- should be reduced by `reduceProjFn?`
  else if ctx.config.autoUnfold then
    if ctx.simpTheorems.isErased (.decl fName) then
      return none
    else if hasSmartUnfoldingDecl (← getEnv) fName then
      unfoldDefinitionAny? e
    else if (← isMatchDef fName) then
      let some value ← unfoldDefinitionAny? e | return none
      let .reduced value ← withSimpMetaConfig <| reduceMatcher? value | return none
      return some value
    else
      return none
  else if ctx.isDeclToUnfold fName then
    unfoldDeclToUnfold?
  else
    return none

private def reduceStep (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  let f := e.getAppFn
  if f.isMVar then
    return (← instantiateMVars e)
  withSimpMetaConfig do
  if cfg.beta then
    if f.isHeadBetaTargetFn false then
      return f.betaRev e.getAppRevArgs
  -- TODO: eta reduction
  if cfg.proj then
    match (← reduceProj? e) with
    | some e => return e
    | none =>
    match (← reduceProjFn? e) with
    | some e => return e
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some e => return e
    | none   => pure ()
  if let .letE _ _ v b nondep := e then
    if cfg.zeta && (!nondep || cfg.zetaHave) then
      return expandLet b #[v] (zetaHave := cfg.zetaHave)
    else if cfg.zetaUnused && !b.hasLooseBVars then
      return consumeUnusedLet b
  match (← unfold? e) with
  | some e' =>
    trace[Meta.Tactic.simp.rewrite] "unfold {.ofConst e.getAppFn}, {e} ==> {e'}"
    recordSimpTheorem (.decl e.getAppFn.constName!)
    return e'
  | none => foldRawNatLit e

private partial def reduce (e : Expr) : SimpM Expr := withIncRecDepth do
  let e' ← reduceStep e
  if e' == e then
    return e'
  else
    trace[Debug.Meta.Tactic.simp] "reduce {e} => {e'}"
    reduce e'

local instance : Inhabited (SimpM α) where
  default := fun _ _ _ => default

partial def lambdaTelescopeDSimp (e : Expr) (k : Array Expr → Expr → SimpM α) : SimpM α := do
  go #[] e
where
  go (xs : Array Expr) (e : Expr) : SimpM α := do
    match e with
    | .lam n d b c => withLocalDecl n c (← dsimp d) fun x => go (xs.push x) (b.instantiate1 x)
    | e => k xs e

/--
We use `withNewLemmas` whenever updating the local context.
-/
def withNewLemmas {α} (xs : Array Expr) (f : SimpM α) : SimpM α := do
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
        withSimpTheorems s f
      else
        f
  else if (← getMethods).wellBehavedDischarge then
    -- See comment at `Methods.wellBehavedDischarge` to understand why
    -- we don't have to reset the cache
    f
  else
    withFreshCache do f

local instance : MonadSimp SimpM where
  simp e := do
    let r ← simp e
    if r.expr == e then
      return .rfl
    else
      return .step r.expr (← r.getProof)
  dsimp := dsimp
  withNewLemmas := withNewLemmas

/--
Given a simplified function result `r` and arguments `args`, simplify arguments using `simp` and `dsimp`.
The resulting proof is built using `congr` and `congrFun` theorems.
-/
def congrArgs (r : Result) (args : Array Expr) : SimpM Result := do
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
          r ← mkCongr r (← simp arg)
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← mkCongr r (← simp arg)
        else
          r ← mkCongrFun r (← dsimp arg)
      else if (← whnfD (← inferType r.expr)).isArrow then
        r ← mkCongr r (← simp arg)
      else
        r ← mkCongrFun r (← dsimp arg)
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
def simpAppUsingCongr (e : Expr) : SimpM Result := do
  let f := e.getAppFn
  let numArgs := e.getAppNumArgs
  let cfg ← getConfig
  let infos := (← getFunInfoNArgs f numArgs).paramInfo
  let rec visit (e : Expr) (i : Nat) : SimpM Result := do
    if i == 0 then
      simp f
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
          mkCongr' e fr (← simp a)
        else if (← whnfD (← inferType f)).isArrow then
          mkCongr' e fr (← simp a)
        else
          mkCongrFun' e fr (← dsimp a)
      else if (← whnfD (← inferType f)).isArrow then
        mkCongr' e fr (← simp a)
      else
        mkCongrFun' e fr (← dsimp a)
  visit e numArgs


/--
Try to use automatically generated congruence theorems. See `mkCongrSimp?`.
-/
def tryAutoCongrTheorem? (e : Expr) : SimpM (Option Result) := do
  let f := e.getAppFn
  -- TODO: cache
  let some cgrThm ← Simp.mkCongrSimp? f | return none
  if cgrThm.argKinds.size != e.getAppNumArgs then return none
  let args := e.getAppArgs
  let infos := (← getFunInfoNArgs f args.size).paramInfo
  let config ← getConfig
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
      let argNew ← dsimp arg
      if arg != argNew then
        simplified := true
      argsNew := argsNew.push argNew
    | CongrArgKind.cast  => hasCast := true; argsNew := argsNew.push arg
    | CongrArgKind.subsingletonInst => argsNew := argsNew.push arg
    | CongrArgKind.eq =>
      let argResult ← simp arg
      argResults := argResults.push argResult
      argsNew    := argsNew.push argResult.expr
      if argResult.proof?.isSome then hasProof := true
      if arg != argResult.expr then simplified := true
    | _ => unreachable!
    i := i + 1
  if !simplified then return some { expr := e }
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
  if hasProof then
    return some { expr := rhs, proof? := proof }
  else
    /- See comment above. This is reachable if `hasCast == true`. The `rhs` is not structurally equal to `mkAppN f argsNew` -/
    return some { expr := rhs }

def simpProj (e : Expr) : SimpM Result := do
  match (← withSimpMetaConfig <| reduceProj? e) with
  | some e => return { expr := e }
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
      let r ← simp s
      let eNew := e.updateProj! r.expr
      match r.proof? with
      | none => return { expr := eNew }
      | some h =>
        let hNew ← mkEqNDRec motive (← mkEqRefl e) h
        return { expr := eNew, proof? := some hNew }
    else
      return { expr := (← dsimp e) }

def simpConst (e : Expr) : SimpM Result :=
  return { expr := (← reduce e) }

def simpLambda (e : Expr) : SimpM Result :=
  withParent e <| lambdaTelescopeDSimp e fun xs e => withNewLemmas xs do
    let r ← simp e
    r.addLambdas xs

def simpArrow (e : Expr) : SimpM Result := do
  trace[Debug.Meta.Tactic.simp] "arrow {e}"
  let p := e.bindingDomain!
  let q := e.bindingBody!
  let rp ← simp p
  trace[Debug.Meta.Tactic.simp] "arrow [{(← getConfig).contextual}] {p} [{← isProp p}] -> {q} [{← isProp q}]"
  if (← pure (← getConfig).contextual <&&> isProp p <&&> isProp q) then
    trace[Debug.Meta.Tactic.simp] "ctx arrow {rp.expr} -> {q}"
    withLocalDeclD e.bindingName! rp.expr fun h => withNewLemmas #[h] do
      let rq ← simp q
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
    mkImpCongr e rp (← simp q)

def simpForall (e : Expr) : SimpM Result := withParent e do
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
      let rd ← simp domain
      if let some h₁ := rd.proof? then
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
          let rb ← simp q_h₁_substr_a
          let h₂ ← mkLambdaFVars #[a] (← rb.getProof)
          let q₂ ← mkLambdaFVars #[a] rb.expr
          let result ← mkForallFVars #[a] rb.expr
          let proof := mkApp6 (mkConst ``forall_prop_domain_congr) p₁ p₂ q₁ q₂ h₁ h₂
          return { expr := result, proof? := proof }
        return result
    let domain ← dsimp domain
    withLocalDecl e.bindingName! e.bindingInfo! domain fun x => withNewLemmas #[x] do
      let b := e.bindingBody!.instantiate1 x
      let rb ← simp b
      let eNew ← mkForallFVars #[x] rb.expr
      match rb.proof? with
      | none   => return { expr := eNew }
      | some h => return { expr := eNew, proof? := (← mkForallCongr (← mkLambdaFVars #[x] h)) }
  else
    return { expr := (← dsimp e) }

/-- Adapter for `Meta.simpHaveTelescope` -/
def simpHaveTelescope (e : Expr) : SimpM Result := do
  -- **Note**: Eliminating unused-let declarations in a single pass may produce O(n^2) proofs.
  let zetaUnusedMode := if (← getConfig).zetaUnused then .singlePass else .no
  match (← Meta.simpHaveTelescope e zetaUnusedMode) with
  | .rfl => return { expr := e }
  | .step e' h =>
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
def simpLet (e : Expr) : SimpM Result := do
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

set_option compiler.ignoreBorrowAnnotation true in
@[export explicit_lean_dsimp_engine]
private partial def dsimpImpl (e : Expr) : SimpM Expr := do
  let cfg ← getConfig
  unless cfg.dsimp do
    return e
  let m ← getMethods
  let pre := m.dpre >> doNotVisitOfNat >> doNotVisitOfScientific >> doNotVisitCharLit >> doNotVisitProofs
  let post := m.dpost >> dsimpReduce
  withInDSimpWithCache fun cache => do
    transformWithCache e cache
      (usedLetOnly := cfg.zeta || cfg.zetaUnused)
      (skipInstances := !cfg.instances)
      (pre := pre)
      (post := post)

def visitFn (e : Expr) : SimpM Result := do
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

def congrDefault (e : Expr) : SimpM Result := do
  if let some result ← tryAutoCongrTheorem? e then
    result.mkEqTrans (← visitFn result.expr)
  else
    withParent e <| simpAppUsingCongr e

/-- Process the given congruence theorem hypothesis. Return true if it made "progress". -/
def processCongrHypothesis (h : Expr) (hType : Expr) : SimpM Bool := do
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

/-- Try to rewrite `e` children using the given congruence theorem -/
def trySimpCongrTheorem? (c : SimpCongrTheorem) (e : Expr) : SimpM (Option Result) := withNewMCtxDepth do withParent e do
  recordCongrTheorem c.theoremName
  trace[Debug.Meta.Tactic.simp.congr] "{c.theoremName}, {e}"
  let thm ← mkConstWithFreshMVarLevels c.theoremName
  let thmType ← inferType thm
  let thmHasBinderNameHint := thmType.hasBinderNameHint
  let (xs, bis, type) ← forallMetaTelescopeReducing thmType
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
        if (← processCongrHypothesis h hType) then
          modified := true
      catch _ =>
        trace[Meta.Tactic.simp.congr] "processCongrHypothesis {c.theoremName} failed {hType}"
        -- Remark: we don't need to check ex.isMaxRecDepth anymore since `try .. catch ..`
        -- does not catch runtime exceptions by default.
        return none
    unless modified do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} not modified"
      return none
    unless (← synthesizeArgs (.decl c.theoremName) bis xs) do
      trace[Meta.Tactic.simp.congr] "{c.theoremName} synthesizeArgs failed"
      return none
    let eNew ← instantiateMVars rhs
    let mut proof ← instantiateMVars (mkAppN thm xs)
    if isIff then
      try proof ← mkAppM ``propext #[proof]
      catch _ => return none
    if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
      trace[Meta.Tactic.simp.congr] "{c.theoremName} has unassigned metavariables"
      return none
    congrArgs { expr := eNew, proof? := proof } extraArgs
  else
    return none

def congr (e : Expr) : SimpM Result := do
  let f := e.getAppFn
  if f.isConst then
    let congrThms ← getSimpCongrTheorems
    let cs := congrThms.get f.constName!
    for c in cs do
      match (← trySimpCongrTheorem? c e) with
      | none   => pure ()
      | some r => return r
    congrDefault e
  else
    congrDefault e

def simpApp (e : Expr) : SimpM Result := do
  if isOfNatNatLit e || isOfScientificLit e || isCharLit e then
    -- Recall that we fold "orphan" kernel Nat literals `n` into `OfNat.ofNat n`
    return { expr := e }
  else
    congr e

def simpStep (e : Expr) : SimpM Result := do
  match e with
  | .mdata m e   => let r ← simp e; return { r with expr := mkMData m r.expr }
  | .proj ..     => simpProj e
  | .app ..      => simpApp e
  | .lam ..      => simpLambda e
  | .forallE ..  => simpForall e
  | .letE ..     => simpLet e
  | .const ..    => simpConst e
  | .bvar ..     => unreachable!
  | .sort ..     => return { expr := e }
  | .lit ..      => return { expr := e }
  | .mvar ..     => return { expr := (← instantiateMVars e) }
  | .fvar ..     => return { expr := (← reduceFVar (← getConfig) (← getSimpTheorems) e) }

def cacheResult (e : Expr) (cfg : Config) (r : Result) : SimpM Result := do
  if cfg.memoize && r.cache then
    modify fun s => { s with cache := s.cache.insert e r }
  return r

partial def simpLoop (e : Expr) : SimpM Result := withIncRecDepth do
  let cfg ← getConfig
  if cfg.memoize then
    let cache := (← get).cache
    if let some result := cache.find? e then
      return result
  if (← get).numSteps > cfg.maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
  else
    checkSystem "simp"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    match (← pre e) with
    | .done r  => cacheResult e cfg r
    | .visit r => cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    | .continue none => visitPreContinue cfg { expr := e }
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Config) (r : Result) : SimpM Result := do
    let eNew ← reduceStep r.expr
    if eNew != r.expr then
      trace[Debug.Meta.Tactic.simp] "reduceStep (pre) {e} => {eNew}"
      let r := { r with expr := eNew }
      cacheResult e cfg (← r.mkEqTrans (← simpLoop r.expr))
    else
      let r ← r.mkEqTrans (← simpStep r.expr)
      visitPost cfg r
  visitPost (cfg : Config) (r : Result) : SimpM Result := do
    match (← post r.expr) with
    | .done r' => cacheResult e cfg (← r.mkEqTrans r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkEqTrans r')
  visitPostContinue (cfg : Config) (r : Result) : SimpM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkEqTrans (← simpLoop r.expr)
    cacheResult e cfg r

set_option compiler.ignoreBorrowAnnotation true in
@[export explicit_lean_simp_engine]
def simpImpl (e : Expr) : SimpM Result := withIncRecDepth do
  if (← isProof e) then
    return { expr := e }
  trace[Meta.Tactic.simp.heads] "{repr e.toHeadIndex}"
  simpLoop e

@[inline] def withCatchingRuntimeEx (x : SimpM α) : SimpM α := do
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
  let (r, s) ← SimpM.run ctx s methods <| withCatchingRuntimeEx <| simp e
  recordSimpUses s
  return (r, s)

def main (e : Expr) (ctx : Context) (stats : Stats := {}) (methods : Methods := {}) : MetaM (Result × Stats) := do
  let (r, s) ← mainCore e ctx { stats with } methods
  return (r, { s with })

def dsimpMainCore (e : Expr) (ctx : Context) (s : State := {}) (methods : Methods := {}) : MetaM (Expr × State) := do
  let (r, s) ← SimpM.run ctx s methods <| withCatchingRuntimeEx <| dsimp e
  recordSimpUses s
  return (r, s)

def dsimpMain (e : Expr) (ctx : Context) (stats : Stats := {}) (methods : Methods := {}) : MetaM (Expr × Stats) := do
  let (r, s) ← dsimpMainCore e ctx { stats with } methods
  return (r, { s with })

def simpMatchDiscrs? (info : MatcherInfo) (e : Expr) : SimpM (Option Result) := do
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
  for i in *...info.numDiscrs do
    let arg := args[i]!
    if i < infos.size && !infos[i]!.hasFwdDeps then
      let argNew ← simp arg
      if argNew.expr != arg then modified := true
      r ← mkCongr r argNew
    else if (← whnfD (← inferType r.expr)).isArrow then
      let argNew ← simp arg
      if argNew.expr != arg then modified := true
      r ← mkCongr r argNew
    else
      let argNew ← dsimp arg
      if argNew != arg then modified := true
      r ← mkCongrFun r argNew
  unless modified do
    return none
  for h : i in info.numDiscrs...args.size do
    let arg := args[i]
    r ← mkCongrFun r arg
  return some r

def simpMatchCore (matcherName : Name) (e : Expr) : SimpM Step := do
  for matchEq in (← Match.getEquationsFor matcherName).eqnNames do
    -- Try lemma
    match (← withReducible <| Simp.tryTheorem? e { origin := .decl matchEq, proof := mkConst matchEq, rfl := (← isRflTheorem matchEq), backwardRfl := (← isBackwardRflTheorem matchEq) }) with
    | none   => pure ()
    | some r => return .visit r
  return .continue

def simpMatch : Simproc := fun e => do
  unless (← getConfig).iota do
    return .continue
  if let some e ← withSimpMetaConfig <| reduceRecMatcher? e then
    return .visit { expr := e }
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
def dischargeGround (e : Expr) : SimpM (Option Expr) := do
  let r ← simp e
  if r.expr.isTrue then
    try
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
    for eqn in eqns do
      -- TODO: cache SimpTheorem to avoid calls to `isRflTheorem`
      if let some result ← Simp.tryTheorem? e { origin := .decl eqn, proof := mkConst eqn, rfl := (← isRflTheorem eqn), backwardRfl := (← isBackwardRflTheorem eqn) } then
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
  return .visit { expr := eNew }

partial def preSEval (s : SimprocsArray) : Simproc :=
  rewritePre >>
  simpMatch >>
  userPreSimprocs s

def postSEval (s : SimprocsArray) : Simproc :=
  rewritePost >>
  userPostSimprocs s >>
  sevalGround

def mkSEvalMethods : CoreM Methods := do
  let s ← getSEvalSimprocs
  return {
    pre        := preSEval #[s]
    post       := postSEval #[s]
    dpre       := dpreDefault #[s]
    dpost      := dpostDefault #[s]
    discharge? := dischargeGround
    wellBehavedDischarge := true
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
def seval (e : Expr) : SimpM Result := do
  let m ← mkSEvalMethods
  let ctx ← mkSEvalContext
  let cacheSaved := (← get).cache
  let usedTheoremsSaved := (← get).usedTheorems
  try
    withReader (fun _ => m.toMethodsRef) do
    withTheReader Simp.Context (fun _ => ctx) do
    modify fun s => { s with cache := {}, usedTheorems := {} }
    simp e
  finally
    modify fun s => { s with cache := cacheSaved, usedTheorems := usedTheoremsSaved }

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
  rewritePre >>
  simpMatch >>
  userPreSimprocs s >>
  simpUsingDecide

def postDefault (s : SimprocsArray) : Simproc :=
  rewritePost >>
  userPostSimprocs s >>
  simpGround >>
  simpArith >>
  simpUsingDecide

partial def isEqnThmHypothesis (e : Expr) : Bool :=
  e.isForall && go e
where
  go (e : Expr) : Bool :=
    match e with
    | .forallE _ d b _ => (d.isEq || d.isHEq || b.hasLooseBVar 0) && go b
    | _ => e.isFalse

private def dischargeUsingAssumption? (e : Expr) : SimpM (Option Expr) := do
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
def dischargeRfl (e : Expr) : SimpM (Option Expr) := do
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


def dischargeDefault? (e : Expr) : SimpM (Option Expr) := do
  let e := e.cleanupAnnotations
  if isEqnThmHypothesis e then
    if let some r ← dischargeUsingAssumption? e then return some r
    if let some r ← dischargeEqnThmHypothesis? e then return some r
  let r ← simp e
  if let some p ← dischargeRfl r.expr then
    return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) e r.expr (← r.getProof) p)
  else if r.expr.isTrue then
    return some (← mkOfEqTrue (← r.getProof))
  else
    return none

abbrev Discharge := Expr → SimpM (Option Expr)

def mkMethods (s : SimprocsArray) (discharge? : Discharge) (wellBehavedDischarge : Bool) : Methods := {
  pre        := preDefault s
  post       := postDefault s
  dpre       := dpreDefault s
  dpost      := dpostDefault s
  discharge?
  wellBehavedDischarge
}

def mkDefaultMethodsCore (simprocs : SimprocsArray) : Methods :=
  mkMethods simprocs dischargeDefault? (wellBehavedDischarge := true)

def mkDefaultMethods : CoreM Methods := do
  if simprocs.get (← getOptions) then
    return mkDefaultMethodsCore #[(← getSimprocs)]
  else
    return mkDefaultMethodsCore {}

end Simp.Engine
end Lean.Meta
