/-
# Forked simp traversal with exact position threading

This module is a **copy of Lean's own simp traversal**, edited minimally to

1. thread the current `SubExpr.Pos` child-index path through the recursion, and
2. log an event into a trace buffer at the exact position where it happened.

It keeps calling the SAME `Lean.Meta.Simp` machinery for everything that
decides *what* simp does: `Simp.Methods` (`pre`/`post`/`dpre`/`dpost`/
`discharge?`) from the context, `Simp.rewrite?`, `Simp.Result`, the simproc
tables, `tryAutoCongrTheorem?`, `simpAppUsingCongr`, `congrArgs`,
`trySimpCongrTheorem?`.  Lemma selection, proof construction and results are
stock; the fork is stock code plus logging, never a re-implementation.

## Source provenance

Every copied function carries a `SOURCE:` comment naming the file and line
range in the Lean toolchain it was copied from, so a Lean bump can be re-synced
by diffing against the new upstream.  Toolchain: **Lean 4.32.2**
(`~/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/`).

Functions whose upstream body is `private` are copied verbatim; every symbol
their bodies reference is public (`Lean/Meta/WHNF.lean`, `Lean/ProjFns.lean`,
`Lean/Meta/Tactic/Simp/Types.lean`, `.../Rewrite.lean`), so no `private`,
`unsafe` or `@[implemented_by]` boundary had to be reproduced.

## Position convention

Per `tracking/SIMP-TRACE-SPEC.md`: `app f a` has 0 = f, 1 = a; `lam`/`forallE`
have 0 = binder type, 1 = body; `letE` has 0 = type, 1 = value, 2 = body;
`mdata` and `proj` have child 0.

Recorder machinery only.  Never imported by translated Mathlib source.
-/

module

public meta import Lean
public meta import ExplicitLean.SimpTrace.Types

public meta section

namespace ExplicitLean.SimpTrace

open Lean Lean.Meta Lean.Meta.Simp

/-! ## The trace buffer

Events are logged into an `IO.Ref` threaded through the run.  We keep the
buffer outside `SimpM`'s own `State` so that nothing in the copied code has to
change shape, and so a discharger's nested run can push/pop a frame.
-/

/-- A logged definitional reduction kind, per the spec. -/
inductive DefKind where
  | beta | eta | proj | zeta | iota | unfold | change
  deriving Inhabited, BEq, Repr

def DefKind.toString : DefKind → String
  | .beta => "beta" | .eta => "eta" | .proj => "proj" | .zeta => "zeta"
  | .iota => "iota" | .unfold => "unfold" | .change => "change"

/-- The ambient context an event was observed in, so recorded subterms
pretty-print with their binders in scope.

`binders` is the decisive field for validation: the free variables the traversal
substituted for the term binders it descended under, **outermost first**.  The
traversal knows them exactly (it introduces them), so the validator never has to
guess which locals came from binder descent — which is what left a raw `_fvar`
in a recorded subterm in REVIEW-3 M4(b). -/
structure EvCtx where
  lctx    : LocalContext := {}
  insts   : LocalInstances := {}
  binders : Array FVarId := #[]
  deriving Inhabited

mutual

/-- One event logged by the forked traversal, at the exact position it happened. -/
inductive Event where
  /-- A rewrite fired by `pre`/`post` and attributed to a simp theorem origin.
  `inv` is the `←` direction.  `prop?` is `some true`/`some false` when the
  lemma is Prop-valued and simp used it as `P = True` / `P = False`.
  `source?` names the simproc whose *proof* was this one lemma applied, per the
  amended spec's `eq` bullet: such a firing is an ordinary `rw`, and `source`
  records where it came from.

  `localOrigin` is `origin` resolved to a local hypothesis when `origin` is the
  *syntax* of one (`simp [h]`); it supplies the `local` object and the `prop`
  flag, while `origin` still supplies `name` and `dir`, since only the syntax
  carries a leading `←`. -/
  | rw (pos : Pos) (origin : Origin) (inv : Bool) (prop? : Option Bool)
       (before after : Expr) (ctx : EvCtx)
       (args : Array Expr) (side : Array SideRec) (source? : Option Name)
       (localOrigin : Origin)
  /-- A simproc firing (or any procedure-computed equation). -/
  | eq (pos : Pos) (source? : Option Name) (before after : Expr)
       (ctx : EvCtx) (side : Array SideRec)
  /-- A definitional reduction performed by the traversal itself. -/
  | defeq (pos : Pos) (kind : DefKind) (name? : Option Name)
          (before after : Expr) (ctx : EvCtx)
  /-- Contextual simp made an implication's antecedent available. -/
  | introCtx (pos : Pos) (fvarId : FVarId) (ctx : EvCtx)
  /-- Dependent congruence (spec 3b17247): the application at `pos` had its
  argument `arg` rewritten by `steps` (whose positions are *relative to that
  argument*), and later arguments depending on it were cast-transported by the
  auto-generated congruence theorem for the head.  Emitted only when a
  `CongrArgKind.cast` dependent is present, so plain positional rewriting would
  need casts; ordinary arguments stay plain `rw` steps. -/
  | congr (pos : Pos) (arg : Nat) (steps : Array Event)
          (before after : Expr) (argBefore argAfter : Expr) (ctx : EvCtx)

/-- A discharged side condition: the side goal, the events recorded while it
was discharged, and the closing form (`rfl` / `true_intro` / `assumption:<n>` /
`absurd:<h>` / `decide` / `omega` / `unresolved:<text>`). -/
inductive SideRec where
  /-- `intros` are the antecedents introduced before the steps, for an
  implication-shaped congruence hypothesis (`c → x = u`); spec 2e73661. -/
  | mk (goal : Expr) (events : Array Event) (by_ : Option String) (ctx : EvCtx)
       (intros : Array String)

end

instance : Inhabited Event := ⟨Event.introCtx #[] default {}⟩
instance : Inhabited SideRec := ⟨SideRec.mk default #[] none {} #[]⟩

def SideRec.goal : SideRec → Expr | SideRec.mk g _ _ _ _ => g
def SideRec.events : SideRec → Array Event | SideRec.mk _ e _ _ _ => e
def SideRec.by_ : SideRec → Option String | SideRec.mk _ _ b _ _ => b
def SideRec.evCtx : SideRec → EvCtx | SideRec.mk _ _ _ c _ => c
def SideRec.intros : SideRec → Array String | SideRec.mk _ _ _ _ i => i

/-- Re-root an event's position under `base`.  Used to place events captured
relative to a subterm back at their absolute positions. -/
partial def Event.rebase (base : Pos) : Event → Event
  | .rw p o inv pr b a c args side src lo => .rw (base ++ p) o inv pr b a c args side src lo
  | .eq p s b a c side => .eq (base ++ p) s b a c side
  | .defeq p k n b a c => .defeq (base ++ p) k n b a c
  | .introCtx p f c => .introCtx (base ++ p) f c
  | .congr p i steps b a ab aa c => .congr (base ++ p) i steps b a ab aa c

/-- The position an event was logged at. -/
def Event.pos : Event → Pos
  | Event.rw p .. | Event.eq p .. | Event.defeq p ..
  | Event.introCtx p .. | Event.congr p .. => p

/-- Mutable trace state for one traced `simp` run. -/
structure TraceState where
  /-- Events of the location currently being simplified. -/
  events : Array Event := #[]
  /-- One frame per active discharger nesting level. -/
  sideStack : Array (Array Event) := #[]
  /-- Side conditions collected for the rewrite currently being assembled. -/
  pendingSide : Array SideRec := #[]
  /-- Classified reasons a call could not be fully traced.  Never a silent
  drop and never a generic abort: the tactic reports each as
  `simp_trace unresolved: <reason>` and still leaves stock simp's goal state. -/
  unresolved : Array String := #[]
  /-- The position the traversal is currently visiting.  Set by the copied
  traversal immediately before it calls into the stock `Methods`. -/
  pos : Pos := #[]
  /-- Free variables substituted for the term binders the traversal has
  descended under, outermost first.  Only *term* binders are pushed here:
  `+contextual`'s antecedent hypotheses bind no position in the running term. -/
  binders : Array FVarId := #[]
  /-- Nesting depth inside a stock procedure that is running its own `simp`.

  A simproc may call the opaque `Simp.simp` on a subterm of its own choosing —
  `reduceIte` does exactly this on an `ite`'s condition — and that call goes to
  *stock* `simpImpl`, not to the fork, so the firings it causes carry no
  position of their own.  While `procDepth > 0` those firings are diverted into
  `procEvents` rather than logged at the traversal's position, which would be
  the enclosing node's and therefore wrong.  The simproc's own result is then
  logged as one `eq` step at the position the traversal is actually visiting,
  and the diverted firings become that step's `side` evidence — which is what
  lets its `by` be checked against a *simplified* condition rather than the
  original one. -/
  procDepth : Nat := 0
  /-- Firings diverted while `procDepth > 0`, innermost frame last. -/
  procEvents : Array (Array Event) := #[]
  /-- The subterm each diverted frame's nested `simp` was started on, so the
  side trace can name its own goal.  A simproc's nested `simp` enters stock
  `simpImpl`, whose first `pre` call is on the whole subterm it was given; the
  recorder notes that term the first time it sees position `[]` inside a frame.
  `none` until then. -/
  procGoals : Array (Option Expr) := #[]
  deriving Inhabited

/-- `LocalContext` lives in `Type 1`, so the buffer is an `ST.Ref` in the
corresponding universe rather than `IO.Ref`. -/
abbrev TraceRef := ST.Ref IO.RealWorld TraceState

/-- Push an event into the innermost active frame.  Diverted into `procEvents`
while inside a stock procedure's own nested `simp` (see `procDepth`). -/
def TraceState.push (s : TraceState) (ev : Event) : TraceState :=
  if h : s.procEvents.size > 0 then
    let i := s.procEvents.size - 1
    have : i < s.procEvents.size := Nat.sub_lt h (by decide)
    { s with procEvents := s.procEvents.set i ((s.procEvents[i]).push ev) }
  else if h : s.sideStack.size > 0 then
    let i := s.sideStack.size - 1
    have : i < s.sideStack.size := Nat.sub_lt h (by decide)
    { s with sideStack := s.sideStack.set i ((s.sideStack[i]).push ev) }
  else
    { s with events := s.events.push ev }

/-- Record a classified unresolved reason. -/
def TraceState.markUnresolved (s : TraceState) (reason : String) : TraceState :=
  if s.unresolved.contains reason then s else
    { s with unresolved := s.unresolved.push reason }

/-! ## The fork's own reader state

`SimpM` is `ReaderT MethodsRef (ReaderT Context (StateRefT State MetaM))`; we
cannot extend it without changing every copied signature.  Instead the fork
carries its position as an explicit parameter and stores it in the trace ref
just before handing control to stock code (so the recorder wrapper installed on
`Methods` reads the right position), which is the only place stock code can log.
-/

/-- Capture the ambient local context and the traversal's binder stack. -/
def captureEvCtx (ref : TraceRef) : MetaM EvCtx := do
  return { lctx := ← getLCtx, insts := ← getLocalInstances,
           binders := (← ref.get).binders }

/-- Descend under a term binder whose bound variable the traversal replaced by
the free variable `x`, for the duration of `k`. -/
@[inline] def withBinder (ref : TraceRef) (x : Expr) (k : SimpM α) : SimpM α := do
  let saved := (← ref.get).binders
  ref.modify fun s => { s with binders := s.binders.push x.fvarId! }
  try k finally ref.modify fun s => { s with binders := saved }

/-- Run `k` with every event it logs diverted away from the trace.

Used where stock simp is re-entered on a subterm the fork did not descend into
itself (a simproc's own `simp c`, `simpHaveTelescope`'s telescope bodies): those
firings have no position in the fork's convention, and logging them at the
enclosing position would be wrong.  The caller records the net change instead. -/
@[inline] def withDivertedEvents (ref : TraceRef) (k : SimpM α) : SimpM α := do
  ref.modify fun s =>
    { s with procDepth := s.procDepth + 1,
             procEvents := s.procEvents.push #[],
             procGoals := s.procGoals.push none }
  let depth := (← ref.get).procEvents.size
  try k finally ref.modify fun s =>
    { s with procDepth := s.procDepth - 1,
             procEvents := s.procEvents.take (depth - 1),
             procGoals := s.procGoals.take (depth - 1) }

/-- Run `k`, returning its result together with the events it logged, which are
captured into a frame instead of reaching the trace.

Unlike `withDivertedEvents` the events are *kept*: the caller decides where they
belong.  `tryAutoCongrTheoremT?` uses this because whether an argument's
rewrites keep their own absolute positions or become a `congr` step's nested
steps is only known after every argument has been visited (a `cast` dependent
may appear later in the argument list). -/
def captureEvents (ref : TraceRef) (k : SimpM α) : SimpM (α × Array Event) := do
  ref.modify fun s => { s with procEvents := s.procEvents.push #[] }
  let depth := (← ref.get).procEvents.size
  let a ←
    try k
    catch ex =>
      ref.modify fun s => { s with procEvents := s.procEvents.take (depth - 1) }
      throw ex
  let st ← ref.get
  let evs :=
    if depth > 0 && depth <= st.procEvents.size then
      st.procEvents.getD (depth - 1) #[]
    else #[]
  ref.set { st with procEvents := st.procEvents.take (depth - 1) }
  return (a, evs)

/-- How many events the innermost active frame currently holds.  Comparing this
across a stock-method call says whether that call logged anything. -/
def eventCount (ref : TraceRef) : SimpM Nat := do
  let st ← ref.get
  if st.procEvents.size > 0 then
    return (st.procEvents.getD (st.procEvents.size - 1) #[]).size
  else if st.sideStack.size > 0 then
    return (st.sideStack.getD (st.sideStack.size - 1) #[]).size
  else
    return st.events.size

/-- Set the current position for the duration of `k`. -/
@[inline] def withPos (ref : TraceRef) (pos : Pos) (k : SimpM α) : SimpM α := do
  let saved := (← ref.get).pos
  ref.modify fun s => { s with pos }
  try k finally ref.modify fun s => { s with pos := saved }

/-! ## Copied helpers from `Lean/Meta/Tactic/Simp/Main.lean`

These are `private` upstream; the bodies are copied verbatim because every
symbol they reference is public.  Only the names are prefixed so they cannot
collide with the originals.
-/

/-- SOURCE: Main.lean:39-40 `Simp.isOfNatNatLit` (public upstream; copied so the
fork has no ordering dependency on it). -/
def isOfNatNatLit' (e : Expr) : Bool :=
  e.isAppOf ``OfNat.ofNat && e.getAppNumArgs >= 3 && (e.getArg! 1).isRawNatLit

/-- SOURCE: Main.lean:58-59 `Simp.isOfScientificLit`. -/
def isOfScientificLit' (e : Expr) : Bool :=
  e.isAppOfArity ``OfScientific.ofScientific 5 && (e.getArg! 4).isRawNatLit
    && (e.getArg! 2).isRawNatLit

/-- SOURCE: Main.lean:62-63 `Simp.isCharLit`. -/
def isCharLit' (e : Expr) : Bool :=
  e.isAppOfArity ``Char.ofNat 1 && e.appArg!.isRawNatLit

/-- SOURCE: Main.lean:70-74 `private Simp.unfoldDefinitionAny?`. -/
def unfoldDefinitionAny?' (e : Expr) : MetaM (Option Expr) := do
  if let .const declName _ := e.getAppFn then
    if (← isIrreducible declName) then
      return none
  unfoldDefinition? e (ignoreTransparency := true)

/-- SOURCE: Main.lean:76-138 `private Simp.reduceProjFn?`. -/
def reduceProjFn?' (e : Expr) : SimpM (Option Expr) := do
  matchConst e.getAppFn (fun _ => pure none) fun cinfo _ => do
    match (← getProjectionFnInfo? cinfo.name) with
    | none => return none
    | some projInfo =>
      let reduceProjCont? (e? : Option Expr) : SimpM (Option Expr) := do
        match e? with
        | none   => pure none
        | some e =>
          match (← withSimpMetaConfig <| reduceProj? e.getAppFn) with
          | some f => return some (mkAppN f e.getAppArgs)
          | none   => return none
      if projInfo.fromClass then
        if (← getContext).isDeclToUnfold cinfo.name then
          let e? ← withReducibleAndInstances <| unfoldDefinition? e
          if e?.isSome then
            recordSimpTheorem (.decl cinfo.name)
          return e?
        else
          unless e.getAppNumArgs > projInfo.numParams do
            return none
          let major := e.getArg! projInfo.numParams
          unless (← isConstructorApp major) do
            return none
          if backward.whnf.reducibleClassField.get (← getOptions) then
            unfoldDefinitionAny?' e
          else
            reduceProjCont? (← unfoldDefinitionAny?' e)
      else
        reduceProjCont? (← unfoldDefinition? e)

/-- SOURCE: Main.lean:140-148 `private Simp.reduceFVar`. -/
def reduceFVar' (cfg : Simp.Config) (thms : SimpTheoremsArray) (e : Expr) : SimpM Expr := do
  let localDecl ← getFVarLocalDecl e
  if cfg.zetaDelta || thms.isLetDeclToUnfold e.fvarId! || localDecl.isImplementationDetail then
    if !cfg.zetaDelta && thms.isLetDeclToUnfold e.fvarId! then
      recordSimpTheorem (.fvar localDecl.fvarId)
    let some v := localDecl.value? | return e
    return v
  else
    return e

/-- SOURCE: Main.lean:158-167 `private Simp.isMatchDef`. -/
partial def isMatchDef' (declName : Name) : CoreM Bool := do
  let .defnInfo info ← getConstInfo declName | return false
  return go (← getEnv) info.value
where
  go (env : Environment) (e : Expr) : Bool :=
    if e.isLambda then
      go env e.bindingBody!
    else
      let f := e.getAppFn
      f.isConst && isMatcherCore env f.constName!

/-- SOURCE: Main.lean:172-211 `private Simp.unfold?`. -/
def unfold?' (e : Expr) : SimpM (Option Expr) := do
  let f := e.getAppFn
  if !f.isConst then
    return none
  let fName := f.constName!
  let ctx ← getContext
  let rec unfoldDeclToUnfold? : SimpM (Option Expr) := do
    let options ← getOptions
    let cfg ← Simp.getConfig
    if cfg.unfoldPartialApp
       || (smartUnfolding.get options && (← getEnv).contains (mkSmartUnfoldingNameFor fName)) then
      unfoldDefinitionAny?' e
    else
      let some cinfo := (← getEnv).find? fName | return none
      let some value := cinfo.value? | return none
      let arity := value.getNumHeadLambdas
      if arity > e.getAppNumArgs then return none
      unfoldDefinitionAny?' e
  if (← isProjectionFn fName) then
    return none
  else if ctx.config.autoUnfold then
    if ctx.simpTheorems.isErased (.decl fName) then
      return none
    else if hasSmartUnfoldingDecl (← getEnv) fName then
      unfoldDefinitionAny?' e
    else if (← isMatchDef' fName) then
      let some value ← unfoldDefinitionAny?' e | return none
      let .reduced value ← withSimpMetaConfig <| reduceMatcher? value | return none
      return some value
    else
      return none
  else if ctx.isDeclToUnfold fName then
    unfoldDeclToUnfold?
  else
    return none

/-! ## `reduceStep`, classified

SOURCE: Main.lean:213-244 `private Simp.reduceStep`.  This is the function the
old post-hoc reconstruction could not observe (the reductions happen outside
`Simp.Methods`), and reconstructing them is what REVIEW-3 C2 and M4 came from.
The fork logs each reduction here **at its exact position**, with the kind the
branch that produced it determines — so `iota` is no longer invisible (REVIEW-3
C1's third instance) and no search is ever needed.

The only edits are: each `return` is replaced by a `return (e', kind, name?)`
carrying the classification, and the caller logs it.
-/

/-- The classification of one `reduceStep` reduction. -/
structure Reduction where
  expr  : Expr
  kind  : DefKind
  name? : Option Name := none

/-- SOURCE: Main.lean:213-244 `private Simp.reduceStep`, with each branch
tagged by the spec kind it corresponds to. -/
def reduceStepC (e : Expr) : SimpM (Option Reduction) := do
  let cfg ← Simp.getConfig
  let f := e.getAppFn
  if f.isMVar then
    let e' ← instantiateMVars e
    -- Metavariable instantiation is not a reduction the spec names; it only
    -- happens when simp is run on a term with assigned mvars, and the result is
    -- definitionally the same term.
    return if e' == e then none else some { expr := e', kind := .change }
  withSimpMetaConfig do
  if cfg.beta then
    if f.isHeadBetaTargetFn false then
      return some { expr := f.betaRev e.getAppRevArgs, kind := .beta }
  -- TODO (upstream): eta reduction.  `eta` stays in the spec and in the kind
  -- enumeration, but stock simp's `reduceStep` does not perform it, so the fork
  -- never emits it either.  Doing so would diverge from stock simp.
  if cfg.proj then
    match (← reduceProj? e) with
    | some e' => return some { expr := e', kind := .proj }
    | none =>
    match (← reduceProjFn?' e) with
    | some e' => return some { expr := e', kind := .proj }
    | none   => pure ()
  if cfg.iota then
    match (← reduceRecMatcher? e) with
    | some e' => return some { expr := e', kind := .iota }
    | none   => pure ()
  if let .letE _ _ v b nondep := e then
    if cfg.zeta && (!nondep || cfg.zetaHave) then
      return some { expr := expandLet b #[v] (zetaHave := cfg.zetaHave), kind := .zeta }
    else if cfg.zetaUnused && !b.hasLooseBVars then
      return some { expr := consumeUnusedLet b, kind := .zeta }
  match (← unfold?' e) with
  | some e' =>
    recordSimpTheorem (.decl e.getAppFn.constName!)
    return some { expr := e', kind := .unfold, name? := some e.getAppFn.constName! }
  | none =>
    let e' ← foldRawNatLit e
    -- Folding an orphan raw literal into `OfNat.ofNat` is a representation
    -- change, not a step a replay must perform; `change` carries it faithfully.
    return if e' == e then none else some { expr := e', kind := .change }

/-- Log one reduction at `pos`, then return its expression. -/
def logReduction (ref : TraceRef) (pos : Pos) (e : Expr) (r : Reduction) :
    SimpM Expr := do
  ref.modify (·.push (.defeq pos r.kind r.name? e r.expr (← captureEvCtx ref)))
  return r.expr

/-- SOURCE: Main.lean:213-244 — a single `reduceStep`, logged.  `simpLoop` takes
one step and re-enters, so the fork must too. -/
def reduceOnce (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Expr := do
  match ← reduceStepC e with
  | none => return e
  | some r => if r.expr == e then return e else logReduction ref pos e r

/-- SOURCE: Main.lean:246-252 `private Simp.reduce`, with each step logged. -/
partial def reduceT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Expr :=
  withIncRecDepth do
    match ← reduceStepC e with
    | none => return e
    | some r =>
      if r.expr == e then return e
      let e' ← logReduction ref pos e r
      reduceT ref pos e'

/-! ## Position arithmetic for applications

`simpAppUsingCongr`, `congrArgs` and `tryAutoCongrTheorem?` all work on the
*spine* of an `n`-ary application `f a₀ ... a_{n-1}`.  In `Expr`'s binary
representation that is `(((f a₀) a₁) ... a_{n-1})`, so relative to the whole
application the function head sits at `0ⁿ` and argument `i` sits at
`0^(n-1-i) ++ [1]`.  REVIEW-3's fork note verified this is exactly the order the
upstream traversal walks, so no congruence-lemma slot ever has to be mapped back
to a child index.
-/

/-- The position of argument `i` of an `n`-ary application, relative to the
application's own position `pos`. -/
def argPos (pos : Pos) (n i : Nat) : Pos :=
  (pos ++ Array.replicate (n - 1 - i) 0).push 1

/-- The position of the head of an `n`-ary application. -/
def fnPos (pos : Pos) (n : Nat) : Pos := pos ++ Array.replicate n 0

/-- SOURCE: Types.lean:682-695 `private Simp.mkCongrFun'`. -/
def mkCongrFunT (e : Expr) (r : Simp.Result) (a : Expr) : MetaM Simp.Result := do
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

/-- SOURCE: Types.lean:697-703 `private Simp.mkCongrPrefix`. -/
def mkCongrPrefixT (declName : Name) (e : Expr) : MetaM Expr := do
  let α ← inferType e.appArg!
  let u ← getLevel α
  let β ← inferType e
  let v ← getLevel β
  return mkApp2 (mkConst declName [u, v]) α β

/-- SOURCE: Types.lean:714-729 `private Simp.mkCongr'`. -/
def mkCongrT (e : Expr) (r₁ r₂ : Simp.Result) : MetaM Simp.Result := do
  let e' := e.updateApp! r₁.expr r₂.expr
  match r₁.proof?, r₂.proof? with
  | none,    none    => return { expr := e', proof? := none }
  | some hf, none    =>
    let h ← mkCongrPrefixT ``congrFun' e
    return { expr := e', proof? := mkApp4 h e.appFn! r₁.expr hf r₂.expr }
  | none,    some ha  =>
    let h ← mkCongrPrefixT ``congrArg e
    return { expr := e', proof? := mkApp4 h e.appArg! r₂.expr r₁.expr ha }
  | some hf, some ha =>
    let h ← mkCongrPrefixT ``_root_.congr e
    return { expr := e', proof? := mkApp6 h e.appFn! r₁.expr e.appArg! r₂.expr hf ha }

/-! ## The `dsimp` layer

SOURCE: Main.lean:469-529.  `dsimpImpl` is driven by `Meta.transformWithCache`,
which does not expose positions.  The fork therefore uses its own traversal
(`dsimpT`), structured like `transformWithCache` but threading `pos`, and calls
the same `dpre`/`dpost` methods plus the same `dsimpReduce` logic.
-/

/-- SOURCE: Main.lean:475-483 `private Simp.doNotVisitProofs`. -/
def doNotVisitProofs' : DSimproc := fun e => do
  if ← isProof e then
    if !backward.dsimp.proofs.get (← getOptions) then
      return .done e
    else
      return .continue e
  else
    return .continue e

/-- SOURCE: Main.lean:486-496 `private Simp.doNotVisit`. -/
def doNotVisit' (pred : Expr → Bool) (declName : Name) : DSimproc := fun e => do
  if pred e then
    if (← readThe Simp.Context).isDeclToUnfold declName then
      return .continue e
    else
      match (← (← getMethods).dpost e) with
      | .continue none => return .done e
      | r => return r
  else
    return .continue e

/-- SOURCE: Main.lean:469-473 `private Simp.dsimpReduce`, position-threaded. -/
def dsimpReduceT (ref : TraceRef) (pos : Pos) : DSimproc := fun e => do
  let mut eNew ← reduceT ref pos e
  if eNew.isFVar then
    let eNew' ← reduceFVar' (← Simp.getConfig) (← Simp.getSimpTheorems) eNew
    if eNew' != eNew then
      -- Unfolding a `let`-bound local is zeta-delta: the spec's `zeta` kind.
      ref.modify (·.push (.defeq pos .zeta none eNew eNew' (← captureEvCtx ref)))
      eNew := eNew'
  if eNew != e then return .visit eNew else return .done e

/-- Log a change produced by a stock `dpre`/`dpost` procedure at `pos`.  These
are definitional by construction; we classify them the same way `reduceStepC`
does, falling back to `change` (with a `pp.all` term supplied later). -/
def classifyDefChange (before after : Expr) : DefKind :=
  if before.isApp && before.getAppFn.isLambda && before.headBeta == after then .beta
  else if before.isLet then .zeta
  else if before.isProj then .proj
  else if before.getAppFn.isConst && after.getAppFn != before.getAppFn then .unfold
  else .change

/-- Run a `DSimproc`, logging any change it makes at `pos`. -/
def logDStep (ref : TraceRef) (pos : Pos) (e : Expr) (s : TransformStep) :
    SimpM TransformStep := do
  let record (e' : Expr) : SimpM Unit := do
    unless e' == e do
      let kind := classifyDefChange e e'
      let name? := if kind == .unfold then
          match e.getAppFn with | .const n _ => some n | _ => none
        else none
      ref.modify (·.push (.defeq pos kind name? e e' (← captureEvCtx ref)))
  match s with
  | .done e' => record e'; return s
  | .visit e' => record e'; return s
  | .continue (some e') => record e'; return s
  | .continue none => return s

/-- SOURCE: Main.lean:517-529 `private Simp.dsimpImpl`, with `transformWithCache`
replaced by a position-threading traversal over the same children and the same
pre/post pipeline.  Caching is dropped (positions differ per occurrence, so a
cached result would be logged at the wrong position); this costs time, never
correctness, and `dsimp` subterms are small in practice. -/
partial def dsimpT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Expr := do
  let cfg ← Simp.getConfig
  unless cfg.dsimp do
    return e
  -- SOURCE: Main.lean:524 — upstream ends in `withInDSimpWithCache`, which does
  -- two things: it swaps the `dsimp` cache (the documented cache disablement,
  -- dropped here) **and** it sets `Context.inDSimp := true`.  `inDSimp` is not
  -- a cache flag: stock `dreduceIte`/`dreduceDIte` read it and take their
  -- `.continue` arm unless it is set, so without this wrapper the `dsimp`-mode
  -- `ite` reduction upstream performs can never happen (REVIEW-5 4).
  Simp.withInDSimp <| visit pos e
where
  /-- SOURCE: Main.lean:522 — the `dpre` pipeline, verbatim. -/
  pre (pos : Pos) (e : Expr) : SimpM TransformStep := do
    let m ← getMethods
    let before ← eventCount ref
    let s ← withPos ref pos (m.dpre e)
    -- `instrumentD` already logged this firing when it could attribute it to a
    -- named dsimproc (`dreduceIte` and friends).  Logging it again would
    -- double-count the change and desync the validator — which is exactly what
    -- entering `withInDSimp` exposed (REVIEW-5 4).
    let s ← if (← eventCount ref) > before then pure s else logDStep ref pos e s
    match s with
    | .continue e? =>
      let e := e?.getD e
      let s ← doNotVisit' isOfNatNatLit' ``OfNat.ofNat e
      match s with
      | .continue e? =>
        let e := e?.getD e
        let s ← doNotVisit' isOfScientificLit' ``OfScientific.ofScientific e
        match s with
        | .continue e? =>
          let e := e?.getD e
          let s ← doNotVisit' isCharLit' ``Char.ofNat e
          match s with
          | .continue e? => doNotVisitProofs' (e?.getD e)
          | s => return s
        | s => return s
      | s => return s
    | s => return s
  /-- SOURCE: Main.lean:523 — the `dpost` pipeline, verbatim. -/
  postStep (pos : Pos) (e : Expr) : SimpM TransformStep := do
    let m ← getMethods
    let before ← eventCount ref
    let s ← withPos ref pos (m.dpost e)
    let s ← if (← eventCount ref) > before then pure s else logDStep ref pos e s
    match s with
    | .continue e? => dsimpReduceT ref pos (e?.getD e)
    | s => return s
  /-- SOURCE: Transform.lean:111-114 `visitPost`. -/
  visitPost (pos : Pos) (e : Expr) : SimpM Expr := do
    match ← postStep pos e with
    | .done e => return e
    | .visit e => visit pos e
    | .continue e? => return e?.getD e
  /-- SOURCE: Transform.lean:116-121 `visitLambda`.

  Upstream collects the whole lambda telescope, instantiating each body with
  `instantiateRev fvars`, and runs `visitPost` on the term *rebuilt* by
  `mkLambdaFVars`.  Two consequences the fork must preserve, and previously did
  not: `pre`/`post` never see a term with loose bvars (REVIEW-4 defect 2's
  PANIC — stock `rewritePost` was handed an open term), and the post step
  happens at the telescope *root*, not inside the binder (defect 1's wrong
  position).  `usedLetOnly` is threaded because it decides whether unused
  binders survive the rebuild. -/
  visitLambda (pos : Pos) (fvars : Array Expr) (e : Expr) : SimpM Expr := do
    match e with
    | .lam n d b c =>
      withLocalDecl n c (← visit (pos.push 0) (d.instantiateRev fvars)) fun x =>
        withBinder ref x do visitLambda (pos.push 1) (fvars.push x) b
    | e =>
      let body ← visit pos (e.instantiateRev fvars)
      visitPost (rootOf pos fvars.size)
        (← mkLambdaFVars (usedLetOnly := (← usedLetOnly)) fvars body)
  /-- SOURCE: Transform.lean:123-128 `visitForall`. -/
  visitForall (pos : Pos) (fvars : Array Expr) (e : Expr) : SimpM Expr := do
    match e with
    | .forallE n d b c =>
      withLocalDecl n c (← visit (pos.push 0) (d.instantiateRev fvars)) fun x =>
        withBinder ref x do visitForall (pos.push 1) (fvars.push x) b
    | e =>
      let body ← visit pos (e.instantiateRev fvars)
      visitPost (rootOf pos fvars.size)
        (← mkForallFVars (usedLetOnly := (← usedLetOnly)) fvars body)
  /-- SOURCE: Transform.lean:130-135 `visitLet`.

  The `let` telescope is the path REVIEW-4 defects 1 and 2 share: under
  `zeta := false` the traversal descends here rather than zeta-reducing, so
  getting the rebuild and the post position right is what fixes both. -/
  visitLet (pos : Pos) (fvars : Array Expr) (e : Expr) : SimpM Expr := do
    match e with
    | .letE n t v b nondep =>
      withLetDecl n (← visit (pos.push 0) (t.instantiateRev fvars))
          (← visit (pos.push 1) (v.instantiateRev fvars)) (nondep := nondep) fun x =>
        withBinder ref x do visitLet (pos.push 2) (fvars.push x) b
    | e =>
      let body ← visit pos (e.instantiateRev fvars)
      visitPost (rootOf pos fvars.size)
        (← mkLetFVars (usedLetOnly := (← usedLetOnly)) (generalizeNondepLet := false)
          fvars body)
  /-- SOURCE: Transform.lean:136-155 `visitApp`, including `skipInstances`.

  Upstream resolves instance arguments through `getFunInfoNArgs` and does not
  visit them when `skipInstances` is set (`!cfg.instances`); visiting them would
  let `dsimp` rewrite inside an instance where stock does not. -/
  visitApp (pos : Pos) (e : Expr) : SimpM Expr := do
    let skipInstances := !(← Simp.getConfig).instances
    e.withApp fun f args => do
      let n := args.size
      let f ← visit (fnPos pos n) f
      if skipInstances then
        let infos := (← getFunInfoNArgs f args.size).paramInfo
        let mut args := args
        for i in [0:args.size] do
          if h : i < infos.size then
            if infos[i].isInstance then
              continue
          args := args.set! i (← visit (argPos pos n i) args[i]!)
        visitPost pos (mkAppN f args)
      else
        let mut args := args
        for i in [0:args.size] do
          args := args.set! i (← visit (argPos pos n i) args[i]!)
        visitPost pos (mkAppN f args)
  /-- SOURCE: Transform.lean:110-112 `visit`.  `checkCache` is dropped (the
  documented cache disablement), but `withIncRecDepth` and the per-node
  `Core.checkSystem "transform"` are kept: without the latter a long `dsimp`
  traversal is uninterruptible (REVIEW-4 defect 3). -/
  visit (pos : Pos) (e : Expr) : SimpM Expr := withIncRecDepth do
    Core.checkSystem "transform"
    match ← pre pos e with
    | .done e => return e
    | .visit e => visit pos e
    | .continue e? =>
      let e := e?.getD e
      match e with
      | .forallE .. => visitForall pos #[] e
      | .lam ..     => visitLambda pos #[] e
      | .letE ..    => visitLet pos #[] e
      | .app ..     => visitApp pos e
      | .mdata _ b  => visitPost pos (e.updateMData! (← visit (pos.push 0) b))
      | .proj _ _ b => visitPost pos (e.updateProj! (← visit (pos.push 0) b))
      | _           => visitPost pos e
  /-- `usedLetOnly := cfg.zeta || cfg.zetaUnused` (SOURCE: Main.lean:526). -/
  usedLetOnly : SimpM Bool := do
    let cfg ← Simp.getConfig
    return cfg.zeta || cfg.zetaUnused
  /-- The position of the telescope root, `n` binders above `pos`.

  `n` cannot exceed `pos.size` when the traversal reached this node from the
  location root, but it can when a subterm is simplified from a *fresh* root
  (`tryAutoCongrTheoremT?` visits a cast-dependent argument at `#[]` so its
  events can be re-rooted later), so the drop is clamped. -/
  rootOf (pos : Pos) (n : Nat) : Pos :=
    if n == 0 then pos else pos.extract 0 (pos.size - min n pos.size)

/-! ## The main traversal

SOURCE: `Lean/Meta/Tactic/Simp/Main.lean` for `simpProj`, `simpConst`,
`simpLambda`, `simpArrow`, `simpForall`, `simpLet`, `visitFn`, `congrDefault`,
`processCongrHypothesis`, `trySimpCongrTheorem?`, `congr`, `simpApp`,
`simpStep`, `cacheResult`, `simpLoop`, `simpImpl`; and
`Lean/Meta/Tactic/Simp/Types.lean` for `congrArgs`, `simpAppUsingCongr` and
`tryAutoCongrTheorem?`.

Two edits are applied uniformly:

* every recursive call to the opaque `Simp.simp` / `Simp.dsimp` becomes a call
  to `simpT` / `dsimpT` with the child's position (the opaque `simp` dispatches
  to stock `simpImpl`, so leaving even one call unchanged would lose positions
  for the whole subtree);
* the stock `Methods` are invoked under `withPos`, so the recorder wrapper
  installed on them reads the position of the term they are firing on.

Everything that decides *what* simp does is untouched: `pre`/`post`/`dpre`/
`dpost`/`discharge?` come from the context's `Methods`, congruence theorems come
from `getSimpCongrTheorems`, and `Result` construction uses the same
`mkCongr`/`mkCongrFun`/`mkCongrArg`/`mkEqTrans` helpers.

Caching is disabled in the fork (`cacheResultT` is a no-op): a cached `Result`
would be reused at a different position and its events would then be attributed
to the wrong place — or, worse, not logged at all.  Disabling it costs time but
never correctness, and it is the only way a position-exact trace can be built
on top of an expression-keyed cache.
-/

mutual

/-- SOURCE: Types.lean:649-679 `Simp.congrArgs`, position-threaded. -/
partial def congrArgsT (ref : TraceRef) (pos : Pos) (r : Simp.Result)
    (args : Array Expr) (numArgs : Nat) (offset : Nat) : SimpM Simp.Result := do
  if args.isEmpty then
    return r
  else
    let cfg ← Simp.getConfig
    let infos := (← getFunInfoNArgs r.expr args.size).paramInfo
    let mut r := r
    let mut i := 0
    for arg in args do
      let apos := argPos pos numArgs (offset + i)
      if h : i < infos.size then
        let info := infos[i]
        if info.isInstance && (!cfg.instances || cfg.ground) then
          r ← Simp.mkCongrFun r arg
        else if !info.hasFwdDeps then
          r ← Simp.mkCongr r (← simpT ref apos arg)
        else if (← whnfD (← inferType r.expr)).isArrow then
          r ← Simp.mkCongr r (← simpT ref apos arg)
        else
          r ← Simp.mkCongrFun r (← dsimpT ref apos arg)
      else if (← whnfD (← inferType r.expr)).isArrow then
        r ← Simp.mkCongr r (← simpT ref apos arg)
      else
        r ← Simp.mkCongrFun r (← dsimpT ref apos arg)
      i := i + 1
    return r

/-- SOURCE: Types.lean:732-765 `Simp.simpAppUsingCongr`, position-threaded.
The inner `visit` destructures `let .app f a := e` and recurses on `f` with
`i-1`, which is exactly the spec's `app f a ↦ 0 = f, 1 = a` convention. -/
partial def simpAppUsingCongrT (ref : TraceRef) (pos : Pos) (e : Expr) :
    SimpM Simp.Result := do
  let f := e.getAppFn
  let numArgs := e.getAppNumArgs
  let cfg ← Simp.getConfig
  let infos := (← getFunInfoNArgs f numArgs).paramInfo
  let rec visit (e : Expr) (i : Nat) : SimpM Simp.Result := do
    if i == 0 then
      simpT ref (fnPos pos numArgs) f
    else
      checkSystem "simp"
      let i := i - 1
      let .app f a := e | unreachable!
      let fr ← visit f i
      let apos := argPos pos numArgs i
      if h : i < infos.size then
        let info := infos[i]
        if info.isInstance && (!cfg.instances || cfg.ground) then
          mkCongrFunT e fr a
        else if !info.hasFwdDeps then
          mkCongrT e fr (← simpT ref apos a)
        else if (← whnfD (← inferType f)).isArrow then
          mkCongrT e fr (← simpT ref apos a)
        else
          mkCongrFunT e fr (← dsimpT ref apos a)
      else if (← whnfD (← inferType f)).isArrow then
        mkCongrT e fr (← simpT ref apos a)
      else
        mkCongrFunT e fr (← dsimpT ref apos a)
  visit e numArgs

/-- SOURCE: Types.lean:807-916 `Simp.tryAutoCongrTheorem?`, position-threaded.
`argKinds` is indexed by the same plain counter as `args`, so the position of
the argument being visited is already in hand. -/
partial def tryAutoCongrTheoremT? (ref : TraceRef) (pos : Pos) (e : Expr) :
    SimpM (Option Simp.Result) := do
  let f := e.getAppFn
  let some cgrThm ← Simp.mkCongrSimp? f | return none
  if cgrThm.argKinds.size != e.getAppNumArgs then return none
  let args := e.getAppArgs
  let numArgs := args.size
  let infos := (← getFunInfoNArgs f args.size).paramInfo
  let config ← Simp.getConfig
  let mut simplified := false
  let mut hasProof   := false
  let mut hasCast    := false
  let mut argsNew    := #[]
  let mut argResults := #[]
  let mut eqArgEvents : Array (Nat × Expr × Expr × Array Event) := #[]
  let mut i          := 0
  for arg in args, kind in cgrThm.argKinds do
    let apos := argPos pos numArgs i
    if h : config.ground ∧ i < infos.size then
      if (infos[i]'h.2).isInstance then
        argsNew := argsNew.push arg
        i := i + 1
        continue
    match kind with
    | CongrArgKind.fixed =>
      let argNew ← dsimpT ref apos arg
      if arg != argNew then
        simplified := true
      argsNew := argsNew.push argNew
    | CongrArgKind.cast  => hasCast := true; argsNew := argsNew.push arg
    | CongrArgKind.subsingletonInst => argsNew := argsNew.push arg
    | CongrArgKind.eq =>
      -- Capture this argument's events separately: if the theorem turns out to
      -- transport a `cast` dependent, they become a `congr` step's nested
      -- `steps` (rooted at the argument) instead of steps at their own absolute
      -- positions, which plain positional rewriting could not replay.
      let (argResult, evs) ← captureEvents ref (simpT ref #[] arg)
      eqArgEvents := eqArgEvents.push (i, arg, argResult.expr, evs)
      argResults := argResults.push argResult
      argsNew    := argsNew.push argResult.expr
      if argResult.proof?.isSome then hasProof := true
      if arg != argResult.expr then simplified := true
    | _ => unreachable!
    i := i + 1
  if !simplified then return some { expr := e }
  -- Replay the captured argument events, now that `hasCast` is settled and the
  -- node is known to have changed.
  if hasCast then
    -- Cast dependents were transported: each rewritten argument becomes one
    -- `congr` step at the application's position, carrying its own steps.
    -- `before`/`after` describe the node at `pos` (what the validator checks);
    -- `argBefore`/`argAfter` describe the argument the nested steps replay.
    -- With several rewritten arguments each step's `before` is the application
    -- as it stands when that step runs, so the steps compose in array order.
    let evCtx ← captureEvCtx ref
    let mut nodeArgs := args
    for (ai, aBefore, aAfter, evs) in eqArgEvents do
      if h : ai < nodeArgs.size then
        unless aBefore == aAfter do
          let nodeBefore := mkAppN f nodeArgs
          nodeArgs := nodeArgs.set ai aAfter
          let nodeAfter := mkAppN f nodeArgs
          ref.modify (·.push
            (.congr pos ai evs nodeBefore nodeAfter aBefore aAfter evCtx))
  else
    -- No cast: the arguments are ordinary, so their rewrites keep their own
    -- absolute positions and stay plain steps, exactly as before.
    for (ai, _, _, evs) in eqArgEvents do
      for ev in evs do
        ref.modify (·.push (ev.rebase (argPos pos numArgs ai)))
  if !hasProof && !hasCast then
    return some { expr := mkAppN f argsNew }
  let mut proof := cgrThm.proof
  let mut type  := cgrThm.type
  let mut j := 0
  let mut subst := #[]
  for arg in args, argNew in argsNew, kind in cgrThm.argKinds do
    proof := mkApp proof arg
    type := type.bindingBody!
    match kind with
    | CongrArgKind.fixed => subst := subst.push argNew
    | CongrArgKind.cast  => subst := subst.push arg
    | CongrArgKind.subsingletonInst =>
      subst := subst.push arg
      let clsNew := type.bindingDomain!.instantiateRev subst
      let instNew ← if (← isDefEq (← inferType arg) clsNew) then
        pure arg
      else
        match (← trySynthInstance clsNew) with
        | LOption.some val => pure val
        | _ => return none
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
  let rhs ← if hasCast then Simp.removeUnnecessaryCasts rhs else pure rhs
  if hasProof then
    return some { expr := rhs, proof? := proof }
  else
    return some { expr := rhs }

/-- SOURCE: Main.lean:531-543 `Simp.visitFn`, position-threaded. -/
partial def visitFnT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result := do
  let f := e.getAppFn
  let numArgs := e.getAppNumArgs
  let fNew ← simpT ref (fnPos pos numArgs) f
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

/-- SOURCE: Main.lean:545-549 `Simp.congrDefault`, position-threaded. -/
partial def congrDefaultT (ref : TraceRef) (pos : Pos) (e : Expr) :
    SimpM Simp.Result := do
  if let some result ← tryAutoCongrTheoremT? ref pos e then
    result.mkEqTrans (← visitFnT ref pos result.expr)
  else
    Simp.withParent e <| simpAppUsingCongrT ref pos e

/-- SOURCE: Main.lean:552-583 `Simp.processCongrHypothesis`.

Per spec 2e73661 a *user* congruence theorem is an ordinary `rw` step naming the
theorem, with one `side` sub-trace per hypothesis in order.  This function
therefore records each hypothesis's own rewrites into a frame and hands the
caller a `SideRec` rooted at that hypothesis's goal, rather than logging the
rewrites at absolute positions.

A hypothesis of implication shape (`c → x = u`) introduces its antecedents
first; their names go in the side trace's `intros`, and the steps that follow
prove the consequent.  `forallTelescopeReducing` gives exactly those antecedents
as `xs`, so the two agree by construction. -/
partial def processCongrHypothesisT (ref : TraceRef) (thmName : Name)
    (h : Expr) (hType : Expr) : SimpM (Bool × Option SideRec) := do
  let _ := thmName
  forallTelescopeReducing hType fun xs hType => withNewLemmasT ref xs do
    let lhs ← instantiateMVars hType.appFn!.appArg!
    -- The hypothesis's steps are relative to its own left-hand side, which is
    -- what the side trace's goal names, so the sub-run starts at the root.
    let (r, evs) ← captureEvents ref (simpT ref #[] lhs)
    let rhs := hType.appArg!
    rhs.withApp fun m zs => do
      let val ← mkLambdaFVars zs r.expr
      unless (← Simp.withSimpMetaConfig <| isDefEq m val) do
        Simp.throwCongrHypothesisFailed
      let mut proof ← r.getProof
      if hType.isAppOf ``Iff then
        try proof ← mkIffOfEq proof
        catch _ => Simp.throwCongrHypothesisFailed
      unless (← isDefEq h (← mkLambdaFVars xs proof)) do
        Simp.throwCongrHypothesisFailed
      let progress := r.proof?.isSome || (xs.size > 0 && lhs != r.expr)
      -- The side goal is the equation this hypothesis establishes.
      let goal ← instantiateMVars (← mkEq lhs r.expr)
      -- The antecedents' *display* names.  Never `eraseMacroScopes`: for an
      -- inaccessible antecedent that yields a plain name which usually denotes a
      -- different, accessible local in the same context — the hazard REVIEW-2
      -- found for `name`.  `ppExpr` gives the `a✝` form a generator can bind.
      let intros ← xs.mapM fun x => do
        pure (← ppExpr x).pretty
      let side : SideRec :=
        .mk goal evs (if evs.isEmpty then some "rfl" else none)
          (← captureEvCtx ref) intros
      return (progress, some side)

/-- SOURCE: Main.lean:586-635 `Simp.trySimpCongrTheorem?`, position-threaded.

A user congruence theorem fires as one `rw` step naming the theorem, with
`"source": "congr"` and one `side` per hypothesis in order (spec 2e73661).
Replay is `rw [ite_congr h₁ h₂ h₃]` with each `hᵢ` proved by its side trace. -/
partial def trySimpCongrTheoremT? (ref : TraceRef) (pos : Pos)
    (c : SimpCongrTheorem) (e : Expr) : SimpM (Option Simp.Result) :=
  withNewMCtxDepth do Simp.withParent e do
    Simp.recordCongrTheorem c.theoremName
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
    let origNumArgs := e.getAppNumArgs
    if e.getAppNumArgs > numArgs then
      let args := e.getAppArgs
      e := mkAppN e.getAppFn args[*...numArgs]
      extraArgs := args[numArgs...*].toArray
    if (← Simp.withSimpMetaConfig <| isDefEq lhs e) then
      let mut modified := false
      let mut sides : Array SideRec := #[]
      for i in c.hypothesesPos do
        let h := xs[i]!
        let hType ← instantiateMVars (← inferType h)
        let hType ← if thmHasBinderNameHint then hType.resolveBinderNameHint else pure hType
        try
          let (progress, side?) ← processCongrHypothesisT ref c.theoremName h hType
          if progress then modified := true
          if let some side := side? then sides := sides.push side
        catch _ =>
          return none
      unless modified do
        return none
      unless (← Simp.synthesizeArgs (.decl c.theoremName) bis xs) do
        return none
      let eNew ← instantiateMVars rhs
      let mut proof ← instantiateMVars (mkAppN thm xs)
      if isIff then
        try proof ← mkAppM ``propext #[proof]
        catch _ => return none
      if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
        return none
      -- One `rw` naming the theorem, carrying its hypotheses as `side` traces.
      -- The side goals now instantiate to their final forms, so re-read them.
      unless eNew == e do
        let sidesFinal ← sides.mapM fun sd => do
          pure (SideRec.mk (← instantiateMVars sd.goal) sd.events sd.by_
            sd.evCtx sd.intros)
        ref.modify (·.push
          (.rw pos (.decl c.theoremName true false) false none e eNew
            (← captureEvCtx ref) #[] sidesFinal (some `congr)
            (.decl c.theoremName true false)))
      congrArgsT ref pos { expr := eNew, proof? := proof } extraArgs
        origNumArgs numArgs
    else
      return none

/-- SOURCE: Main.lean:637-648 `Simp.congr`, position-threaded. -/
partial def congrT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result := do
  let f := e.getAppFn
  if f.isConst then
    let congrThms ← Simp.getSimpCongrTheorems
    let cs := congrThms.get f.constName!
    for c in cs do
      match (← trySimpCongrTheoremT? ref pos c e) with
      | none   => pure ()
      | some r => return r
    congrDefaultT ref pos e
  else
    congrDefaultT ref pos e

/-- SOURCE: Main.lean:650-655 `Simp.simpApp`, position-threaded. -/
partial def simpAppT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result := do
  if isOfNatNatLit' e || isOfScientificLit' e || isCharLit' e then
    return { expr := e }
  else
    congrT ref pos e

/-- SOURCE: Main.lean:299-323 `Simp.simpProj`, position-threaded.  A `.proj`
node has child 0, per the spec. -/
partial def simpProjT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result := do
  match (← Simp.withSimpMetaConfig <| reduceProj? e) with
  | some e' =>
    ref.modify (·.push (.defeq pos .proj none e e' (← captureEvCtx ref)))
    return { expr := e' }
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
      let r ← simpT ref (pos.push 0) s
      let eNew := e.updateProj! r.expr
      match r.proof? with
      | none => return { expr := eNew }
      | some h =>
        let hNew ← mkEqNDRec motive (← mkEqRefl e) h
        return { expr := eNew, proof? := some hNew }
    else
      return { expr := (← dsimpT ref pos e) }

/-- SOURCE: Main.lean:325-326 `Simp.simpConst`, position-threaded. -/
partial def simpConstT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result :=
  return { expr := (← reduceT ref pos e) }

/-- SOURCE: Main.lean:268-287 `Simp.withNewLemmas`. -/
partial def withNewLemmasT (ref : TraceRef) (xs : Array Expr) (f : SimpM α) :
    SimpM α := do
  let _ := ref
  if (← Simp.getConfig).contextual then
    Simp.withFreshCache do
      let mut s ← Simp.getSimpTheorems
      let mut updated := false
      let ctx ← Simp.getContext
      for x in xs do
        if (← isProof x) then
          s ← s.addTheorem (.fvar x.fvarId!) x (config := ctx.indexConfig)
          updated := true
      if updated then
        Simp.withSimpTheorems s f
      else
        f
  else if (← Simp.getMethods).wellBehavedDischarge then
    f
  else
    Simp.withFreshCache do f

/-- SOURCE: Main.lean:257-263 `Simp.lambdaTelescopeDSimp`, position-threaded.
Each `lam` crossed pushes 1 (the body), per the spec; the binder type is
`dsimp`ed at child 0 of the same node. -/
partial def lambdaTelescopeDSimpT (ref : TraceRef) (pos : Pos) (e : Expr)
    (k : Pos → Array Expr → Expr → SimpM α) : SimpM α := do
  go pos #[] e
where
  go (pos : Pos) (xs : Array Expr) (e : Expr) : SimpM α := do
    match e with
    | .lam n d b c =>
      withLocalDecl n c (← dsimpT ref (pos.push 0) d) fun x =>
        withBinder ref x do go (pos.push 1) (xs.push x) (b.instantiate1 x)
    | e => k pos xs e

/-- SOURCE: Main.lean:328-331 `Simp.simpLambda`, position-threaded. -/
partial def simpLambdaT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result :=
  Simp.withParent e <| lambdaTelescopeDSimpT ref pos e fun bpos xs e =>
    withNewLemmasT ref xs do
      let r ← simpT ref bpos e
      r.addLambdas xs

/-- SOURCE: Main.lean:333-363 `Simp.simpArrow`, position-threaded.  An arrow
`p → q` is a non-dependent `forallE`, so `p` is child 0 and `q` is child 1.
When `+contextual` assumes `p`, that is logged as the spec's `intro_ctx` at the
arrow's own position. -/
partial def simpArrowT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result := do
  let p := e.bindingDomain!
  let q := e.bindingBody!
  let rp ← simpT ref (pos.push 0) p
  if (← pure (← Simp.getConfig).contextual <&&> isProp p <&&> isProp q) then
    withLocalDeclD e.bindingName! rp.expr fun h => withNewLemmasT ref #[h] do
      ref.modify (·.push (.introCtx pos h.fvarId! (← captureEvCtx ref)))
      let rq ← simpT ref (pos.push 1) q
      match rq.proof? with
      | none    => Simp.mkImpCongr e rp rq
      | some hq =>
        let hq ← mkLambdaFVars #[h] hq
        if rq.expr.containsFVar h.fvarId! then
          return { expr := (← mkForallFVars #[h] rq.expr),
                   proof? := (← withDefault <| mkImpDepCongrCtx (← rp.getProof) hq) }
        else
          return { expr := e.updateForallE! rp.expr rq.expr,
                   proof? := (← withDefault <| mkImpCongrCtx (← rp.getProof) hq) }
  else
    Simp.mkImpCongr e rp (← simpT ref (pos.push 1) q)

/-- SOURCE: Main.lean:365-412 `Simp.simpForall`, position-threaded. -/
partial def simpForallT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result :=
  Simp.withParent e do
    if e.isArrow then
      simpArrowT ref pos e
    else if (← isProp e) then
      let domain := e.bindingDomain!
      if (← isProp domain) then
        let rd ← simpT ref (pos.push 0) domain
        if let some h₁ := rd.proof? then
          -- `forall_prop_domain_congr` rewrites the body under a *substituted*
          -- binder (`h₁.substr a`), so the body simp sees is not the body at
          -- child 1 of this node.  Positions inside it are therefore not
          -- expressible in the spec's convention; classify rather than guess.
          let p₁ := domain
          let p₂ := rd.expr
          let q₁ := mkLambda e.bindingName! e.bindingInfo! p₁ e.bindingBody!
          let result ← withLocalDecl e.bindingName! e.bindingInfo! p₂ fun a =>
            withBinder ref a <| withNewLemmasT ref #[a] do
              let prop := mkSort Level.zero
              let h₁_substr_a := mkApp6 (mkConst ``Eq.substr [Level.one]) prop
                (mkLambda `x .default prop (mkBVar 0)) p₂ p₁ h₁ a
              let q_h₁_substr_a := e.bindingBody!.instantiate1 h₁_substr_a
              let before := q_h₁_substr_a
              let rb ← simpT ref (pos.push 1) q_h₁_substr_a
              unless rb.expr == before do
                ref.modify (·.markUnresolved
                  "rewrite under `forall_prop_domain_congr` (substituted binder)")
              let h₂ ← mkLambdaFVars #[a] (← rb.getProof)
              let q₂ ← mkLambdaFVars #[a] rb.expr
              let result ← mkForallFVars #[a] rb.expr
              let proof := mkApp6 (mkConst ``forall_prop_domain_congr) p₁ p₂ q₁ q₂ h₁ h₂
              return { expr := result, proof? := proof }
          return result
      let domain ← dsimpT ref (pos.push 0) domain
      withLocalDecl e.bindingName! e.bindingInfo! domain fun x =>
        withBinder ref x <| withNewLemmasT ref #[x] do
          let b := e.bindingBody!.instantiate1 x
          let rb ← simpT ref (pos.push 1) b
          let eNew ← mkForallFVars #[x] rb.expr
          match rb.proof? with
          | none   => return { expr := eNew }
          | some h => return { expr := eNew,
                               proof? := (← mkForallCongr (← mkLambdaFVars #[x] h)) }
    else
      return { expr := (← dsimpT ref pos e) }

/-- SOURCE: Main.lean:436-467 `Simp.simpLet`, position-threaded.

Two things upstream does here are invisible to a `Methods` wrapper and must be
recorded, or the validator replays against a term simp has already changed
(REVIEW-4 defect 1):

* **`letToHave`** rewrites the `let` into a `have` *before* any simplification.
  That is a definitional change of the term at this position, so it is logged as
  a `change` step carrying the converted term. Without it the validator
  navigates a `let` while every later event was recorded against a `have`.
* **`simpHaveTelescope`** simplifies a whole `have` telescope at once through
  the generic `MonadSimp SimpM` instance, which dispatches to *stock* `simp`;
  its inner rewrites carry no position. We run it unchanged (diverging from
  stock simp is never an option) and record the whole telescope rewrite as one
  `change` at this position, so the replayed term stays in step. The call is
  additionally marked unresolved, because a `change` is a defeq assertion rather
  than the sequence of rewrites simp actually made. -/
partial def simpLetT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result := do
  assert! e.isLet
  if e.letNondep! then
    haveTelescope pos e
  else
    let e ←
      if (← Simp.getConfig).letToHave then
        let eNew ← letToHave e
        unless eNew == e do
          -- A definitional conversion at this position; never a silent desync.
          ref.modify (·.push (.defeq pos .change none e eNew (← captureEvCtx ref)))
        if eNew.isLet && eNew.letNondep! then
          return ← haveTelescope pos eNew
        pure eNew
      else
        pure e
    return { expr := (← dsimpT ref pos e) }
where
  haveTelescope (pos : Pos) (e : Expr) : SimpM Simp.Result := do
    -- `simpHaveTelescope` runs *stock* `simp` on the telescope's bodies, under
    -- the telescope's own binders.  Those firings carry no position of their
    -- own and are observed on open terms, so they are diverted exactly as a
    -- simproc's nested `simp` is (`procEvents`), and the telescope rewrite is
    -- recorded as one `change` at this position instead.
    let r ← withDivertedEvents ref (Simp.simpHaveTelescope e)
    unless r.expr == e do
      ref.modify (·.push (.defeq pos .change none e r.expr (← captureEvCtx ref)))
      ref.modify (·.markUnresolved
        "`have` telescope simplified as a unit (`simpHaveTelescope` runs stock \
simp, so its inner rewrites carry no position); recorded as one `change`")
    return r

/-- SOURCE: Main.lean:657-670 `Simp.simpStep`, position-threaded. -/
partial def simpStepT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result := do
  match e with
  | .mdata m e' => let r ← simpT ref (pos.push 0) e'
                   return { r with expr := mkMData m r.expr }
  | .proj ..     => simpProjT ref pos e
  | .app ..      => simpAppT ref pos e
  | .lam ..      => simpLambdaT ref pos e
  | .forallE ..  => simpForallT ref pos e
  | .letE ..     => simpLetT ref pos e
  | .const ..    => simpConstT ref pos e
  | .bvar ..     => unreachable!
  | .sort ..     => return { expr := e }
  | .lit ..      => return { expr := e }
  | .mvar ..     => return { expr := (← instantiateMVars e) }
  | .fvar ..     =>
    let e' ← reduceFVar' (← Simp.getConfig) (← Simp.getSimpTheorems) e
    unless e' == e do
      ref.modify (·.push (.defeq pos .zeta none e e' (← captureEvCtx ref)))
    return { expr := e' }

/-- SOURCE: Main.lean:677-712 `Simp.simpLoop`, position-threaded.

`cacheResult` is dropped: a cached `Result` is keyed on the expression alone, so
reusing it at a second position would either log that position's events nowhere
or log them at the first position.  A position-exact trace and an
expression-keyed result cache are incompatible; correctness wins. -/
partial def simpLoopT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result :=
  withIncRecDepth do
    let cfg ← Simp.getConfig
    if (← get).numSteps > cfg.maxSteps then
      throwError "`simp` failed: maximum number of steps exceeded"
    else
      checkSystem "simp"
      modify fun s => { s with numSteps := s.numSteps + 1 }
      match (← withPos ref pos (Simp.pre e)) with
      | .done r  => return r
      | .visit r => r.mkEqTrans (← simpLoopT ref pos r.expr)
      | .continue none => visitPreContinue cfg { expr := e }
      | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Simp.Config) (r : Simp.Result) : SimpM Simp.Result := do
    -- SOURCE: Main.lean:695 — **one** `reduceStep`, not a fixpoint.  Looping to
    -- a fixpoint here would charge the `maxSteps` budget once per reduction
    -- *chain* instead of once per reduction, so a cutoff would land in a
    -- different place than stock (REVIEW-4 minor 7).
    let eNew ← reduceOnce ref pos r.expr
    if eNew != r.expr then
      let r := { r with expr := eNew }
      r.mkEqTrans (← simpLoopT ref pos r.expr)
    else
      let r ← r.mkEqTrans (← simpStepT ref pos r.expr)
      visitPost cfg r
  visitPost (cfg : Simp.Config) (r : Simp.Result) : SimpM Simp.Result := do
    match (← withPos ref pos (Simp.post r.expr)) with
    | .done r' => r.mkEqTrans r'
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkEqTrans r')
  visitPostContinue (cfg : Simp.Config) (r : Simp.Result) : SimpM Simp.Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkEqTrans (← simpLoopT ref pos r.expr)
    return r

/-- SOURCE: Main.lean:716-720 `Simp.simpImpl`, position-threaded.  This is the
fork's entry point and replaces every recursive `Simp.simp` call. -/
partial def simpT (ref : TraceRef) (pos : Pos) (e : Expr) : SimpM Simp.Result :=
  withIncRecDepth do
    if (← isProof e) then
      return { expr := e }
    simpLoopT ref pos e

end

end ExplicitLean.SimpTrace
