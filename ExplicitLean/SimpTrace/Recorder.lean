/-
Recorder: wraps the stock `Simp.Methods` so every firing is logged into the
forked traversal's trace buffer **at the position the traversal is currently
visiting**.

The position is not reconstructed.  `ExplicitLean/SimpTrace/Traversal.lean`
sets `TraceState.pos` immediately before it hands control to a stock method, so
when `pre`/`post`/`dpre`/`dpost` fire, the exact `SubExpr.Pos` of the subterm
they are rewriting is already in the buffer.  There is no search anywhere in
this module.

Recorder machinery only.  Never imported by translated Mathlib source.
-/

module

public meta import Lean
public meta import ExplicitLean.SimpTrace.Types
public meta import ExplicitLean.SimpTrace.Traversal
public meta import ExplicitLean.SimpTrace.Position

public meta section

namespace ExplicitLean.SimpTrace

open Lean Meta Elab

/-! ### Attribution

A firing's origin is read from `usedTheorems`, which grows by exactly the
origins the procedure registered.  When it does not grow — simp had already
recorded that origin earlier in the run — we probe the candidate theorems
individually with stock `Simp.tryTheoremWithExtraArgs?` to name the exact one.

When neither succeeds the firing is a computed equation: the spec's `eq` kind,
whose `by` is decided by a scratch check.  It is **never** an abort.  That is
REVIEW-3 C1: the previous recorder threw on any unattributable firing, so
ordinary literal arithmetic, matcher reduction and `Option.getD` on a literal
all failed on goals stock `simp` proves.
-/

/-- How many arguments the origin's own rewrite left-hand side takes, or `none`
when its statement cannot be read.  Used to tell a lemma that rewrote a whole
application from one simp matched against a prefix and reapplied. -/
def lhsArity? (o : Origin) (inv : Bool) (prop? : Option Bool) :
    Simp.SimpM (Option Nat) := do
  -- A Prop-valued lemma rewrites the proposition itself, so its "left-hand
  -- side" is the whole statement and there is no prefix matching to undo.
  if prop?.isSome then return none
  let type? : Option Expr ← match o with
    | .decl declName _ _ => pure ((← getEnv).find? declName |>.map (·.type))
    | .fvar fvarId => pure ((← getLCtx).find? fvarId |>.map (·.type))
    | _ => pure none
  let some type := type? | return none
  try
    forallTelescopeReducing type fun _ concl => do
      let concl ← whnfR concl
      let sides? :=
        if let some (_, l, r) := concl.eq? then some (l, r)
        else if let some (l, r) := concl.iff? then some (l, r) else none
      let some (l, r) := sides? | return none
      return some ((if inv then r else l).getAppNumArgs)
  catch _ => return none

/-- Deepen `pos` into the function of an application for each trailing argument
that `before` and `after` share.

simp matches a lemma against a *prefix* of an application and reapplies the
remaining arguments, so the node that actually changed is `f` in `f a₁ ... aₙ`,
not the application.  Counting the shared trailing arguments recovers how far
down the rewritten node sits.  Nothing is guessed: it stops as soon as a pair
differs, and an `after` that is not an application of the same arity leaves the
position alone. -/
def descendToRewritten (lhsArity : Nat) (pos : Pos) (before after : Expr) :
    Pos × Expr × Expr := Id.run do
  let n := before.getAppNumArgs
  -- `lhsArity` is how many arguments the lemma's own left-hand side takes.
  -- Only the surplus is what simp reapplied; an equal arity means the lemma
  -- rewrote this whole application, which is the common case (`h : ∀ x, f x =
  -- g x` rewriting `f a` to `g a` leaves `a` shared without being extra).
  -- Counting shared trailing arguments alone cannot tell the two apart.
  if n == 0 || after.getAppNumArgs != n || lhsArity >= n then
    return (pos, before, after)
  let extra := n - lhsArity
  let bs := before.getAppArgs
  let as := after.getAppArgs
  -- Those surplus arguments must actually be untouched; if simp changed one,
  -- it did not simply reapply them and the node really is this application.
  for i in [0:extra] do
    let j := n - 1 - i
    if bs[j]! != as[j]! then return (pos, before, after)
  let b := mkAppN before.getAppFn (bs.extract 0 lhsArity)
  let a := mkAppN after.getAppFn (as.extract 0 lhsArity)
  return (pos ++ Array.replicate extra 0, b, a)

/-- The new origins a procedure registered, in registration order. -/
def newOrigins (usedBefore usedAfter : Simp.UsedSimps) : Array Origin :=
  usedAfter.toArray.filter fun o => !usedBefore.contains o

/--
Identify which simp theorem rewrote `before` to `after`, by probing the
candidate theorems individually with stock `Simp.tryTheorem*?`.  Used only when
`usedTheorems` did not grow, so no attribution is lost to simp's caching.
-/
def reattribute? (before after : Expr) (post : Bool) :
    Simp.SimpM (Option (Origin × Bool)) := do
  for thms in (← readThe Simp.Context).simpTheorems do
    let tree := if post then thms.post else thms.pre
    let candidates ← Simp.withSimpIndexConfig <| tree.getMatchWithExtra before
    let candidates := candidates.insertionSort fun a b => a.1.priority > b.1.priority
    for (thm, numExtraArgs) in candidates do
      if thms.erased.contains thm.origin then continue
      let r? ← try
          Simp.tryTheoremWithExtraArgs? before thm numExtraArgs
        catch _ => pure none
      if let some r := r? then
        if r.expr == after then
          match thm.origin with
          | .decl n p inv => return some (.decl n p inv, inv)
          | o => return some (o, false)
  return none

/-! ### The `prop` flag (spec amendment; REVIEW-3 M5)

simp uses a Prop-valued lemma `h : P` as the rewrite `P ↝ True` (`eq_true h`)
and `h : ¬P` as `P ↝ False` (`eq_false h`).  The trace must say so, or a replay
generator elaborates the name and finds neither an `Eq` nor an `Iff` — which is
exactly what T2 reported on `exists_eq'` and `List.not_mem_nil`.

We decide the flag from the origin's own declared type: strip the binders, and
if what remains is neither `Eq` nor `Iff`, the lemma is Prop-valued.  `after`
then says which of `True`/`False` simp rewrote to.
-/

/-- The local a stored simp-theorem proof was built from, together with the
arguments it was applied to and whether the wrapper reversed the direction.

simp stores a hypothesis's proof already instantiated and wrapped: `h a b` for a
∀-quantified `h`, `eq_true (h a)` for a Prop-valued one, `And.left h` for a
conjunct, and under a `.lam` binder when the hypothesis is quantified.  The head
fvar is the local; the applied arguments are what a replayer must supply.

`Iff.mp`/`Iff.mpr` are **not** walked: `Iff.mp h hp` takes the iff `h` *and* a
proof `hp` of its left side, so `appArg!` reaches `hp`, which is not the
hypothesis the rewrite is by (REVIEW-7 5).  `Eq.symm`/`Iff.symm` are walked but
flip the direction, for the same reason the simproc path does. -/
partial def proofLocal? (proof : Expr) :
    Option (Origin × Array Expr × Bool × String) :=
  go proof false
where
  /-- The fourth component is the projection suffix walked through on the way
  to the local (`".2.1"` for `h.2.1`).  It is part of the *name*: `simp [h.2.1]`
  with `h : p ∧ q ∧ r` rewrites by the conjunct, and a name of plain `h` would
  tell a replayer to rewrite by the whole conjunction (REVIEW-9 2). -/
  go (e : Expr) (inv : Bool) : Option (Origin × Array Expr × Bool × String) :=
    match e with
    -- A quantified hypothesis's proof is stored under binders.
    -- A quantified hypothesis's proof is stored under binders.  The arguments
    -- it is applied to below then reference those binders, so they are loose
    -- bvars here, not terms a replayer could write; unification recovers them
    -- from the subterm instead, so we keep the local and drop the arguments.
    | .lam _ _ body _ =>
      (go body inv).map fun (o, _, i, pr) => (o, #[], i, pr)
    | _ =>
      match e.getAppFn with
      -- A beta-redex: simp stores `(fun x => ...) a`, so look inside the
      -- function rather than treating the redex as opaque.
      | .lam .. => go e.getAppFn.headBeta inv
      | .fvar fvarId => some (.fvar fvarId, e.getAppArgs, inv, "")
      | .const n _ =>
        if n == ``Eq.symm || n == ``Iff.symm then
          if e.getAppNumArgs == 0 then none else go e.appArg! (!inv)
        else if n == ``And.left || n == ``And.right then
          -- Record which conjunct, innermost last: `h.2.1` is
          -- `And.left (And.right h)`, walked outside-in, so the suffix built
          -- here reads `.2` then `.1` -- the order the user wrote.
          if e.getAppNumArgs == 0 then none else
            let comp := if n == ``And.left then ".1" else ".2"
            (go e.appArg! inv).map fun (o, a, i, pr) => (o, a, i, pr ++ comp)
        else if n == ``eq_true || n == ``eq_false || n == ``propext
                || n == ``of_eq_true then
          if e.getAppNumArgs == 0 then none else go e.appArg! inv
        else
          -- A *global* constant the user applied explicitly (`@xor_not_right a`
          -- in `simp [← @xor_not_right a]`): a legitimate, replayable origin,
          -- so it resolves to the declaration rather than being classified.
          some (.decl n true false, e.getAppArgs, inv, "")
      | _ => none

/- Resolve the proposition proof hidden inside a source-local simp theorem.
   A source argument such as `h` can elaborate to a generated theorem
   application (`Bool.of_not_eq_true h`) rather than a theorem whose head is
   the local fvar.  The source registration already authenticated that the
   argument head is local; within that boundary, retain the actual proposition
   fvar instead of treating the generated wrapper as an ordinary rw lemma. -/
partial def propositionFVar? (e : Expr) : MetaM (Option FVarId) := do
  match e with
  | .fvar fvarId =>
    match (← getLCtx).find? fvarId with
    | some localDecl =>
      if ← isProp localDecl.type then return some fvarId
      return none
    | none => return none
  | .app fn arg =>
    match ← propositionFVar? arg with
    | some fvarId => return some fvarId
    | none => propositionFVar? fn
  | .mdata _ body => propositionFVar? body
  | _ => return none

/-- Keep only those recorded arguments that sit at an *explicit* binder of the
origin's own type, in order.  Named-argument syntax can fill an implicit binder
(`heq_comm (a := a)`), and a replayer cannot write such an argument
positionally; unification recovers it instead. -/
def explicitOnly (o : Origin) (args : Array Expr) : MetaM (Array Expr) := do
  if args.isEmpty then return args
  let type? : Option Expr ← match o with
    | .decl declName _ _ => pure ((← getEnv).find? declName |>.map (·.type))
    | .fvar fvarId => pure ((← getLCtx).find? fvarId |>.map (·.type))
    | _ => pure none
  let some type := type? | return args
  forallTelescopeReducing type fun xs _ => do
    let mut out : Array Expr := #[]
    for i in [0:args.size] do
      if h : i < xs.size then
        let some decl ← xs[i].fvarId!.findDecl? | return args
        if decl.binderInfo == .default then out := out.push args[i]!
    return out

/--
Resolve an `Origin.stx` to the local hypothesis it elaborated to, when it is one.

`simp [h]` records the *syntax* the user wrote; `simp [*]` records an
`Origin.fvar`.  The spec is unconditional — a rewrite by a local hypothesis
carries the `local` object and, when Prop-valued, the `prop` flag — so the two
forms must not disagree.

The fvar is read off the simp theorem's **proof term**, never guessed from the
syntax's characters: a character whitelist dropped every non-ASCII name (`hα`,
`h₃`, `«quoted»`), losing `local` and `prop` for names Mathlib uses constantly
(REVIEW-6 1).  Matching is on `Origin.stx`'s unique `id` rather than structural
`==`, because `Origin` compares its stored `Syntax` and the trace's copy is not
the tree's.
-/
def resolveStxOrigin (o : Origin) (sourceHeadLocal : Bool := false) :
    Simp.SimpM (Origin × Array Expr × Bool × String) := do
  let .stx id _ := o | return (o, #[], false, "")
  for thms in (← readThe Simp.Context).simpTheorems do
    for sthm in thms.pre.values ++ thms.post.values do
      if let .stx id' _ := sthm.origin then
        if id' == id then
          match proofLocal? sthm.proof with
          | some (resolved, args, inv, proj) =>
            if sourceHeadLocal then
              if let some fvarId ← propositionFVar? sthm.proof then
                return (.fvar fvarId, #[], false, proj)
            -- Keep only the arguments at *explicit* binders.  `heq_comm
            -- (a := a) (b := b)` names two of four implicit binders, and
            -- `getAppArgs` returns all four; recording them would tell a
            -- replayer to write `rw [heq_comm α β a b]`, which does not
            -- elaborate.  Implicit ones are recovered by unification, so they
            -- are dropped (REVIEW-9 2).
            let args ← explicitOnly resolved args
            return (resolved, args, inv, proj)
          -- The argument elaborated to something that is not a local (a term,
          -- a global applied to arguments): leave the origin as written, and
          -- the caller classifies it — "unresolved" is never a silent pass.
          | none => return (o, #[], false, "")
  return (o, #[], false, "")

/-- Is this origin's statement an equation or an iff (after its binders)? -/
def originIsEquational (o : Origin) (lctx : LocalContext) (insts : LocalInstances) :
    MetaM Bool := do
  let type? : Option Expr ← withLCtx lctx insts do
    match o with
    | .decl declName _ _ =>
      match (← getEnv).find? declName with
      | some ci => pure (some ci.type)
      | none => pure none
    | .fvar fvarId =>
      match lctx.find? fvarId with
      | some d => pure (some d.type)
      | none => pure none
    | _ => pure none
  let some type := type? | return true
  withLCtx lctx insts do
    forallTelescopeReducing type fun _ body => do
      let body ← whnfR body
      return body.isEq || body.isAppOf ``Iff

/-- The `prop` flag for a rewrite, per the amended spec: `some true` when the
lemma was used as `P = True`, `some false` when as `P = False`, `none` when the
lemma really is an equation or an iff. -/
def propFlag? (o : Origin) (after : Expr) (lctx : LocalContext)
    (insts : LocalInstances) : MetaM (Option Bool) := do
  if ← originIsEquational o lctx insts then return none
  if after.isTrue then return some true
  else if after.isFalse then return some false
  else return none

/-! ### T16 operational theorem matching

The stock matcher below is copied at the small boundary where it constructs a
theorem rewrite.  It deliberately records only binder ordinals and provenance
classes.  The assigned metavariables are used to construct the stock result,
but are never inspected for serialization.  `Simp.Result.proof?` remains an
internal parity oracle only and is not consulted by this path.
-/

def originLabel (o : Origin) : String :=
  match o with
  | .decl n _ _ => "decl:" ++ n.toString
  | .fvar f => "local:" ++ f.name.toString
  | .stx _ _ => "source"
  | .other n => "other:" ++ n.toString

/-! ### Direct source-argument lookup

`Origin.stx` retains the parser node passed to stock argument elaboration.  We
match that node against the source side table by its canonical source range.
The table was populated before `mkSimpContext`; this lookup therefore does not
walk, count, or otherwise depend on the theorem table.  One source argument can
produce several `SimpTheorem`s (for example conjunction projections), and every
one carries the same `Origin.stx` range and hence the same direct `argId`. -/
def sourceArgInfo? (ref : TraceRef) (o : Origin) : Simp.SimpM (Option SourceArg) := do
  let .stx _ originStx := o | return none
  let some start := originStx.getPos? (canonicalOnly := true) | return none
  let some stop := originStx.getTailPos? (canonicalOnly := true) | return none
  let start := start.byteIdx
  let stop := stop.byteIdx
  let st ← ref.get
  for arg in st.sourceArgs do
    if arg.startByte == start && arg.endByte == stop then return some arg
  return none

def originalType? (o : Origin) : Simp.SimpM (Option Expr) := do
  match o with
  | .decl n _ _ => return (← getEnv).find? n |>.map (·.type)
  | .fvar f => return (← getLCtx).find? f |>.map (·.type)
  | _ => return none

/-- Name the construction combinator used to turn the source theorem into the
indexed equation.  The source type is the authoritative input: generated aux
lemma bodies are intentionally not decompiled. -/
def preprocessOperations (ref : TraceRef) (sourceOrigin : Origin)
    (constructionOrigin : Origin) (processedType : Expr) : Simp.SimpM (Array String) := do
  let mut out : Array String := #[]
  let reverse ← match sourceOrigin with
    | .decl _ _ inv => pure inv
    | .stx .. =>
      let info? ← sourceArgInfo? ref sourceOrigin
      pure ((info?.map (·.direction == "rev")).getD false)
    | _ => pure false
  if reverse then out := out.push "reverse"
  match ← originalType? constructionOrigin with
  | none => return out.push "processed"
  | some original =>
    let op ← forallTelescopeReducing original fun _ body => do
      let body ← whnfR body
      if body.isEq then
        return "direct_eq"
      if body.isAppOf ``Iff then
        return "iff_propext"
      if body.not?.isSome then
        return "not_to_false"
      if let some (left, right) := body.and? then
        let lhs := processedType.appFn!.appArg!
        if lhs == left then
          return "conjunction_left"
        if lhs == right then
          return "conjunction_right"
        return "conjunction_projection"
      return "prop_to_true"
    return out.push op

def synthInstanceOperational (thmId : Origin) (x type : Expr) : Simp.SimpM Bool := do
  match (← trySynthInstance type) with
  | LOption.some val =>
    if ← withReducibleAndInstances <| isDefEq x val then
      return true
    trace[Meta.Tactic.simp.discharge] "{← ppOrigin thmId}, failed to assign instance"
    return false
  | _ =>
    trace[Meta.Tactic.simp.discharge] "{← ppOrigin thmId}, failed to synthesize instance"
    return false

/-- Mirror stock `synthesizeArgs`, retaining only why each binder was filled. -/
def synthesizeArgsOperational (thmId : Origin) (bis : Array BinderInfo)
    (xs : Array Expr) : Simp.SimpM (Bool × Array BinderDerivation × Array DischargeDerivation) := do
  let mut binders : Array BinderDerivation := #[]
  let mut discharges : Array DischargeDerivation := #[]
  let skipAssignedInstances := tactic.skipAssignedInstances.get (← getOptions)
  for x in xs, bi in bis do
    let i := binders.size
    let type ← inferType x
    let initial ← instantiateMVars x
    if !skipAssignedInstances && bi.isInstImplicit then
      unless ← synthInstanceOperational thmId x type do
        return (false, binders, discharges)
      binders := binders.push ⟨i, "instance"⟩
      continue
    if initial.isMVar then
      if (← isClass? type).isSome then
        if ← synthInstanceOperational thmId x type then
          binders := binders.push ⟨i, "instance"⟩
          continue
      if ← isProp type then
        unless ← Simp.discharge?' thmId x type do
          return (false, binders, discharges)
        -- The discharger's nested recorder frame is attached by the wrapper;
        -- only its ordinal and success provenance belong in this summary.
        binders := binders.push ⟨i, "discharge"⟩
        discharges := discharges.push ⟨i, "configured-or-default"⟩
        continue
    binders := binders.push ⟨i, "matched"⟩
  return (true, binders, discharges)

def derivationFor (_ref : TraceRef) (o : Origin) (constructionOrigin : Origin)
    (processedType : Expr)
    (redex : Pos) (extraArgs : Nat) (binders : Array BinderDerivation)
    (discharge : Array DischargeDerivation) : Simp.SimpM RuleDerivation := do
  let sourceArg? ← sourceArgInfo? _ref o
  let sourceKind := match o with
    | .stx _ _ => some "simp-argument"
    | .decl _ _ _ => none
    | .fvar _ => some "local-evidence"
    | .other _ => none
  let preprocess ← preprocessOperations _ref o constructionOrigin processedType
  let origin := originLabel constructionOrigin
  let result : RuleDerivation := { origin := origin }
  let result := { result with source? := sourceKind }
  let result := { result with argId? := sourceArg?.map (fun a : SourceArg => a.argId) }
  let result := { result with direction? := sourceArg?.map (fun a : SourceArg => a.direction) }
  let result := { result with preprocess := preprocess }
  let result := { result with redex := redex }
  let result := { result with extraArgs := extraArgs }
  let result := { result with binders := binders }
  let result := { result with discharge := discharge }
  return result

/-- A copy of `Simp.tryTheoremCore` with event-time provenance capture. -/
def tryTheoremOperational? (ref : TraceRef) (_tag : String) (e : Expr)
    (thm : SimpTheorem) (numExtraArgs : Nat) (rflOnly : Bool) :
    Simp.SimpM (Option (Simp.Result × RuleDerivation × Pos × Expr × Expr)) := do
  withNewMCtxDepth do
    let val ← thm.getValue
    let type ← inferType val
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    if rflOnly && !(thm.rfl || (backward.defeqAttrib.useBackward.get (← getOptions) && thm.backwardRfl)) then
      return none
    Simp.recordTriedSimpTheorem thm.origin
    let mut extraArgs : Array Expr := #[]
    let mut core := e
    for _ in *...numExtraArgs do
      extraArgs := extraArgs.push core.appArg!
      core := core.appFn!
    extraArgs := extraArgs.reverse
    unless ← Simp.withSimpMetaConfig <| isDefEq lhs core do
      return none
    let (ok, binders, discharges) ← synthesizeArgsOperational thm.origin bis xs
    unless ok do return none
    let proof ← instantiateMVars (mkAppN val xs)
    if ← hasAssignableMVar proof then return none
    let rhs := (← instantiateMVars type).appArg!
    if (← instantiateMVars core) == rhs then return none
    if thm.perm && !(← acLt rhs core .reduceSimpleOnly) then return none
    if ← hasAssignableMVar rhs then return none
    let rhs ← if type.hasBinderNameHint then rhs.resolveBinderNameHint else pure rhs
    let implicitDefEq := thm.rfl ||
      (thm.backwardRfl && backward.defeqAttrib.useBackward.get (← getOptions))
    let proof? := if implicitDefEq && (← Simp.getConfig).implicitDefEqProofs
      then none else some proof
    let coreResult : Simp.Result := { expr := rhs, proof? }
    let result ← coreResult.addExtraArgs extraArgs
    let pos := (← ref.get).pos
    let redexPos := pos ++ Array.replicate numExtraArgs 0
    let env ← getEnv
    let sourceInfo? ← sourceArgInfo? ref thm.origin
    let (resolvedConstructionOrigin, _, _, _) ←
      resolveStxOrigin thm.origin ((sourceInfo?.map (·.headLocal)).getD false)
    let constructionOrigin := match resolvedConstructionOrigin with
      | .stx .. =>
        -- A source simp argument is stored as an already-applied theorem
        -- expression.  Its head declaration is the construction input; using
        -- that declaration's source type recovers the preprocessing operation
        -- without decompiling the resulting `Simp.Result.proof?`.
        match val.getAppFn with
        | .const n _ => if env.find? n |>.isSome then .decl n true false else
            match sourceInfo? with
            | some info => if !info.headLocal then
                match info.headName? with
                | some n => if env.find? n |>.isSome then .decl n true false else thm.origin
                | none => thm.origin
              else thm.origin
            | none => thm.origin
        | _ =>
          match sourceInfo? with
          | some info => if !info.headLocal then
              match info.headName? with
              | some n => if env.find? n |>.isSome then .decl n true false else thm.origin
              | none => thm.origin
            else thm.origin
          | none => thm.origin
      | o => o
    let derivation ← derivationFor ref thm.origin constructionOrigin type redexPos
      numExtraArgs binders discharges
    Simp.recordSimpTheorem thm.origin
    return some (result, derivation, redexPos, core, rhs)

def rewriteOperational? (ref : TraceRef) (tag : String) (e : Expr)
    (tree : SimpTheoremTree) (erased : PHashSet Origin) (rflOnly : Bool) :
    Simp.SimpM (Option Simp.Result) := do
  let useBackward := backward.defeqAttrib.useBackward.get (← getOptions)
  let tryCandidate (thm : SimpTheorem) (extra : Nat) : Simp.SimpM (Option Simp.Result) := do
    checkSystem "simp"
    if erased.contains thm.origin then return none
    if rflOnly && !(thm.rfl || (useBackward && thm.backwardRfl)) then
      return none
    if let some (result, derivation, pos, before, after) ←
        tryTheoremOperational? ref tag e thm extra rflOnly then
      let evCtx ← captureEvCtx ref
      let sides := (← ref.get).pendingSide
      ref.modify fun s => { s with pendingSide := #[] }
      let inv := match thm.origin with | .decl _ _ i => i | _ => false
      let sourceInfo? ← sourceArgInfo? ref thm.origin
      let (resolved, rargs, rinv, rproj) ←
        resolveStxOrigin thm.origin ((sourceInfo?.map (·.headLocal)).getD false)
      let prop? ← propFlag? resolved result.expr evCtx.lctx evCtx.insts
      ref.modify (·.push (.rw pos thm.origin (inv != rinv) prop? before after evCtx
        rargs sides none resolved rproj (some derivation)))
      return some result
    return none
  if (← Simp.getConfig).index then
    let candidates ← Simp.withSimpIndexConfig <| tree.getMatchWithExtra e
    let candidates := candidates.insertionSort fun a b => a.1.priority > b.1.priority
    for (thm, extra) in candidates do
      if let some result ← tryCandidate thm extra then return some result
  else
    let (theorems, numArgs) ← Simp.withSimpIndexConfig <| tree.getMatchLiberal e
    let theorems := theorems.insertionSort fun a b => a.priority > b.priority
    for thm in theorems do
      if erased.contains thm.origin then continue
      if rflOnly && !(thm.rfl || (useBackward && thm.backwardRfl)) then continue
      let lhsNumArgs ← withNewMCtxDepth do
        let val ← thm.getValue
        let type ← inferType val
        let (_, _, type) ← forallMetaTelescopeReducing type
        let type ← whnf (← instantiateMVars type)
        return type.appFn!.appArg!.getAppNumArgs
      if let some result ← tryCandidate thm (numArgs - lhsNumArgs) then
        return some result
  return none

def noteProcGoal (ref : TraceRef) (e : Expr) : Simp.SimpM Unit := do
  ref.modify fun s =>
    if s.procEvents.size > 0 && s.procGoals.size > 0
       && (s.procGoals.getD (s.procGoals.size - 1) none).isNone then
      { s with procGoals := s.procGoals.set! (s.procGoals.size - 1) (some e) }
    else s

def rewritePreOperational (ref : TraceRef) : Simp.Simproc := fun e => do
  noteProcGoal ref e
  for thms in (← Simp.getContext).simpTheorems do
    if let some r ← rewriteOperational? ref "pre" e thms.pre thms.erased false then
      return .visit r
  return .continue

def rewritePostOperational (ref : TraceRef) : Simp.Simproc := fun e => do
  noteProcGoal ref e
  for thms in (← Simp.getContext).simpTheorems do
    if let some r ← rewriteOperational? ref "post" e thms.post thms.erased false then
      return .visit r
  return .continue

/-! ### Lemma-headed simproc proofs (spec amendment 408a39b)

A simproc whose returned proof is an application of **one lemma** is not an `eq`
step: it is an ordinary `rw` whose `name` is that lemma, with the discharged
condition as a `side` sub-trace and `"source"` naming the simproc.  `reduceIte`
returns `ite_cond_eq_true α c inst a b (h : c = True)`, `reduceDIte` returns
`dite_cond_eq_true ...`; both are genuine equation lemmas, and because the
`Decidable` instance is an *argument of `ite`* rather than part of the rewrite
motive, `rw [ite_cond_eq_true a b (eq_true h)]` is well-typed ordinary Lean.

The test is generic, never a table of simproc names: take the proof's head
constant and walk its arguments against the lemma's own binder telescope.  Each
explicit argument must be

* a subterm of the term being rewritten (the `ite`'s branches and condition),
* an instance argument (`instImplicit`, or a class-typed argument), or
* a proof — which is the discharged condition, and becomes the `side` entry.

If any explicit argument is none of these, the proof is not a plain lemma
application at this position and we fall back to `eq`/unresolved.  Implicit
arguments are unification's business and are not checked.
-/

/-- The outcome of inspecting a simproc's proof term. -/
inductive ProofShape where
  /-- One lemma applied; `name` is it.  `proofArgs` are the explicit arguments
  that are proofs, i.e. the conditions the discharger established.
  `explicitArgs` is *every* explicit argument, in the lemma's own order: replay
  writes `rw [name a₁ a₂ ...]` and must supply what simp supplied, and an
  explicit *instance*-typed argument in particular cannot be left to synthesis,
  which may pick a different instance than simp used (REVIEW-6 2). -/
  | lemmaApp (name : Name) (proofArgs : Array Expr) (inv : Bool := false)
       (explicitArgs : Array Expr := #[])
  /-- Anything else: let the `rfl`/`decide` scratch check decide. -/
  | computed
  deriving Inhabited

/-- Is `a` a subterm of `e` (structurally)? -/
def isSubtermOf (a e : Expr) : Bool :=
  Option.isSome <| e.find? fun s => s == a

/-- Heads that are *plumbing*: they move a proof between `Eq`, `Iff` and `True`
rather than rewriting anything, so a proof headed by one is never "one lemma
applied".  `propext` is the one REVIEW-5 found: it has a single explicit
argument and that argument is a proof, so the generic walk below happily
classified `propext h` as a rewrite by `propext` — a step no replayer can
execute, since `rw [propext]` is not a rewrite. -/
def isPlumbingHead (n : Name) : Bool :=
  n == ``Eq.trans || n == ``Eq.symm || n == ``Eq.mpr || n == ``Eq.mp
  || n == ``propext || n == ``Iff.symm || n == ``Iff.trans || n == ``Iff.intro
  || n == ``Iff.mp || n == ``Iff.mpr || n == ``Iff.rfl || n == ``Iff.of_eq
  || n == ``of_eq_true || n == ``of_eq_false || n == ``eq_self
  || n == ``eq_true || n == ``eq_false || n == ``iff_of_eq
  || n == ``Eq.ndrec || n == ``Eq.rec || n == ``Eq.subst || n == ``Eq.substr
  || n == ``id || n == ``trans

/--
Classify a simproc's proof term per the amended spec.  `target` is the term the
simproc rewrote, so "a subterm of the position" is decided against it.
-/
partial def classifyProof (target : Expr) (proof : Expr) : MetaM ProofShape := do
  let .const declName _ := proof.getAppFn | return .computed
  -- An `Iff`-returning simproc wraps its proof in `propext`.  The rewriting
  -- lemma is then the *inner* proof's head, and the rewrite is an iff rewrite,
  -- which `rw` performs exactly as it does an equational one.  Unwrap one level
  -- and classify that; if the inner proof is not itself a single lemma
  -- application, the firing stays `computed` and becomes an `eq` step whose
  -- `by` the scratch check decides (REVIEW-5 2).
  if declName == ``propext && proof.getAppNumArgs == 3 then
    return ← classifyProof target proof.appArg!
  -- `Iff.symm h` proves the iff in the other direction, so the lemma inside is
  -- the rewriting one and the rewrite is reversed.  `Iff.trans` composes two
  -- lemmas and names no single one, so it stays unresolved.
  if declName == ``Iff.symm && proof.getAppNumArgs == 3 then
    match ← classifyProof target proof.appArg! with
    | .lemmaApp n pargs inv eargs => return .lemmaApp n pargs (!inv) eargs
    | .computed => return .computed
  -- `Eq.symm (propext (L ...))`: one lemma, applied in reverse.
  if declName == ``Eq.symm && proof.getAppNumArgs == 4 then
    match ← classifyProof target proof.appArg! with
    | .lemmaApp n pargs inv eargs => return .lemmaApp n pargs (!inv) eargs
    | .computed => return .computed
  if isPlumbingHead declName then
    return .computed
  let some ci := (← getEnv).find? declName | return .computed
  let args := proof.getAppArgs
  -- Walk the lemma's own telescope so we know which arguments are explicit.
  let shape? ← forallTelescopeReducing ci.type fun xs _ => do
    if xs.size < args.size then return none
    let mut proofArgs : Array Expr := #[]
    let mut explicitArgs : Array Expr := #[]
    for i in [0:args.size] do
      let arg := args[i]!
      let some decl ← xs[i]!.fvarId!.findDecl? | return none
      match decl.binderInfo with
      | .implicit | .strictImplicit | .instImplicit => continue
      | .default =>
        -- A replayer writes `rw [name a₁ a₂ ...]` and must supply exactly what
        -- simp supplied, so every explicit *value* argument is recorded in
        -- order.  A proof argument is **not** one of them: it is a condition
        -- the discharger established and is carried as a `side` sub-trace, so
        -- putting it in `args` would tell the replayer to write out a proof
        -- term it is supposed to prove.
        if ← isProof arg then
          proofArgs := proofArgs.push arg
        else if isSubtermOf arg target then
          explicitArgs := explicitArgs.push arg
          continue
        else if (← Meta.isClass? (← inferType arg)).isSome then
          explicitArgs := explicitArgs.push arg
          -- An explicit *instance*-typed argument: synthesis may pick a
          -- different instance than simp did, so it must be in `args`. It is,
          -- above; accepting it here is now safe.
          continue
        else
          -- Neither a subterm of the position, an instance, nor a proof: the
          -- lemma is not being applied *to this position*, so replay could not
          -- reconstruct the argument.
          return none
    return some (proofArgs, explicitArgs)
  match shape? with
  | some (proofArgs, explicitArgs) =>
    return .lemmaApp declName proofArgs false explicitArgs
  | none => return .computed

/--
Which spec close form closes the goal `e`, if any.

`describeProof` must not invent a `by` (round 3's principle), but it must also
not classify a goal the spec *can* close: after the recorded steps a side goal
is very often literally `True` or `¬False`, and classifying those made 7 of the
corpus's 8 classified side conditions false positives (REVIEW-8 1).  The
question to ask is what the goal **is**, not what its proof term looks like.
-/
def goalCloseForm? (e : Expr) : Simp.SimpM (Option String) := do
  let e ← instantiateMVars e
  try
    let e ← withReducible <| whnfR e
    -- `True`: the spec's `true_intro`.
    if e.isConstOf ``True then return some "true_intro"
    -- `¬False`, i.e. `False → False`, and any `False → _`: refutable by empty
    -- pattern matching, which is the spec's `nofun`.
    if let some p := e.not? then
      if p.isConstOf ``False then return some "nofun"
    if let .forallE _ d _ _ := e then
      if (← withReducible <| whnfR d).isConstOf ``False then return some "nofun"
    -- `a = a` / `p ↔ p`: closed by reflexivity.
    if let some (_, lhs, rhs) := e.eq? then
      if ← withReducible <| isDefEq lhs rhs then return some "rfl"
    if let some (lhs, rhs) := e.iff? then
      if ← withReducible <| isDefEq lhs rhs then return some "rfl"
    -- A decidable ground proposition: the spec's `decide`.
    return none
  catch _ => return none

/-- Does `declName` applied to `args` elaborate?  A cheap scratch check that the
recorded argument list is one a replayer can actually write. -/
def checkArgsElaborate (declName : Name) (args : Array Expr) : MetaM Bool := do
  if args.isEmpty then return true
  try
    withoutModifyingState do
      let f ← mkConstWithFreshMVarLevels declName
      let _ ← inferType (mkAppN f args)
      pure true
  catch _ => pure false

/-! ### Bounded operational records for `reduceIte`/`reduceDIte`

The built-in procedures simplify their condition with a nested simp, then
choose one of four fixed semantic lemmas.  The fork routes these two
procedures through `simpT`; generic procedures still divert opaque nested
events into `procEvents`.  Replay those events structurally to identify the
branch, and record the constructor directly.  This deliberately does not look
at `Simp.Result.proof?`: the result is used only for the stock parity check,
while the derivation comes from the procedure's visible redex and condition
trace. -/

def eventExprPair? : Event → Option (Expr × Expr)
  | .rw _ _ _ _ before after .. => some (before, after)
  | .eq _ _ before after .. => some (before, after)
  | .defeq _ _ _ before after .. => some (before, after)
  | .congr _ _ _ before after .. => some (before, after)
  | .transport _ _ _ _ before after .. => some (before, after)
  | .introCtx .. | .introCtxExit .. => none

def replayProcCondition (goal : Expr) (nested : Array Event) :
    Option (Expr × Array Event) := Id.run do
  let mut current := goal
  let mut located : Array Event := #[]
  for ev in nested do
    let some (before, after) := eventExprPair? ev | return none
    let some p := uniqueOccurrence? current before | return none
    let some next := replaceAt? current p after | return none
    located := located.push (ev.reposition p)
    current := next
  return some (current, located)

def mkIteConditionSide (goal : Expr) (truth : Expr) (nested : Array Event)
    (ctx : EvCtx) : Simp.SimpM (Option (SideRec × Bool)) := do
  let sideGoal ← mkEq goal truth
  match replayProcCondition sideGoal nested with
  | none => return none
  | some (after, events) =>
    let by_ ← goalCloseForm? after
    let complete := by_.isSome
    let rec_ : SideRec := .mk sideGoal events by_ ctx #[] sideGoal (some after)
    return some (rec_, complete)

/- Peel only the application arguments beyond the fixed five arguments of an
`ite`/`dite` core.  This is intentionally driven by the redex's application
arity, not by a search for a matching subterm. -/
def peelBoundedIteApplication (before after : Expr) :
    Option (Expr × Expr × Nat) := Id.run do
  let n := before.getAppNumArgs
  if n < 5 then return none
  let extra := n - 5
  let mut coreBefore := before
  let mut coreAfter := after
  for _ in [0:extra] do
    let (.app beforeFn beforeArg) := coreBefore | return none
    let (.app afterFn afterArg) := coreAfter | return none
    if beforeArg != afterArg then return none
    coreBefore := beforeFn
    coreAfter := afterFn
  return some (coreBefore, coreAfter, extra)

/- The bounded path is valid only when the procedure frame's observed goal is
the conditional's actual condition.  A later `reduceIte` call can occur after
forked traversal has already simplified that condition; such a call has no
condition frame of its own and must use the ordinary event path below. -/
def boundedIteCondition? (before after : Expr) : Option Expr :=
  match peelBoundedIteApplication before after with
  | some (coreBefore, _, _) =>
    if coreBefore.isAppOf ``ite || coreBefore.isAppOf ``dite then
      let args := coreBefore.getAppArgs
      if args.size >= 2 then some args[1]! else none
    else none
  | none => none

def emitBoundedIteStep (ref : TraceRef) (pos : Pos) (e : Expr) (r : Simp.Result)
    (evCtx : EvCtx) (side : Array SideRec) (src : Name)
    (diverted : Array Event) (procGoal? : Option Expr) : Simp.SimpM Unit := do
  let isDite := src == ``reduceDIte
  let constructorTrue := if isDite then ``dite_cond_eq_true else ``ite_cond_eq_true
  let constructorFalse := if isDite then ``dite_cond_eq_false else ``ite_cond_eq_false
  let expectedShape := if isDite then "dite" else "ite"
  let fail (reason : String) := do
    ref.modify (·.markUnresolved s!"simproc:{src}: {reason}")
  let (coreBefore, coreAfter, extraArgs) ← match peelBoundedIteApplication e r.expr with
    | some result => pure result
    | none => fail "conditional core or trailing application cannot be established"; return
  let corePos := pos ++ Array.replicate extraArgs 0
  let (condition, _selected, args) ←
    if isDite then
      let_expr dite _ c _ _ _ ← coreBefore
        | fail s!"{expectedShape} core missing"; return
      pure (c, coreAfter, #[])
    else
      let_expr ite _ c _ tb eb ← coreBefore
        | fail s!"{expectedShape} core missing"; return
      if coreAfter == tb then pure (c, coreAfter, #[tb, eb])
      else if coreAfter == eb then pure (c, coreAfter, #[tb, eb])
      else fail "result core is neither branch"; return
  let procGoal ← match procGoal? with
    | some goal => pure goal
    | none => fail "condition trace missing"; return
  unless procGoal == condition do
    fail "condition trace redex mismatch"; return
  let trueResult := replayProcCondition condition diverted
  let (conditionAfter, _) ← match trueResult with
    | some result => pure result
    | none => fail "condition trace could not be placed"; return
  let (truth, constructor, branch) ←
    if conditionAfter.isTrue then pure (mkConst ``True, constructorTrue, "true")
    else if conditionAfter.isFalse then pure (mkConst ``False, constructorFalse, "false")
    else fail "condition trace does not close to True or False"; return
  let (conditionSide, complete) ← match ← mkIteConditionSide condition truth diverted evCtx with
    | some result => pure result
    | none => fail "condition evidence missing"; return
  unless complete do fail "condition evidence is incomplete"
  let ctx ← captureEvCtx ref
  let origin : Origin := .decl constructor true false
  let source := some src
  let derivation : RuleDerivation :=
    { origin := "simproc:" ++ src.toString,
      source? := some "operational",
      redex := corePos,
      extraArgs := extraArgs,
      simproc? := some
        { source := src.toString, redex := corePos, extraArgs := extraArgs, branch := branch,
          constructor := constructor.toString } }
  ref.modify (·.push (.rw corePos origin false none coreBefore coreAfter ctx args
    (side.push conditionSide) source origin "" (some derivation)))

/- A cached simproc origin is not added to `usedTheorems` again.  The nested
condition frame is the identifying signal we retain for these two fixed
redexes, so recover the bounded source without consulting the result proof. -/
def inferBoundedIteSource? (e : Expr) (r : Simp.Result)
    (procGoal? : Option Expr) : Option Name :=
  if procGoal?.isNone then none
  else if e.isAppOf ``dite then some ``reduceDIte
  else if e.isAppOf ``ite then
    let args := e.getAppArgs
    if h : args.size >= 5 then
      let tb := args[3]!
      let eb := args[4]!
      if r.expr == tb || r.expr == eb then some ``reduceIte else none
    else none
  else none

def emitProcStep (ref : TraceRef) (pos : Pos) (e : Expr) (r : Simp.Result)
    (evCtx : EvCtx) (side : Array SideRec) (src? : Option Name)
    (diverted : Array Event := #[]) (procGoal? : Option Expr := none)
    (controlled : Bool := false) : Simp.SimpM Unit := do
  -- These two procedures are handled from their redex and diverted condition
  -- frame.  In particular, do this before the generic proof classifier below:
  -- their branch proof is not recorder input.
  if let some src := src? then
    if src == ``reduceIte || src == ``reduceDIte then
      let boundedCondition? := boundedIteCondition? e r.expr
      let bounded? := match procGoal?, boundedCondition? with
        | some goal, some condition => goal == condition
        | _, _ => controlled
      if bounded? then
        let goal? := match procGoal? with
          | some goal => some goal
          | none => boundedCondition?
        emitBoundedIteStep ref pos e r evCtx side src diverted goal?
        return
  let shape ← match r.proof? with
    | some proof => classifyProof e (← instantiateMVars proof)
    | none => pure .computed
  match shape with
  | .lemmaApp declName proofArgs inv explicitArgs =>
    -- Each proof argument is a condition the simproc established.  We already
    -- captured the discharger's own work as `side`; when we captured none, the
    -- condition came from somewhere else and we must name it honestly.
    let mut sides := side
    let mut unnamed : Array String := #[]
    if sides.isEmpty then
      -- One side goal per proof argument, each stated as that hypothesis's own
      -- instantiated type — the only place a side goal is built.  The
      -- discharger's diverted events belong to the *first* such condition (a
      -- simproc runs its nested `simp` on the one subterm it needs), so they
      -- are attached there, rebased onto that goal.
      let mut first := true
      for pa in proofArgs do
        let ty ← instantiateMVars (← inferType pa)
        -- The diverted events came from the simproc's nested `simp`, which
        -- calls *stock* `simpImpl`: the fork's `withPos` never runs inside it,
        -- so every one of them arrives at the frame root with `pos = []`.  A
        -- constant prefix would therefore give three rewrites of three
        -- different subterms the same position -- which elaborates and then
        -- rewrites the wrong subterm.  Recover each position from the subterm
        -- the event records, threading the goal so later steps see the earlier
        -- rewrites.  An event whose `before` is absent or occurs more than once
        -- is a genuine unknown: drop the whole side trace rather than guess,
        -- and let the caller classify it (REVIEW-9 1).
        let mut located : Array Event := #[]
        let mut cur := ty
        let mut locOk := true
        if first then
          for ev in diverted do
            let (before, after) := match ev with
              | .rw _ _ _ _ b a .. => (some b, some a)
              | .eq _ _ b a _ _ => (some b, some a)
              | .defeq _ _ _ b a _ => (some b, some a)
              | .congr _ _ _ b a _ _ _ => (some b, some a)
              | .transport _ _ _ _ b a _ _ _ _ _ => (some b, some a)
              | .introCtx .. | .introCtxExit .. => (none, none)
            match before, after with
            | some b, some a =>
              match uniqueOccurrence? cur b with
              | some q =>
                located := located.push (ev.reposition q)
                cur := (replaceAt? cur q a).getD cur
              | none => locOk := false
            | _, _ => locOk := false
        let evs := if first && locOk then located else #[]
        let unlocated := first && !locOk && !diverted.isEmpty
        first := false
        -- With steps recorded, the close is what the goal becomes *after* them;
        -- with none, it is what the goal already is.  Never a hardcoded form.
        -- The close describes the goal once *every* recorded step has been
        -- applied to it, so replay them against `ty` at their own positions.
        -- Reading the last event's `after` instead would hand `goalCloseForm?`
        -- a subterm (`False`) rather than the goal (`False = False`), which is
        -- what made `rfl`-closable conditions come out classified (REVIEW-9 1).
        let after := if evs.isEmpty then ty else cur
        if unlocated then
          -- The steps exist but their positions could not be recovered, so the
          -- trace cannot say *where* to rewrite.  Emitting the goal with no
          -- steps would claim it was discharged by nothing; say what happened.
          let txt := (← ppExpr ty).pretty
          unnamed := unnamed.push txt
          sides := sides.push
            (SideRec.mk ty #[] (some "unresolved:nested simp steps could not be \
              placed in the side goal") evCtx #[] ty none)
          continue
        match ← goalCloseForm? after with
        | some by_ => sides := sides.push (SideRec.mk ty evs (some by_) evCtx #[] ty
            (if evs.isEmpty then none else some after))
        | none =>
        match ← assumptionName? pa with
        | some by_ => sides := sides.push (SideRec.mk ty evs (some by_) evCtx #[] ty
            (if evs.isEmpty then none else some after))
        | none =>
          -- The condition's proof is a term no close form describes — a
          -- `noConfusion` elimination under a binder, say.  Naming it
          -- `true_intro` would tell a replayer to close a goal that is not
          -- `True`; record the classified form instead.
          let txt := (← ppExpr ty).pretty
          unnamed := unnamed.push txt
          sides := sides.push
            (SideRec.mk ty evs (some s!"unresolved:condition proof not a \
              hypothesis or a recorded discharge") evCtx #[] ty none)
    for u in unnamed do
      ref.modify (·.markUnresolved
        s!"simproc:{(src?.map toString).getD declName.toString} side condition \
`{u}` proved by a term no close form describes")
    -- Confirm `name` applied to `args` really elaborates to what simp used: a
    -- recorded argument list that does not reproduce simp's term would send a
    -- replayer to a different instance or a different lemma instantiation
    -- (REVIEW-6 2).  On failure the call is classified rather than silently
    -- emitting an unreplayable step.
    let ok ← checkArgsElaborate declName explicitArgs
    unless ok do
      ref.modify (·.markUnresolved
        s!"simproc:{(src?.map toString).getD declName.toString} lemma \
`{declName}` applied to its recorded arguments does not re-elaborate")
    ref.modify (·.push (.rw pos (.decl declName true false) inv none
      e r.expr evCtx explicitArgs sides src? (.decl declName true false) ""))
  | .computed =>
    ref.modify (·.push (.eq pos src? e r.expr evCtx side))
where
  /-- Name the close form a condition proof corresponds to, or `none` when no
  spec form describes it.  simp wraps a hypothesis `h : c` as `eq_true h` to
  get `c = True`, and a decidable ground condition as `eq_true_of_decide`. -/
  assumptionName? (pa : Expr) : Simp.SimpM (Option String) := do
    -- The wrapper is stripped to *find* the local, but it must be kept in what
    -- we report: `close.by` renders as `exact <term>`, and simp wraps `hp : P`
    -- as `eq_true hp` precisely because the side goal is `P = True`, which `hp`
    -- alone does not prove.  Reporting the bare name here produced
    -- `exact hp` against `P = True` -- a type mismatch at replay (REVIEW-9 1).
    let wrapper? : Option Name :=
      if pa.isAppOfArity ``eq_true 2 then some ``eq_true
      else if pa.isAppOfArity ``eq_false 2 then some ``eq_false
      else none
    let core := if wrapper?.isSome then pa.appArg! else pa
    match core with
    | .fvar fvarId =>
      -- The *display* name, never `eraseMacroScopes`: for an inaccessible `a✝`
      -- the erased form is plain `a`, which in the same context usually denotes
      -- a different, accessible local, so a generator emitting `exact a` picks
      -- the wrong one.  `name`, `intros` and `local` already use the display
      -- form; `close.by` must agree with them (REVIEW-6 5).
      let nm := (← ppExpr (mkFVar fvarId)).pretty
      match wrapper? with
      | some w => return some s!"assumption:{w} {nm}"
      | none => return some s!"assumption:{nm}"
    | _ =>
      if core.isAppOf ``eq_true_of_decide || core.isAppOf ``of_decide_eq_true then
        return some "decide"
      else if core.isAppOf ``rfl || core.isAppOf ``Eq.refl then
        return some "rfl"
      else if core.isConstOf ``True.intro || core.isAppOf ``trivial then
        return some "true_intro"
      else if ← isNofunProof core then
        -- Spec fd4419b: `nofun` closes `c₁ ... = c₂ ... → False` (distinct
        -- constructors) or any goal refutable by empty pattern matching.
        -- `reduceCtorEq` hands `eq_false'` exactly such a function.
        return some "nofun"
      else
        return none

  /-- Is `e` a proof refutable by empty pattern matching — a function into
  `False` (or any type) whose body eliminates an impossible hypothesis?

  We decide this from the *type*, not the term: the proof `reduceCtorEq` builds
  is a `noConfusion` elimination under a binder, whose exact shape is an
  implementation detail, whereas the statement "a hypothesis equating distinct
  constructors implies anything" is what `nofun` discharges and is stable. -/
  isNofunProof (e : Expr) : Simp.SimpM Bool := do
    let ty ← instantiateMVars (← inferType e)
    forallTelescopeReducing ty fun xs _ => do
      -- Exactly one hypothesis, and it equates two distinct constructors.
      unless xs.size == 1 do return false
      let hty ← whnfR (← inferType xs[0]!)
      let some (_, lhs, rhs) := hty.eq? | return false
      let some (c₁, _) ← constructorApp'? lhs | return false
      let some (c₂, _) ← constructorApp'? rhs | return false
      return c₁.name != c₂.name

/-! ### Method instrumentation -/

/-! ### Controlled conditional simprocs

The built-in `reduceIte` and `reduceDIte` closures call opaque `Simp.simp` on
their condition.  Keep their declarations and candidate registration intact,
but erase only those two entries from the invocation array and run equivalent
closures at the same pre-simproc boundary.  This preserves all other
candidate order and prevents a second registration/firing. -/

partial def peelConditional (e : Expr) (args : Array Expr := #[]) :
    Option (Expr × Array Expr) :=
  -- `Expr.isAppOf` also succeeds for an application of an `ite` result
  -- (e.g. `(if p then f else g) x`).  Keep peeling until the complete
  -- five-argument conditional core is exposed, exactly as the stock
  -- simproc's `numExtraArgs` peeling does.
  if (e.isAppOf ``ite || e.isAppOf ``dite) && e.getAppNumArgs == 5 then
    some (e, args.reverse)
  else
    match e with
    | .app f a => peelConditional f (args.push a)
    | _ => none

def controlledReduceIte (ref : TraceRef) : Simp.Simproc := fun e => do
  match peelConditional e with
  | none => return .continue
  | some (core, extraArgs) =>
    let_expr f@ite α c i tb eb ← core | return .continue
    let r ← simpT ref #[] c
    if r.expr.isTrue then
      let pr := mkApp (mkApp5 (mkConst ``ite_cond_eq_true f.constLevels!) α c i tb eb)
        (← r.getProof)
      Simp.recordSimpTheorem (.decl ``reduceIte false)
      ref.modify (·.markProcOrigin ``reduceIte)
      let step : Simp.Step := .visit { expr := tb, proof? := pr }
      return (← step.addExtraArgs extraArgs)
    if r.expr.isFalse then
      let pr := mkApp (mkApp5 (mkConst ``ite_cond_eq_false f.constLevels!) α c i tb eb)
        (← r.getProof)
      Simp.recordSimpTheorem (.decl ``reduceIte false)
      ref.modify (·.markProcOrigin ``reduceIte)
      let step : Simp.Step := .visit { expr := eb, proof? := pr }
      return (← step.addExtraArgs extraArgs)
    return .continue

def controlledReduceDIte (ref : TraceRef) : Simp.Simproc := fun e => do
  match peelConditional e with
  | none => return .continue
  | some (core, extraArgs) =>
    let_expr f@dite α c i tb eb ← core | return .continue
    let r ← simpT ref #[] c
    if r.expr.isTrue then
      let pr ← r.getProof
      let h := mkApp2 (mkConst ``of_eq_true) c pr
      let eNew := mkApp tb h |>.headBeta
      let prNew := mkApp (mkApp5 (mkConst ``dite_cond_eq_true f.constLevels!) α c i tb eb) pr
      Simp.recordSimpTheorem (.decl ``reduceDIte false)
      ref.modify (·.markProcOrigin ``reduceDIte)
      let step : Simp.Step := .visit { expr := eNew, proof? := prNew }
      return (← step.addExtraArgs extraArgs)
    if r.expr.isFalse then
      let pr ← r.getProof
      let h := mkApp2 (mkConst ``of_eq_false) c pr
      let eNew := mkApp eb h |>.headBeta
      let prNew := mkApp (mkApp5 (mkConst ``dite_cond_eq_false f.constLevels!) α c i tb eb) pr
      Simp.recordSimpTheorem (.decl ``reduceDIte false)
      ref.modify (·.markProcOrigin ``reduceDIte)
      let step : Simp.Step := .visit { expr := eNew, proof? := prNew }
      return (← step.addExtraArgs extraArgs)
    return .continue

def controlledConditionalSimprocs (ref : TraceRef) (allowIte allowDIte : Bool) : Simp.Simproc := fun e => do
  unless Simp.simprocs.get (← getOptions) do return .continue
  match peelConditional e with
  | none => return .continue
  | some (core, _) =>
    if allowIte && core.isAppOf ``ite then
      controlledReduceIte ref e
    else if allowDIte && core.isAppOf ``dite then
      controlledReduceDIte ref e
    else
      return .continue

def controlledDReduceIte (ref : TraceRef) : Simp.DSimproc := fun e => do
  unless (← Simp.inDSimp) do return .continue
  match peelConditional e with
  | none => return .continue
  | some (core, extraArgs) =>
    let_expr ite _ _ c i tb eb ← core | return .continue
    let r ← simpT ref #[] c
    if r.expr.isTrue || r.expr.isFalse then
      match_expr (← whnfD i) with
      | Decidable.isTrue _ _ =>
        Simp.recordSimpTheorem (.decl ``dreduceIte false)
        ref.modify (·.markProcOrigin ``dreduceIte)
        let step : Simp.DStep := .visit tb
        return step.addExtraArgs extraArgs
      | Decidable.isFalse _ _ =>
        Simp.recordSimpTheorem (.decl ``dreduceIte false)
        ref.modify (·.markProcOrigin ``dreduceIte)
        let step : Simp.DStep := .visit eb
        return step.addExtraArgs extraArgs
      | _ => return .continue
    return .continue

def controlledDReduceDIte (ref : TraceRef) : Simp.DSimproc := fun e => do
  unless (← Simp.inDSimp) do return .continue
  match peelConditional e with
  | none => return .continue
  | some (core, extraArgs) =>
    let_expr dite _ _ c i tb eb ← core | return .continue
    let r ← simpT ref #[] c
    if r.expr.isTrue || r.expr.isFalse then
      match_expr (← whnfD i) with
      | Decidable.isTrue _ h =>
        Simp.recordSimpTheorem (.decl ``dreduceDIte false)
        ref.modify (·.markProcOrigin ``dreduceDIte)
        let step : Simp.DStep := .visit (mkApp tb h).headBeta
        return step.addExtraArgs extraArgs
      | Decidable.isFalse _ h =>
        Simp.recordSimpTheorem (.decl ``dreduceDIte false)
        ref.modify (·.markProcOrigin ``dreduceDIte)
        let step : Simp.DStep := .visit (mkApp eb h).headBeta
        return step.addExtraArgs extraArgs
      | _ => return .continue
    return .continue

def controlledConditionalDSimprocs (ref : TraceRef) (allowIte allowDIte : Bool) : Simp.DSimproc := fun e => do
  unless Simp.simprocs.get (← getOptions) do return .continue
  match peelConditional e with
  | none => return .continue
  | some (core, _) =>
    if allowIte && core.isAppOf ``ite then
      controlledDReduceIte ref e
    else if allowDIte && core.isAppOf ``dite then
      controlledDReduceDIte ref e
    else
      return .continue

/-- Capture the position the traversal is currently at. -/
@[inline] def currentPos (ref : TraceRef) : Simp.SimpM Pos :=
  return (← ref.get).pos

/-- Instrument a `Simproc` so each firing is logged at the traversal's current
position.  `tag` is `"pre"` or `"post"`, which decides which theorem tree
`reattribute?` probes. -/
def instrument (ref : TraceRef) (tag : String) (p : Simp.Simproc) : Simp.Simproc :=
  fun e => do
    let usedBefore := (← get).usedTheorems
    -- A simproc may run its own `simp` on a subterm it chooses (`reduceIte` does
    -- this on an `ite`'s condition).  That call goes to *stock* `simpImpl`, so
    -- its firings carry no position of their own; divert them into a frame and
    -- attach them to the simproc's `eq` step as `side` evidence.
    -- Inside an active frame, the first `pre` we see is on the subterm the
    -- simproc handed to its nested `simp`: that is the side goal.
    ref.modify fun s =>
      if s.procEvents.size > 0 && s.procGoals.size > 0
         && (s.procGoals.getD (s.procGoals.size - 1) none).isNone then
        { s with procGoals := s.procGoals.set! (s.procGoals.size - 1) (some e) }
      else s
    ref.modify fun s =>
      { s with procEvents := s.procEvents.push #[],
               procGoals := s.procGoals.push none }
    let depth := (← ref.get).procEvents.size
    let stepResult ←
      try p e
      catch ex =>
        ref.modify fun s =>
          { s with procEvents := s.procEvents.take (depth - 1),
                   procGoals := s.procGoals.take (depth - 1) }
        throw ex
    -- Read the diverted frame and its goal, then pop both.
    let st ← ref.get
    let ok := depth > 0 && depth <= st.procEvents.size && depth <= st.procGoals.size
    let diverted := if ok then st.procEvents.getD (depth - 1) #[] else #[]
    let divertedGoal? := if ok then st.procGoals.getD (depth - 1) none else none
    ref.set { st with
                      procEvents := st.procEvents.take (depth - 1),
                      procGoals := st.procGoals.take (depth - 1) }
    let st ← ref.get
    let (st, controlledOrigin?) := st.takeProcOrigin
    ref.set st
    let usedAfter := (← get).usedTheorems
    let record (r : Simp.Result) : Simp.SimpM Unit := do
      unless r.expr == e do
        -- simp applies a partially-matching lemma to the arguments it did not
        -- match (`Simp.Result.addExtraArgs`): `h : Option.map f = Option.map g`
        -- rewrites the *function* of `Option.map f (some x)`.  The traversal is
        -- at the whole application, so recording its position says the step
        -- rewrites the application -- and a replayer then looks for
        -- `Option.map f` at a node that holds `Option.map f (some x)`.  Descend
        -- into the function for each trailing argument both sides share, which
        -- is exactly the prefix simp matched (REVIEW-9 4).
        let pos ← currentPos ref
        let evCtx ← captureEvCtx ref
        let side := (← ref.get).pendingSide
        ref.modify fun s => { s with pendingSide := #[] }
        -- Firings the simproc caused inside its own nested `simp` have no
        -- position of their own; they are kept and handed to `emitProcStep`,
        -- which attaches them to the side condition they belong to.  They are
        -- *not* wrapped in a `SideRec` here: doing so recorded the subterm the
        -- simproc chose to simplify as the side goal, with a hardcoded
        -- `true_intro` close, where the lemma's real side condition is an
        -- equation *about* that subterm (`c = False` for `ite_cond_eq_false`).
        -- There is one code path for side goals now — the lemma hypothesis's
        -- instantiated type, in `emitProcStep` — and this is not a second one
        -- (REVIEW-9 1).
        let rebased := diverted.map (Event.strip pos)
        let news := newOrigins usedBefore usedAfter
        -- `+contextual` registers the antecedent hypothesis alongside the
        -- lemma that fired, so a single firing can add more than one origin;
        -- the rewrite we are recording is the last one registered.
        let origin? : Option (Origin × Bool) :=
          match controlledOrigin? with
          | some n => some (.decl n false false, false)
          | none =>
            if news.isEmpty then none
            else match news[news.size - 1]! with
              | .decl n p inv => some (.decl n p inv, inv)
              | o => some (o, false)
        let origin? ← match origin? with
          | some oi => pure (some oi)
          | none => reattribute? e r.expr (tag == "post")
        match origin? with
        | some (o, inv) =>
          -- A simproc registers its declaration name in `usedTheorems` just as
          -- a lemma does; the spec wants those recorded as `eq`, not `rw`.
          let isProc ← match o with
            | .decl declName _ _ => Simp.isSimproc declName
            | _ => pure false
          if isProc then
            let src := match o with | .decl n _ _ => some n | _ => none
            -- A simproc rewrites the node it was handed, so it keeps the
            -- untrimmed pair: `emitProcStep` takes the whole `Simp.Result`,
            -- and pairing a trimmed `e` with it would describe two different
            -- terms.
            emitProcStep ref pos e r evCtx side src rebased divertedGoal?
              controlledOrigin?.isSome
          else
            -- `simp [h]` records the *syntax* as the origin.  Resolve it to
            -- the hypothesis for the `local` object and the `prop` flag, which
            -- the spec requires unconditionally (REVIEW-5 1), but keep the
            -- original origin for `name` and `dir`: the syntax is what carries
            -- a leading `←`, and replacing it would silently turn a reverse
            -- rewrite into a forward one.
            let sourceInfo? ← sourceArgInfo? ref o
            let (resolved, rargs, rinv, rproj) ←
              resolveStxOrigin o ((sourceInfo?.map (·.headLocal)).getD false)
            -- Every rewrite origin must be a global constant or a local fvar.
            -- A `.stx` that resolves to neither leaves the step without the
            -- identity the spec requires, and the structural check cannot see
            -- it either, so it is classified rather than silently shipped
            -- (REVIEW-7 1a) — "none" is never a pass.
            if resolved matches .stx .. then
              ref.modify (·.markUnresolved "origin")
            let prop? ← propFlag? resolved r.expr evCtx.lctx evCtx.insts
            -- Now that the origin is resolved, its own left-hand side says how
            -- many arguments the lemma matched; anything beyond that is what
            -- simp reapplied, and the rewritten node sits that many levels
            -- down the function spine (REVIEW-9 4).
            let arity ← lhsArity? resolved rinv prop?
            let (pos, e, rExpr) :=
              descendToRewritten (arity.getD e.getAppNumArgs) pos e r.expr
            -- A wrapper that reverses the statement (`h.symm`) flips `dir`.
            ref.modify (·.push
              (.rw pos o (inv != rinv) prop? e rExpr evCtx rargs side none
                resolved rproj))
        | none =>
          -- No origin at all: a simproc that registered nothing (`simpUsingDecide`
          -- and the ground arithmetic/matcher simprocs).  Same classification.
          let bounded? := inferBoundedIteSource? e r divertedGoal?
          emitProcStep ref pos e r evCtx side bounded? rebased divertedGoal?
    match stepResult with
    | .done r => record r
    | .visit r => record r
    | .continue (some r) => record r
    | .continue none => pure ()
    return stepResult

/-- Instrument a `DSimproc`.  The definitional layer's own reductions are logged
by the fork (`Traversal.logDStep`, `Traversal.reduceStepC`); this wrapper exists
only so a `dpre`/`dpost` firing that *is* attributable to a simproc is recorded
as an `eq` step rather than an anonymous `change`. -/
def instrumentD (ref : TraceRef) (p : Simp.DSimproc) : Simp.DSimproc := fun e => do
  let usedBefore := (← get).usedTheorems
  ref.modify fun s =>
    { s with procEvents := s.procEvents.push #[],
             procGoals := s.procGoals.push none }
  let depthD := (← ref.get).procEvents.size
  let stepResult ←
    try p e
    catch ex =>
      ref.modify fun s =>
        { s with procEvents := s.procEvents.take (depthD - 1),
                 procGoals := s.procGoals.take (depthD - 1) }
      throw ex
  ref.modify fun s =>
    { s with procEvents := s.procEvents.take (depthD - 1),
             procGoals := s.procGoals.take (depthD - 1) }
  let st ← ref.get
  let (st, controlledOrigin?) := st.takeProcOrigin
  ref.set st
  let usedAfter := (← get).usedTheorems
  let news := newOrigins usedBefore usedAfter
  unless news.isEmpty && controlledOrigin?.isNone do
    let changed? : Option Expr := match stepResult with
      | .done e' => if e' == e then none else some e'
      | .visit e' => if e' == e then none else some e'
      | .continue (some e') => if e' == e then none else some e'
      | .continue none => none
    if let some e' := changed? then
      let pos ← currentPos ref
      let evCtx ← captureEvCtx ref
      -- `instrumentD` wraps `dpre`/`dpost`, the **definitional** layer, so a
      -- firing here is definitional by construction.  The spec (e95c745) makes
      -- it a `change` carrying the dsimproc's name in `source`; recording it as
      -- a propositional `eq` or `rw` forces a replayer into a rewrite it cannot
      -- perform — T2 refused the `dreduce_ite` step outright, because its
      -- position is the domain of a dependent `∀` (REVIEW-6 4).
      let src := match controlledOrigin?, news[news.size - 1]? with
        | some n, _ => some n
        | none, some (.decl n _ _) => some n
        | _, _ => none
      ref.modify (·.push (.defeq pos .change src e e' evCtx))
  return stepResult

/-! ### Dischargers

Each discharger call is one side condition.  Steps performed by a nested simp
inside the discharger are captured into a side frame rooted at the side goal.

Close forms follow the amended spec.  A discharger we cannot describe is
recorded as `{"by": "unresolved:<text>"}` and the call is reported unresolved —
a **classified** outcome, per the task.  REVIEW-3 M3 was the previous behaviour:
a `throwError`, so `simp_trace (disch := omega)` failed on a goal stock
`simp (disch := omega)` proves.
-/

/-- Describe how a side condition closed, and reconcile that with the events the
recorder captured, so a replayer is never told to do the work twice.
`goal` is the side goal, needed to tell a genuine `rfl` close from an
`of_eq_true`-wrapped rewrite to `True`. -/
def describeProof (goal : Expr) (proof : Expr) (nested : Array Event)
    (dischargerText? : Option String) :
    Simp.SimpM (String × Array Event × Option String) := do
  match proof with
  | .fvar fvarId =>
    -- The display name, for the reason given at `assumptionName?` above.
    let display := (← ppExpr (mkFVar fvarId)).pretty
    -- The hypothesis alone proves it; recorded events did not contribute.
    return (s!"assumption:{display}", #[], none)
  | _ =>
    if nested.isEmpty then
      if proof.isAppOf ``of_eq_true then
        -- `of_eq_true p` means the goal was *rewritten to `True`* by the steps
        -- in `p`, not that it holds by `rfl`.  Those inner rewrites are
        -- diverted (they carry no position), so `nested` is empty and writing
        -- `rfl` asserts a close we never observed and that usually does not
        -- hold — `rfl` cannot prove an opaque `P k` (REVIEW-7 3).
        -- `rfl` is recorded only when the goal really is closed by reflexivity.
        if let some form ← goalCloseForm? goal then return (form, nested, none)
        return ("unresolved:discharged by rewriting to True, steps not \
recorded", nested,
          some "side condition rewritten to `True` by lemmas whose steps carry \
no position")
      else if proof.isAppOf ``eq_true_of_decide then return ("decide", nested, none)
      else if proof.isAppOf ``trivial || proof.isAppOf ``True.intro then
        return ("true_intro", nested, none)
      else match dischargerText? with
        | some txt =>
          -- A user-supplied discharger.  `omega` has its own close form in the
          -- amended spec; anything else is a classified unresolved outcome.
          if txt == "omega" then
            return ("omega", nested, none)
          else
            return (s!"unresolved:{txt}", nested,
              some s!"side condition discharged by `{txt}`")
        | none =>
          return ("unresolved:unrecognised discharge proof", nested,
            some "side condition discharged by a proof whose closing form is not \
              one of the spec's (rfl, true_intro, assumption:<name>, \
              absurd:<hyp>, decide, omega)")
    else
      -- The recorded steps reduced the side goal to `True`; closing it is then
      -- `True.intro`, and the steps are the actual discharge.
      return ("true_intro", nested, none)

/-- Instrument the discharger. -/
def instrumentDischarge (ref : TraceRef) (dischargerText? : Option String)
    (d : Simp.Discharge) : Simp.Discharge :=
  fun e => do
    -- A side goal is its own root: the spec says positions are child indices
    -- "from the root of the location", and a side trace is a nested trace with
    -- the same shape.  Without resetting, events logged while the discharger
    -- runs keep whatever position the *outer* traversal was at, which cannot
    -- exist in the side goal at all — T2 rejects them by name (REVIEW-8 3).
    -- Record the position the frame opens at, so events pushed into it are
    -- rebased to the side goal's own root.
    ref.modify fun s =>
      { s with sideStack := s.sideStack.push #[], sideBase := s.sideBase.push s.pos }
    let depth := (← ref.get).sideStack.size
    let result ←
      -- The discharger's own events are rooted at the side goal, not at the
      -- node whose condition it discharges.
      try withPreservedCacheT ref <| atSideRoot ref (d e)
      catch ex =>
        -- Never leave a dangling frame: a discharger that throws would
        -- otherwise send every later event into the abandoned frame.
        ref.modify fun s =>
          { s with sideStack := s.sideStack.take (depth - 1),
                   sideBase := s.sideBase.take (depth - 1) }
        throw ex
    -- Take the frame the discharger filled, then pop it.
    let st ← ref.get
    let nested :=
      if depth > 0 && depth <= st.sideStack.size then
        st.sideStack.getD (depth - 1) #[]
      else #[]
    ref.set { st with sideStack := st.sideStack.take (depth - 1),
                      sideBase := st.sideBase.take (depth - 1) }
    match result with
    | none => return none
    | some proof =>
      -- The side goal carries metavariables the lemma match assigns;
      -- instantiate so the recorded term is ground.
      let e ← instantiateMVars e
      let evCtx ← captureEvCtx ref
      -- Rebase the frame's events onto the side goal's own root.  Pushing
      -- through `procEvents` (a simproc's nested `simp`) bypasses the rebase in
      -- `TraceState.push`, so it is applied here, where every event that
      -- belongs to this side condition has been collected.
      let base := (← ref.get).pos
      let nested := nested.map (Event.strip base)
      let (by_, kept, unresolved?) ← describeProof e proof nested dischargerText?
      if let some reason := unresolved? then
        ref.modify (·.markUnresolved reason)
      let rec_ : SideRec := .mk e kept (some by_) evCtx #[] e none
      ref.modify fun s => { s with pendingSide := s.pendingSide.push rec_ }
      return some proof

/-! ### Entry point

`runTraced` is the fork's replacement for `Meta.simp`: it builds instrumented
`Methods` around the stock defaults, then runs the **forked** traversal
(`simpT`) instead of the opaque `Simp.simp`.  Everything the `Methods` do is
stock; the traversal is the fork.
-/

/-- The default discharger copied at the fork boundary.  Its only traversal
edit is replacing the opaque nested `Simp.simp` with `simpT`; all proof
construction and the result tests are stock. -/
partial def isEqnThmHypothesisT (e : Expr) : Bool :=
  e.isForall && go e
where
  go (e : Expr) : Bool :=
    match e with
    | .forallE _ d b _ => (d.isEq || d.isHEq || b.hasLooseBVar 0) && go b
    | _ => e.isFalse

def dischargeUsingAssumptionT (e : Expr) : SimpM (Option Expr) := do
  let lctxInitIndices := (← readThe Simp.Context).lctxInitIndices
  let contextual := (← Simp.getConfig).contextual
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if !contextual && localDecl.index >= lctxInitIndices then
      return none
    else if (← Simp.withSimpMetaConfig <| isDefEq e localDecl.type) then
      return some localDecl.toExpr
    else
      return none

partial def dischargeEqnThmHypothesisT (e : Expr) : MetaM (Option Expr) := do
  assert! isEqnThmHypothesisT e
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
    catch _ =>
      return some mvarId

def dischargeRflT (e : Expr) : SimpM (Option Expr) := do
  forallTelescope e fun xs e => do
    let some (t, a, b) := e.eq? | return .none
    unless a.getAppFn.isMVar || b.getAppFn.isMVar do return .none
    if (← Simp.withSimpMetaConfig <| isDefEq a b) then
      let u ← getLevel t
      let proof := mkApp2 (.const ``rfl [u]) t a
      let proof ← mkLambdaFVars xs proof
      return .some proof
    return .none

def dischargeDefaultT (ref : TraceRef) (e : Expr) : Simp.SimpM (Option Expr) := do
  let e := e.cleanupAnnotations
  if isEqnThmHypothesisT e then
    if let some r ← dischargeUsingAssumptionT e then return some r
    if let some r ← dischargeEqnThmHypothesisT e then return some r
  let r ← simpT ref #[] e
  if let some p ← dischargeRflT r.expr then
    return some (mkApp4 (mkConst ``Eq.mpr [Level.zero]) e r.expr (← r.getProof) p)
  else if r.expr.isTrue then
    return some (← mkOfEqTrue (← r.getProof))
  else
    return none

/-- Build instrumented `Methods` around the stock defaults. -/
def mkRecordingMethods (ref : TraceRef) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) (dischargerText? : Option String) :
    Simp.Methods :=
  let d : Simp.Discharge := discharge?.getD (dischargeDefaultT ref)
  -- Mirror stock simp exactly: `simpCore` uses `mkDefaultMethodsCore`
  -- (`wellBehavedDischarge := true`) when no custom discharger is given, and
  -- `false` only for a user discharger.  Hardcoding `false` would force
  -- `withFreshCache` on every implication descent, changing which subterms simp
  -- revisits and so the trace itself.
  let allowIte := simprocs.any fun s => s.simprocNames.contains ``reduceIte
  let allowDIte := simprocs.any fun s => s.simprocNames.contains ``reduceDIte
  let allowDReduceIte := simprocs.any fun s => s.simprocNames.contains ``dreduceIte
  let allowDReduceDIte := simprocs.any fun s => s.simprocNames.contains ``dreduceDIte
  let conditionalFree := simprocs.erase ``reduceIte |>.erase ``reduceDIte
    |>.erase ``dreduceIte |>.erase ``dreduceDIte
  let base := Simp.mkMethods conditionalFree
    (instrumentDischarge ref dischargerText? d)
    (wellBehavedDischarge := discharge?.isNone)
  let userPre := instrument ref "pre"
    (Simp.simpMatch >> controlledConditionalSimprocs ref allowIte allowDIte >>
      Simp.userPreSimprocs conditionalFree >> Simp.simpUsingDecide)
  let userPost := instrument ref "post"
    (Simp.userPostSimprocs conditionalFree >> Simp.simpGround >> Simp.simpArith
      >> Simp.simpUsingDecide)
  { base with
    -- The theorem phase is the fork-side operational matcher.  The remaining
    -- stock procedures retain the existing instrumented path, so generic
    -- simprocs remain classified/unresolved exactly as before.
    pre := rewritePreOperational ref >> userPre
    post := rewritePostOperational ref >> userPost
    dpre := instrumentD ref
      (controlledConditionalDSimprocs ref allowDReduceIte allowDReduceDIte >> base.dpre)
    dpost := instrumentD ref
      (controlledConditionalDSimprocs ref allowDReduceIte allowDReduceDIte >> base.dpost) }

/-- Run the forked traversal on `e`, returning simp's result, the updated stats
and the events logged at their exact positions. -/
def runTraced (e : Expr) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) (dischargerText? : Option String)
    (stats : Simp.Stats) (sourceArgs : Array SourceArg := #[]) :
    MetaM (Simp.Result × Simp.Stats × Array Event × Array String) := do
  let ref : TraceRef ← ST.mkRef ({ sourceArgs } : TraceState)
  let methods := mkRecordingMethods ref simprocs discharge? dischargerText?
  let (r, s) ← Simp.SimpM.run ctx { stats with } methods <|
    Simp.withCatchingRuntimeEx <| simpT ref #[] e
  let st ← ref.get
  return (r, { s with }, st.events, st.unresolved)

end ExplicitLean.SimpTrace
