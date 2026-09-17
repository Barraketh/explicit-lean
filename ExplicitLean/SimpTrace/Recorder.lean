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

/-! ### Method instrumentation -/

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
      if s.procEvents.size > 0 && s.procGoals.back!.isNone then
        { s with procGoals := s.procGoals.set! (s.procGoals.size - 1) (some e) }
      else s
    ref.modify fun s =>
      { s with procDepth := s.procDepth + 1,
               procEvents := s.procEvents.push #[],
               procGoals := s.procGoals.push none }
    let depth := (← ref.get).procEvents.size
    let stepResult ←
      try p e
      catch ex =>
        ref.modify fun s =>
          { s with procDepth := s.procDepth - 1,
                   procEvents := s.procEvents.take (depth - 1),
                   procGoals := s.procGoals.take (depth - 1) }
        throw ex
    -- Read the diverted frame and its goal, then pop both.
    let st ← ref.get
    let diverted := if st.procEvents.size >= depth then st.procEvents[depth - 1]! else #[]
    let divertedGoal? := if st.procGoals.size >= depth then st.procGoals[depth - 1]! else none
    ref.set { st with procDepth := st.procDepth - 1,
                      procEvents := st.procEvents.take (depth - 1),
                      procGoals := st.procGoals.take (depth - 1) }
    let usedAfter := (← get).usedTheorems
    let record (r : Simp.Result) : Simp.SimpM Unit := do
      unless r.expr == e do
        let pos ← currentPos ref
        let evCtx ← captureEvCtx ref
        let side := (← ref.get).pendingSide
        ref.modify fun s => { s with pendingSide := #[] }
        -- Firings the simproc caused inside its own nested `simp`: they have no
        -- position of their own, so they become this step's `side` evidence.
        -- The side goal is the subterm the simproc chose to simplify — the first
        -- diverted firing's `before`, which is that subterm before any rewrite —
        -- not the whole term the simproc fired on.  `reduceIte` picks an `ite`'s
        -- condition; naming the `ite` there would misdescribe the side goal.
        let divertedSide : Array SideRec :=
          if diverted.isEmpty then #[]
          else #[SideRec.mk (divertedGoal?.getD e) diverted (some "true_intro") evCtx]
        let news := newOrigins usedBefore usedAfter
        -- `+contextual` registers the antecedent hypothesis alongside the
        -- lemma that fired, so a single firing can add more than one origin;
        -- the rewrite we are recording is the last one registered.
        let origin? : Option (Origin × Bool) :=
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
            ref.modify (·.push (.eq pos src e r.expr evCtx (side ++ divertedSide)))
          else
            let prop? ← propFlag? o r.expr evCtx.lctx evCtx.insts
            ref.modify (·.push (.rw pos o inv prop? e r.expr evCtx #[] side))
        | none =>
          -- No origin at all: a simproc that registered nothing (`simpUsingDecide`
          -- and the ground arithmetic/matcher simprocs).  This is the spec's
          -- `eq` kind, whose `by` a scratch check decides — never an abort.
          ref.modify (·.push (.eq pos none e r.expr evCtx (side ++ divertedSide)))
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
    { s with procDepth := s.procDepth + 1,
             procEvents := s.procEvents.push #[],
             procGoals := s.procGoals.push none }
  let depthD := (← ref.get).procEvents.size
  let stepResult ←
    try p e
    catch ex =>
      ref.modify fun s =>
        { s with procDepth := s.procDepth - 1,
                 procEvents := s.procEvents.take (depthD - 1),
                 procGoals := s.procGoals.take (depthD - 1) }
      throw ex
  ref.modify fun s =>
    { s with procDepth := s.procDepth - 1,
             procEvents := s.procEvents.take (depthD - 1),
             procGoals := s.procGoals.take (depthD - 1) }
  let usedAfter := (← get).usedTheorems
  let news := newOrigins usedBefore usedAfter
  unless news.isEmpty do
    let changed? : Option Expr := match stepResult with
      | .done e' => if e' == e then none else some e'
      | .visit e' => if e' == e then none else some e'
      | .continue (some e') => if e' == e then none else some e'
      | .continue none => none
    if let some e' := changed? then
      let pos ← currentPos ref
      let evCtx ← captureEvCtx ref
      match news[news.size - 1]! with
      | .decl n _ _ =>
        if ← Simp.isSimproc n then
          ref.modify (·.push (.eq pos (some n) e e' evCtx #[]))
        else
          ref.modify (·.push (.rw pos (.decl n true false) false none e e' evCtx #[] #[]))
      | o => ref.modify (·.push (.rw pos o false none e e' evCtx #[] #[]))
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
recorder captured, so a replayer is never told to do the work twice. -/
def describeProof (proof : Expr) (nested : Array Event)
    (dischargerText? : Option String) :
    Simp.SimpM (String × Array Event × Option String) := do
  match proof with
  | .fvar fvarId =>
    let n := (← fvarId.getDecl).userName
    -- The hypothesis alone proves it; recorded events did not contribute.
    return (s!"assumption:{n.eraseMacroScopes}", #[], none)
  | _ =>
    if nested.isEmpty then
      if proof.isAppOf ``of_eq_true then return ("rfl", nested, none)
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
    ref.modify fun s => { s with sideStack := s.sideStack.push #[] }
    let depth := (← ref.get).sideStack.size
    let result ←
      try d e
      catch ex =>
        -- Never leave a dangling frame: a discharger that throws would
        -- otherwise send every later event into the abandoned frame.
        ref.modify fun s =>
          { s with sideStack := s.sideStack.take (depth - 1) }
        throw ex
    -- Take the frame the discharger filled, then pop it.
    let st ← ref.get
    let nested := if st.sideStack.size >= depth then st.sideStack[depth - 1]! else #[]
    ref.set { st with sideStack := st.sideStack.take (depth - 1) }
    match result with
    | none => return none
    | some proof =>
      -- The side goal carries metavariables the lemma match assigns;
      -- instantiate so the recorded term is ground.
      let e ← instantiateMVars e
      let evCtx ← captureEvCtx ref
      let (by_, kept, unresolved?) ← describeProof proof nested dischargerText?
      if let some reason := unresolved? then
        ref.modify (·.markUnresolved reason)
      let rec_ : SideRec := .mk e kept (some by_) evCtx
      ref.modify fun s => { s with pendingSide := s.pendingSide.push rec_ }
      return some proof

/-! ### Entry point

`runTraced` is the fork's replacement for `Meta.simp`: it builds instrumented
`Methods` around the stock defaults, then runs the **forked** traversal
(`simpT`) instead of the opaque `Simp.simp`.  Everything the `Methods` do is
stock; the traversal is the fork.
-/

/-- Build instrumented `Methods` around the stock defaults. -/
def mkRecordingMethods (ref : TraceRef) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) (dischargerText? : Option String) :
    Simp.Methods :=
  let d : Simp.Discharge := discharge?.getD Simp.dischargeDefault?
  -- Mirror stock simp exactly: `simpCore` uses `mkDefaultMethodsCore`
  -- (`wellBehavedDischarge := true`) when no custom discharger is given, and
  -- `false` only for a user discharger.  Hardcoding `false` would force
  -- `withFreshCache` on every implication descent, changing which subterms simp
  -- revisits and so the trace itself.
  let base := Simp.mkMethods simprocs
    (instrumentDischarge ref dischargerText? d)
    (wellBehavedDischarge := discharge?.isNone)
  { base with
    pre := instrument ref "pre" base.pre
    post := instrument ref "post" base.post
    dpre := instrumentD ref base.dpre
    dpost := instrumentD ref base.dpost }

/-- Run the forked traversal on `e`, returning simp's result, the updated stats
and the events logged at their exact positions. -/
def runTraced (e : Expr) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) (dischargerText? : Option String)
    (stats : Simp.Stats) :
    MetaM (Simp.Result × Simp.Stats × Array Event × Array String) := do
  let ref : TraceRef ← ST.mkRef ({} : TraceState)
  let methods := mkRecordingMethods ref simprocs discharge? dischargerText?
  let (r, s) ← Simp.SimpM.run ctx { stats with } methods <|
    Simp.withCatchingRuntimeEx <| simpT ref #[] e
  let st ← ref.get
  return (r, { s with }, st.events, st.unresolved)

end ExplicitLean.SimpTrace
