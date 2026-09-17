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

/--
Resolve an `Origin.stx` to the local hypothesis it elaborated to, when it is one.

When the user writes `simp [h]` for a local `h`, simp records the origin as the
*syntax* the user wrote, not `Origin.fvar`; via `simp [*]` the same rewrite
records an `Origin.fvar`. The spec is unconditional — a rewrite by a local
hypothesis carries the `local` object and, when the lemma is Prop-valued, the
`prop` flag — so the two forms must not disagree (REVIEW-5 1). `simp [h]` is the
dominant shape in Mathlib.

The simp theorem carrying this origin has the hypothesis as its `proof` (or as
the head of an application of it), so this is a lookup rather than a search.
-/
def resolveStxOrigin (o : Origin) (lctx : LocalContext) : Simp.SimpM Origin := do
  let .stx _ ref := o | return o
  -- The syntax the user wrote is an identifier when the argument is a
  -- hypothesis (`simp [h]`, `simp [← h]`); strip a leading arrow and look the
  -- name up in the local context that was live at the firing.  This is a
  -- lookup, not a search: scanning the theorem trees would be a 20 000-entry
  -- walk per step, and matching `Origin` structurally does not work anyway
  -- because the stored `Syntax` differs from the trace's copy.
  let txt := ref.prettyPrint.pretty.trimAscii.toString
  let txt := if txt.startsWith "←" then (txt.drop 1).trimAscii.toString
    else if txt.startsWith "<-" then (txt.drop 2).trimAscii.toString
    else txt
  -- An argument that is not a bare identifier (`simp [foo a b]`, a term) names
  -- no single hypothesis, so it is left as it is.
  unless txt.all (fun c => c.isAlphanum || c == '_' || c == '\'' || c == '!'
      || c == '?' || c == '\u2080' || c == '\u2081' || c == '\u2082') do
    return o
  match lctx.findFromUserName? (Name.mkSimple txt) with
  | some decl => return .fvar decl.fvarId
  | none => return o

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
  that are proofs, i.e. the conditions the discharger established. -/
  | lemmaApp (name : Name) (proofArgs : Array Expr)
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
  n == ``Eq.trans || n == ``Eq.mpr || n == ``Eq.mp || n == ``Eq.symm
  || n == ``id || n == ``of_eq_true || n == ``eq_true || n == ``eq_false
  || n == ``eq_self || n == ``propext || n == ``Iff.intro || n == ``Iff.mp
  || n == ``Iff.mpr || n == ``iff_of_eq || n == ``Eq.subst || n == ``Eq.ndrec

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
  if isPlumbingHead declName then
    return .computed
  let some ci := (← getEnv).find? declName | return .computed
  let args := proof.getAppArgs
  -- Walk the lemma's own telescope so we know which arguments are explicit.
  let shape? ← forallTelescopeReducing ci.type fun xs _ => do
    if xs.size < args.size then return none
    let mut proofArgs : Array Expr := #[]
    for i in [0:args.size] do
      let arg := args[i]!
      let some decl ← xs[i]!.fvarId!.findDecl? | return none
      match decl.binderInfo with
      | .implicit | .strictImplicit | .instImplicit => continue
      | .default =>
        if ← isProof arg then
          proofArgs := proofArgs.push arg
        else if isSubtermOf arg target then
          continue
        else if (← Meta.isClass? (← inferType arg)).isSome then
          continue
        else
          -- An explicit argument that is neither a subterm of the position, an
          -- instance, nor a proof: the lemma is not being applied *to this
          -- position*, so replay could not reconstruct the argument.
          return none
    return some proofArgs
  match shape? with
  | some proofArgs => return .lemmaApp declName proofArgs
  | none => return .computed

/--
Emit the step for a procedure firing, per the amended spec's `eq` bullet: a
proof that is one lemma applied is an ordinary `rw` naming that lemma, with the
discharged conditions as `side` entries and `source` naming the simproc;
anything else stays an `eq`, whose `by` the scratch check decides (and which
becomes a classified `unresolved:simproc:<name>` when it cannot).
-/
def emitProcStep (ref : TraceRef) (pos : Pos) (e : Expr) (r : Simp.Result)
    (evCtx : EvCtx) (side : Array SideRec) (src? : Option Name) :
    Simp.SimpM Unit := do
  let shape ← match r.proof? with
    | some proof => classifyProof e (← instantiateMVars proof)
    | none => pure .computed
  match shape with
  | .lemmaApp declName proofArgs =>
    -- Each proof argument is a condition the simproc established.  We already
    -- captured the discharger's own work as `side`; when we captured none, the
    -- condition came from somewhere else and we must name it honestly.
    let mut sides := side
    let mut unnamed : Array String := #[]
    if sides.isEmpty then
      for pa in proofArgs do
        let ty ← instantiateMVars (← inferType pa)
        match ← assumptionName? pa with
        | some by_ => sides := sides.push (SideRec.mk ty #[] (some by_) evCtx #[])
        | none =>
          -- The condition's proof is a term no close form describes — a
          -- `noConfusion` elimination under a binder, say.  Naming it
          -- `true_intro` would tell a replayer to close a goal that is not
          -- `True`; record the classified form instead.
          let txt := (← ppExpr ty).pretty
          unnamed := unnamed.push txt
          sides := sides.push
            (SideRec.mk ty #[] (some s!"unresolved:condition proof not a \
              hypothesis or a recorded discharge") evCtx #[])
    for u in unnamed do
      ref.modify (·.markUnresolved
        s!"simproc:{(src?.map toString).getD declName.toString} side condition \
`{u}` proved by a term no close form describes")
    ref.modify (·.push (.rw pos (.decl declName true false) false none
      e r.expr evCtx #[] sides src? (.decl declName true false)))
  | .computed =>
    ref.modify (·.push (.eq pos src? e r.expr evCtx side))
where
  /-- Name the close form a condition proof corresponds to, or `none` when no
  spec form describes it.  simp wraps a hypothesis `h : c` as `eq_true h` to
  get `c = True`, and a decidable ground condition as `eq_true_of_decide`. -/
  assumptionName? (pa : Expr) : Simp.SimpM (Option String) := do
    let core := if pa.isAppOfArity ``eq_true 2 || pa.isAppOfArity ``eq_false 2
      then pa.appArg! else pa
    match core with
    | .fvar fvarId =>
      let n := (← fvarId.getDecl).userName
      return some s!"assumption:{n.eraseMacroScopes}"
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
          else #[SideRec.mk (divertedGoal?.getD e) diverted (some "true_intro") evCtx #[]]
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
            emitProcStep ref pos e r evCtx (side ++ divertedSide) src
          else
            -- `simp [h]` records the *syntax* as the origin.  Resolve it to
            -- the hypothesis for the `local` object and the `prop` flag, which
            -- the spec requires unconditionally (REVIEW-5 1), but keep the
            -- original origin for `name` and `dir`: the syntax is what carries
            -- a leading `←`, and replacing it would silently turn a reverse
            -- rewrite into a forward one.
            let resolved ← resolveStxOrigin o evCtx.lctx
            let prop? ← propFlag? resolved r.expr evCtx.lctx evCtx.insts
            ref.modify (·.push
              (.rw pos o inv prop? e r.expr evCtx #[] side none resolved))
        | none =>
          -- No origin at all: a simproc that registered nothing (`simpUsingDecide`
          -- and the ground arithmetic/matcher simprocs).  Same classification.
          emitProcStep ref pos e r evCtx (side ++ divertedSide) none
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
          ref.modify (·.push
            (.rw pos (.decl n true false) false none e e' evCtx #[] #[] none
              (.decl n true false)))
      | o => ref.modify (·.push (.rw pos o false none e e' evCtx #[] #[] none o))
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
    let nested :=
      if depth > 0 && depth <= st.sideStack.size then
        st.sideStack.getD (depth - 1) #[]
      else #[]
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
      let rec_ : SideRec := .mk e kept (some by_) evCtx #[]
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
