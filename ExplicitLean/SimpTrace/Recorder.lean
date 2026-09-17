/-
Step recorder: wraps stock `Simp.Methods` so every firing of a `pre`/`post`
procedure is logged as a raw `(before, after, provenance)` triple, together with
the side-condition sub-runs the discharger performed.

Recorder machinery only.  Positions are *not* computed here; see
`ExplicitLean/SimpTrace/Position.lean`.
-/

module

public meta import Lean
public meta import ExplicitLean.SimpTrace.Types

public meta section

namespace ExplicitLean.SimpTrace

open Lean Meta Elab

/-- Where a recorded firing came from. -/
inductive Provenance where
  /-- A simp theorem or local hypothesis fired. `inv` is `←`. -/
  | thm (origin : Origin) (inv : Bool)
  /-- A simproc or other non-lemma procedure produced the result. `name?` is the
  procedure we could attribute it to, when we could. -/
  | proc (name? : Option Name)
  /-- A firing we could not attribute to any origin: the recorder saw a change
  but `usedTheorems` did not grow because the same lemma had already been
  recorded earlier in the run. -/
  | unattributed
  /-- Definitional machinery (`dsimp` layer: beta/eta/unfold/proj). -/
  | defeq
  deriving Inhabited

mutual

/-- One firing as observed inside the simp run. -/
structure RawStep where
  provenance : Provenance
  before     : Expr
  after      : Expr
  /-- Local context at the firing, so binder-bound names pretty-print. -/
  lctx       : LocalContext
  localInsts : LocalInstances
  /-- Free variables in `lctx`, in declaration order, tagged with whether they
  are proofs.  Proof locals are the hypotheses `+contextual` introduces for the
  antecedent of an implication; they are not term binders of the running term,
  so position solving must not count them as binder crossings. -/
  fvarKinds  : Array (FVarId × Bool) := #[]
  /-- Proof locals simp introduced beyond the location's own context: the
  antecedent hypotheses `+contextual` assumes.  Filled in by position solving,
  which knows the base context. -/
  contextualFVars : Array FVarId := #[]
  /-- Side-condition sub-runs performed while this step's lemma was matched. -/
  side       : Array RawSide := #[]

/-- One discharged side condition. -/
structure RawSide where
  goal  : Expr
  /-- Nested steps, when the discharger ran a nested simp. -/
  steps : Array RawStep := #[]
  /-- How it closed: `assumption:<n>`, `rfl`, `decide`, `trivial`, `eq_self`. -/
  by_   : Option String := none

end

instance : Inhabited RawStep :=
  ⟨{ provenance := .defeq, before := default, after := default,
     lctx := {}, localInsts := {} }⟩
instance : Inhabited RawSide := ⟨{ goal := default }⟩

/-- Mutable recorder state threaded through the simp run via `IO.Ref`. -/
structure RecorderState where
  steps : Array RawStep := #[]
  /-- Steps recorded while inside a discharger, i.e. belonging to a side goal.
  The stack has one frame per nesting level. -/
  sideStack : Array (Array RawStep) := #[]
  /-- Side conditions collected for the firing currently being assembled. -/
  pendingSide : Array RawSide := #[]
  /-- Set when a step kind we cannot classify is seen; the tactic fails on it. -/
  unsupported : Array String := #[]
  deriving Inhabited

abbrev RecorderRef := IO.Ref RecorderState

/-- Push a step into the innermost active frame. -/
def RecorderState.push (s : RecorderState) (step : RawStep) : RecorderState :=
  if s.sideStack.size > 0 then
    let i := s.sideStack.size - 1
    let frame := s.sideStack[i]!
    { s with sideStack := s.sideStack.set! i (frame.push step) }
  else
    { s with steps := s.steps.push step }

/-- Record an unsupported observation; the tactic turns these into a hard error
so that a step is never silently dropped. -/
def RecorderState.note (s : RecorderState) (msg : String) : RecorderState :=
  { s with unsupported := s.unsupported.push msg }

/-- Capture the current local context so a recorded subterm can be
pretty-printed later with its binders in scope. -/
private def captureCtx : MetaM (LocalContext × LocalInstances × Array (FVarId × Bool)) := do
  let lctx ← getLCtx
  let mut kinds : Array (FVarId × Bool) := #[]
  for decl in lctx do
    -- Include implementation-detail declarations: simp marks some of the
    -- locals it introduces for binder descent that way, and omitting them
    -- leaves their free variables unabstractable in recorded subterms.
    kinds := kinds.push (decl.fvarId, ← isProof decl.toExpr)
  return (lctx, (← getLocalInstances), kinds)

/-- Attribute a `Simp.Result` produced by a procedure whose name we do not know
directly.  `usedTheorems` grows by exactly the theorems the procedure used, so a
single new entry identifies a lemma firing; otherwise we call it a simproc. -/
private def classify (before after : Expr) (usedBefore usedAfter : Simp.UsedSimps)
    : Provenance :=
  -- A lemma firing registers its origin in `usedTheorems`.
  let newOnes := usedAfter.toArray.filter fun o => !usedBefore.contains o
  -- `+contextual` registers the antecedent hypothesis alongside the lemma that
  -- actually fired, so a single firing can add more than one origin.  The
  -- rewrite we are recording is the last origin registered.
  if newOnes.isEmpty then
    if before == after then .defeq
    -- `simpUsingDecide` (`+decide` / `Simp.Config.decide`) closes a proposition
    -- by decidability without registering any theorem, so the firing looks
    -- unattributed.  It is a computed equation: route it to `mkEqStep`, whose
    -- scratch check confirms `decide` actually proves it.
    else .unattributed
  else
    match newOnes[newOnes.size - 1]! with
    | .decl n p inv => .thm (.decl n p inv) inv
    | o => .thm o false

/--
Identify which simp theorem rewrote `before` to `after`, by probing the
candidate theorems individually with stock `Simp.tryTheorem?`.  We use this only
when `usedTheorems` did not grow (the lemma had already fired earlier in the
run), so no attribution is lost to simp's caching.

Probing one theorem at a time is what lets us name the exact origin:
`Simp.rewrite?` reports only the resulting expression.
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

/-- Instrument a `Simproc` so each firing is recorded. -/
def instrument (ref : RecorderRef) (tag : String) (p : Simp.Simproc) : Simp.Simproc :=
  fun e => do
    let usedBefore := (← get).usedTheorems
    let stepResult ← p e
    let usedAfter := (← get).usedTheorems
    let record (r : Simp.Result) : Simp.SimpM Unit := do
      -- Only a genuine change is a step.  `Simp.Step.continue none` and
      -- results equal to the input carry no rewriting.
      unless r.expr == e do
        let (lctx, localInsts, fvarKinds) ← captureCtx
        let mut prov := classify e r.expr usedBefore usedAfter
        if let .unattributed := prov then
          if let some (o, inv) ← reattribute? e r.expr (tag == "post") then
            prov := .thm o inv
          else if r.expr.isTrue || r.expr.isFalse then
            -- `simpUsingDecide` (`+decide` / `Simp.Config.decide`) closes a
            -- proposition by decidability without registering a theorem, so no
            -- origin exists.  It is a computed equation: route it to
            -- `mkEqStep`, whose scratch check confirms `decide` proves it.
            prov := .proc none
        let side := (← ref.get).pendingSide
        ref.modify fun (s : RecorderState) =>
          RecorderState.push { s with pendingSide := #[] }
            { provenance := prov, before := e, after := r.expr,
              lctx, localInsts, fvarKinds, side }
    match stepResult with
    | .done r => record r
    | .visit r => record r
    | .continue (some r) => record r
    | .continue none => pure ()
    -- `tag` distinguishes pre from post for debugging only.
    let _ := tag
    return stepResult

/-- Instrument a `DSimproc` (definitional layer). -/
def instrumentD (ref : RecorderRef) (p : Simp.DSimproc) : Simp.DSimproc :=
  fun e => do
    let stepResult ← p e
    let record (e' : Expr) : Simp.SimpM Unit := do
      unless e' == e do
        let (lctx, localInsts, fvarKinds) ← captureCtx
        ref.modify fun (s : RecorderState) =>
          RecorderState.push s
            { provenance := .defeq, before := e, after := e',
              lctx, localInsts, fvarKinds }
    match stepResult with
    | .done e' => record e'
    | .visit e' => record e'
    | .continue (some e') => record e'
    | .continue none => pure ()
    return stepResult

/--
Describe how a side condition closed, and reconcile that with the steps the
recorder captured, so a replayer is never told to do the work twice.

If the proof is a bare hypothesis, the discharge is that `assumption` and any
recorded steps are dead (simp explored, then used the hypothesis): drop them.
If steps did reduce the goal, they are the discharge and `close` is the closing
form they end in.
-/
private def describeProof (proof : Expr) (nested : Array RawStep) :
    Simp.SimpM (Option String × Array RawStep) := do
  match proof with
  | .fvar fvarId =>
    let n := (← fvarId.getDecl).userName
    -- The hypothesis alone proves it; recorded steps did not contribute.
    return (some s!"assumption:{n.eraseMacroScopes}", #[])
  | _ =>
    if nested.isEmpty then
      -- No recorded rewriting: the discharger closed it definitionally or by a
      -- decision procedure.  Distinguish the common shapes.
      if proof.isAppOf ``of_eq_true then return (some "rfl", nested)
      else if proof.isAppOf ``eq_true_of_decide then return (some "decide", nested)
      else if proof.isAppOf ``trivial || proof.isAppOf ``True.intro then
        return (some "true_intro", nested)
      else
        -- Same policy as the main trace: a close we cannot name is an error,
        -- never a value the spec does not define and replay cannot execute.
        throwError "simp_trace: side condition discharged by a proof whose \
          closing form is not one of the spec's (rfl, true_intro, \
          assumption:<name>, absurd:<hyp>, decide)\n  proof: {proof}"
    else
      -- The recorded steps reduced the side goal to `True`; closing it is then
      -- `True.intro`, and the steps are the actual discharge.
      return (some "true_intro", nested)

/-- Instrument the discharger: each call is one side condition.  Steps performed
by a nested simp inside the discharger are captured into the side frame. -/
def instrumentDischarge (ref : RecorderRef) (d : Simp.Discharge) : Simp.Discharge :=
  fun e => do
    ref.modify fun s => { s with sideStack := s.sideStack.push #[] }
    let result ← d e
    let st ← ref.get
    let nested := st.sideStack.back!
    ref.set { st with sideStack := st.sideStack.pop }
    match result with
    | none => return none
    | some proof =>
      -- The side goal and its steps carry metavariables that the lemma match
      -- assigns; instantiate them so recorded terms are ground.
      let e ← instantiateMVars e
      let nested ← nested.mapM fun st => do
        return { st with
          before := ← instantiateMVars st.before
          after := ← instantiateMVars st.after }
      let (by_, keptSteps) ← describeProof proof nested
      let sideRec : RawSide := { goal := e, steps := keptSteps, by_ }
      ref.modify fun (s : RecorderState) =>
        { s with pendingSide := s.pendingSide.push sideRec }
      return some proof

/-- Build instrumented `Methods` around the stock defaults. -/
def mkRecordingMethods (ref : RecorderRef) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) : Simp.Methods :=
  let d : Simp.Discharge := discharge?.getD Simp.dischargeDefault?
  -- Mirror stock simp exactly: `simpCore` uses `mkDefaultMethodsCore`
  -- (`wellBehavedDischarge := true`) when no custom discharger is given, and
  -- `false` only for a user discharger.  Hardcoding `false` would force
  -- `withFreshCache` on every implication descent, changing which subterms simp
  -- revisits and so the trace itself.
  let base := Simp.mkMethods simprocs (instrumentDischarge ref d)
    (wellBehavedDischarge := discharge?.isNone)
  { base with
    pre := instrument ref "pre" base.pre
    post := instrument ref "post" base.post
    dpre := instrumentD ref base.dpre
    dpost := instrumentD ref base.dpost }

end ExplicitLean.SimpTrace
