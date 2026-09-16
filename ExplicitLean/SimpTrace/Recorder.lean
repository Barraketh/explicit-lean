/-
Step recorder: wraps stock `Simp.Methods` so every firing of a `pre`/`post`
procedure is logged as a raw `(before, after, provenance)` triple, together with
the side-condition sub-runs the discharger performed.

Recorder machinery only.  Positions are *not* computed here; see
`ExplicitLean/SimpTrace/Position.lean`.
-/
import Lean
import ExplicitLean.SimpTrace.Types

namespace ExplicitLean.SimpTrace

open Lean Meta Elab

/-- Where a recorded firing came from. -/
inductive Provenance where
  /-- A simp theorem or local hypothesis fired. `inv` is `←`. -/
  | thm (origin : Origin) (inv : Bool)
  /-- A simproc or other non-lemma procedure produced the result. `name?` is the
  procedure we could attribute it to, when we could. -/
  | proc (name? : Option Name)
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
private def captureCtx : MetaM (LocalContext × LocalInstances) := do
  return ((← getLCtx), (← getLocalInstances))

/-- Attribute a `Simp.Result` produced by a procedure whose name we do not know
directly.  `usedTheorems` grows by exactly the theorems the procedure used, so a
single new entry identifies a lemma firing; otherwise we call it a simproc. -/
private def classify (before after : Expr) (usedBefore usedAfter : Simp.UsedSimps)
    : Provenance :=
  -- A lemma firing registers its origin in `usedTheorems`.
  let newOnes := usedAfter.toArray.filter fun o => !usedBefore.contains o
  if h : newOnes.size = 1 then
    match newOnes[0] with
    | .decl n p inv => .thm (.decl n p inv) inv
    | o => .thm o false
  else
    if before == after then .defeq else .proc none

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
        let (lctx, localInsts) ← captureCtx
        let prov := classify e r.expr usedBefore usedAfter
        let side := (← ref.get).pendingSide
        ref.modify fun (s : RecorderState) =>
          RecorderState.push { s with pendingSide := #[] }
            { provenance := prov, before := e, after := r.expr,
              lctx, localInsts, side }
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
        let (lctx, localInsts) ← captureCtx
        ref.modify fun (s : RecorderState) =>
          RecorderState.push s
            { provenance := .defeq, before := e, after := e',
              lctx, localInsts }
    match stepResult with
    | .done e' => record e'
    | .visit e' => record e'
    | .continue (some e') => record e'
    | .continue none => pure ()
    return stepResult

/-- Name how a side condition closed, for the sub-trace's `close`. -/
private def describeProof (proof : Expr) (nested : Array RawStep) :
    Simp.SimpM (Option String) := do
  match proof with
  | .fvar fvarId =>
    let n := (← fvarId.getDecl).userName
    return some s!"assumption:{n}"
  | _ =>
    if nested.isEmpty then
      -- No recorded rewriting: the discharger closed it definitionally or by a
      -- decision procedure.  Distinguish the common shapes.
      if proof.isAppOf ``of_eq_true then return some "rfl"
      else if proof.isAppOf ``eq_true_of_decide then return some "decide"
      else if proof.isAppOf ``trivial || proof.isAppOf ``True.intro then
        return some "trivial"
      else return some "unknown"
    else
      return some "rfl"

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
      let by_ ← describeProof proof nested
      let sideRec : RawSide := { goal := e, steps := nested, by_ }
      ref.modify fun (s : RecorderState) =>
        { s with pendingSide := s.pendingSide.push sideRec }
      return some proof

/-- Build instrumented `Methods` around the stock defaults. -/
def mkRecordingMethods (ref : RecorderRef) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) : Simp.Methods :=
  let d : Simp.Discharge := discharge?.getD Simp.dischargeDefault?
  let base := Simp.mkMethods simprocs (instrumentDischarge ref d)
    (wellBehavedDischarge := false)
  { base with
    pre := instrument ref "pre" base.pre
    post := instrument ref "post" base.post
    dpre := instrumentD ref base.dpre
    dpost := instrumentD ref base.dpost }

end ExplicitLean.SimpTrace
