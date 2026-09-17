/-
The `simp_trace` tactic.

`simp_trace` runs **stock simp** and records the trace described in
`tracking/SIMP-TRACE-SPEC.md`.  It accepts exactly the argument forms `simp`
accepts, plus an optional leading `(out := "<path>")` clause naming the file to
write the trace JSON to.  With no `out` clause the JSON is logged as an info
message tagged `simp-trace-json:` so a driver can collect it from the compiler
output.

The goal state after `simp_trace` is the state stock `simp` would leave: we
replicate `Meta.simpGoal`'s structure (it does not accept custom `Methods`) and
apply the same results with the same `applySimpResult*` helpers.

Recorder machinery only.  This module is never imported by translated source.
-/

module

public meta import Lean
public meta import ExplicitLean.SimpTrace.Types
public meta import ExplicitLean.SimpTrace.Recorder
public meta import ExplicitLean.SimpTrace.Position

public meta section

namespace ExplicitLean.SimpTrace

open Lean Meta Elab Tactic Parser.Tactic

/-! ### Syntax

The argument slots after `(out := ...)` mirror `Parser.Tactic.simp` exactly, so
we can rebuild a genuine `simp` syntax node and hand it to stock
`mkSimpContext`, which reads its arguments by position.
-/

/-- The out-clause.  It is written *last* and introduced by its own `out`
keyword rather than an open paren, so it can never compete with `simp`'s own
parenthesized forms (`(config := ...)`, `(discharger := ...)`, `(disch := ...)`).
A paren-led clause makes the parser commit on `(` and demand `out`, which would
leave `simp_trace` unable to express those forms at all — i.e. not substitutable
for `simp`, the whole point of the tactic. -/
syntax simpTraceOut := &" out" " := " str

syntax (name := simpTrace) "simp_trace" optConfig
  (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (location)? (simpTraceOut)? : tactic

/-! ### Pretty-printing helpers -/

/-- Pretty-print an expression inside a captured local context. -/
def ppIn (lctx : LocalContext) (insts : LocalInstances) (e : Expr) : MetaM String :=
  withLCtx lctx insts do
    return (← ppExpr e).pretty

/-- Pretty-print with `pp.all` for `change` steps. -/
def ppAllIn (lctx : LocalContext) (insts : LocalInstances) (e : Expr) : MetaM String :=
  withLCtx lctx insts do
    withOptions (fun o => (o.setBool `pp.all true)) do
      return (← ppExpr e).pretty

/-! ### Classifying a raw firing into a spec `Step` -/

/-- Is `after` obtained from `before` by beta reduction alone? -/
private def isBeta (before after : Expr) : Bool :=
  before.isApp && before.getAppFn.isLambda && before.headBeta == after

/-- Is this an eta contraction? -/
private def isEta (before after : Expr) : Bool :=
  match before.etaExpanded? with
  | some _ => false
  | none => before.isLambda && after == before.eta

/-- Detect a projection reduction: `.proj` or a structure-projection application
whose result is the corresponding field. -/
private def isProj (before : Expr) : Bool :=
  before.isProj

/--
Decide which `eq`-step tactic proves `lhs = rhs`, by actually running the
candidate in a scratch metavariable.  Returns `"rfl"`, `"decide"` or `"unknown"`.
-/
def scratchCheckEq (lhs rhs : Expr) : MetaM String := do
  let ty ← try mkEq lhs rhs catch _ => return "unknown"
  -- `rfl`
  let rflOk ← try
      withoutModifyingState do
        let mv ← mkFreshExprSyntheticOpaqueMVar ty
        mv.mvarId!.refl
        return true
    catch _ => pure false
  if rflOk then return "rfl"
  -- `decide`
  let decideOk ← try
      withoutModifyingState do
        let d ← mkDecide ty
        let r ← withDefault <| whnf d
        return r.isConstOf ``true
    catch _ => pure false
  if decideOk then return "decide" else return "unknown"

/-- Counter of `eq` steps whose proving tactic we could not confirm. -/
structure Counters where
  unknownEq : Nat := 0
  deriving Inhabited

/-- Convert one solved raw step into a spec `Step`. -/
partial def toStep (counters : IO.Ref Counters) (s : SolvedStep) : MetaM Step := do
  let raw := s.raw
  let beforePP ← ppIn raw.lctx raw.localInsts raw.before
  let afterPP ← ppIn raw.lctx raw.localInsts raw.after
  let side ← raw.side.mapM (toSide counters)
  match raw.provenance with
  | .thm origin inv =>
    -- A simproc registers its declaration name in `usedTheorems` just as a
    -- lemma does; the spec wants those recorded as `eq`, not `rw`.
    if let .decl declName _ _ := origin then
      if ← Simp.isSimproc declName then
        return ← mkEqStep counters raw s.pos beforePP afterPP (some declName) side
    let (name, rev) ← originName origin raw.lctx raw.localInsts
    return { kind := "rw", pos := s.pos, name? := some name,
             dir? := some (if inv || rev then "rev" else "fwd"),
             before? := some beforePP, after? := some afterPP, side }
  | .proc name? =>
    -- A simproc-computed equation.  Confirm the replay tactic really proves it.
    return ← mkEqStep counters raw s.pos beforePP afterPP name? side
  | .unattributed =>
    -- The recorder saw a change it could not attribute to a lemma or simproc.
    -- Per the task, never drop a step silently: fail loudly.
    throwError "simp_trace: unattributed simp step (no recordable kind)\n\
      before: {beforePP}\nafter:  {afterPP}"
  | .defeq =>
    if isBeta raw.before raw.after then
      return { kind := "beta", pos := s.pos,
               before? := some beforePP, after? := some afterPP }
    else if isEta raw.before raw.after then
      return { kind := "eta", pos := s.pos,
               before? := some beforePP, after? := some afterPP }
    else if isProj raw.before then
      return { kind := "proj", pos := s.pos,
               before? := some beforePP, after? := some afterPP }
    else if raw.before.isLet then
      -- `zeta`: `let x := v; b` to `b[v/x]` (amended spec).
      return { kind := "zeta", pos := s.pos,
               before? := some beforePP, after? := some afterPP }
    else if let some c := unfoldedConstant? raw.before raw.after then
      return { kind := "unfold", pos := s.pos, name? := some c.toString,
               before? := some beforePP, after? := some afterPP }
    else
      -- Last resort per the spec: a definitional `change` carrying `pp.all`.
      let toPP ← ppAllIn raw.lctx raw.localInsts raw.after
      return { kind := "change", pos := s.pos, to? := some toPP,
               before? := some beforePP, after? := some afterPP }
where
  /-- Build an `eq` step, verifying in a scratch check which ordinary tactic
  actually proves the equation the simproc produced. -/
  mkEqStep (counters : IO.Ref Counters) (raw : RawStep) (pos : Pos)
      (beforePP afterPP : String) (source? : Option Name)
      (side : Array SideTrace) : MetaM Step := do
    let by_ ← withLCtx raw.lctx raw.localInsts <|
      scratchCheckEq raw.before raw.after
    if by_ == "unknown" then
      counters.modify fun c => { c with unknownEq := c.unknownEq + 1 }
    return { kind := "eq", pos,
             lhs? := some beforePP, rhs? := some afterPP,
             by_? := some by_,
             source? := some ((source?.map toString).getD
               (if by_ == "decide" then "decide" else "simproc")),
             before? := some beforePP, after? := some afterPP, side }

  /-- Name a rewrite origin, resolving local hypotheses to their user names.
  Returns the name and whether the syntax carried a `←`. -/
  originName (o : Origin) (lctx : LocalContext) (insts : LocalInstances) :
      MetaM (String × Bool) := do
    match o with
    | .decl n _ _ => return (n.toString, false)
    | .fvar fvarId =>
      withLCtx lctx insts do
        match lctx.find? fvarId with
        | some d =>
          -- `+contextual` introduces inaccessible antecedent hypotheses; give
          -- them the stable name the matching `intro_ctx` step uses.
          let n := d.userName
          if n.isInaccessibleUserName || n.hasMacroScopes then
            return (s!"ctx:{d.index}", false)
          else return (n.toString, false)
        | none => return (fvarId.name.toString, false)
    | .stx _ ref =>
      -- `simp [← h]` records the argument syntax; strip the arrow into `dir`.
      let txt := ref.prettyPrint.pretty.trimAscii.toString
      if txt.startsWith "←" then
        return (txt.drop 1 |>.trimAscii.toString, true)
      else if txt.startsWith "<-" then
        return (txt.drop 2 |>.trimAscii.toString, true)
      else return (txt, false)
    | .other n => return (n.toString, false)

  /-- The head constant that was delta-unfolded, when that is what happened. -/
  unfoldedConstant? (before after : Expr) : Option Name :=
    match before.getAppFn with
    | .const n _ => if after.getAppFn != before.getAppFn then some n else none
    | _ => none

  toSide (counters : IO.Ref Counters) (r : RawSide) : MetaM SideTrace := do
    let goalPP ← ppExpr r.goal
    -- Nested steps were recorded against the side goal; solve their positions
    -- against that goal exactly as we do for a top-level location.
    let (solved, _) ← solvePositions (← getLCtx) r.goal r.steps
    let steps ← solved.mapM (toStep counters)
    return { goal := goalPP.pretty, steps,
             close := r.by_.map fun b => { by_ := b } }

/-! ### Building the `simp` syntax we hand to `mkSimpContext`

`simp_trace`'s slots are the `simp` slots shifted by one (the `out` clause sits
at index 1).  We rebuild a node of kind `Parser.Tactic.simp` with the original
slots so stock argument elaboration is used verbatim.
-/

def toSimpSyntax (stx : Syntax) : Syntax :=
  let simpTk := mkAtomFrom stx "simp"
  Syntax.node (SourceInfo.fromRef stx) ``Parser.Tactic.simp
    #[simpTk, stx[1], stx[2], stx[3], stx[4], stx[5]]

/-! ### Locations -/

/-- The set of locations `simp_trace` will visit, mirroring `expandOptLocation`. -/
structure Selection where
  fvarIds : Array FVarId
  simplifyTarget : Bool

def elabSelection (stx : Syntax) : TacticM Selection := do
  match expandOptLocation stx[5] with
  | .targets hyps simplifyTarget =>
    return { fvarIds := ← getFVarIds hyps, simplifyTarget }
  | .wildcard =>
    return { fvarIds := ← (← getMainGoal).getNondepPropHyps, simplifyTarget := true }

/-! ### The tactic -/

/-- Run instrumented simp on one expression, returning the result and the raw
steps it fired. -/
def tracedSimp (e : Expr) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) (stats : Simp.Stats) :
    MetaM (Simp.Result × Simp.Stats × Array RawStep) := do
  let ref ← IO.mkRef ({} : RecorderState)
  let methods := mkRecordingMethods ref simprocs discharge?
  let (r, stats) ← Simp.main e ctx stats (methods := methods)
  let st ← ref.get
  unless st.unsupported.isEmpty do
    throwError "simp_trace: unsupported simp step kind(s): {st.unsupported}"
  return (r, stats, st.steps)

/-- Turn one traced run into a `LocationTrace`, validating every position. -/
def buildLocation (counters : IO.Ref Counters) (hyp? : Option String)
    (pre : Expr) (result : Simp.Result) (raws : Array RawStep)
    (closed : Bool) : MetaM LocationTrace := do
  let (solved, running) ← solvePositions (← getLCtx) pre raws
  -- Validation: the replayed running term must be simp's actual result.
  unless running == result.expr do
    throwError "simp_trace: replayed term does not match simp's result\n\
      replayed: {running}\nactual:   {result.expr}"
  let steps ← solved.mapM (toStep counters)
  let prePP := (← ppExpr pre).pretty
  let postPP := (← ppExpr result.expr).pretty
  let close : Option CloseInfo :=
    if closed then
      if result.expr.isTrue then some { by_ := "trivial" }
      else if result.expr.isFalse then some { by_ := "assumption:False" }
      else some { by_ := "rfl" }
    else none
  return { hyp?, pre := prePP, post? := if closed then none else some postPP,
           steps, close }

@[tactic simpTrace]
def evalSimpTrace : Tactic := fun stx => withMainContext do
  let simpStx := toSimpSyntax stx
  let selection ← elabSelection stx
  let r@{ ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  if ctx.config.suggestions then
    throwError "+suggestions requires using simp? instead of simp"
  let counters ← IO.mkRef ({} : Counters)
  let locsRef ← IO.mkRef (#[] : Array LocationTrace)
  let addLoc (l : LocationTrace) : MetaM Unit := locsRef.modify (·.push l)

  -- Replicate `Meta.simpGoal`, substituting `tracedSimp` for `Meta.simp`.
  let goal ← getMainGoal
  let initialGoals ← getGoals
  let tail := initialGoals.tail
  let closedAll ← dischargeWrapper.with fun discharge? => withLoopChecking r do
    goal.withContext do
      goal.checkNotAssigned `simp_trace
      let mut mvarIdNew := goal
      let mut toAssert : Array Hypothesis := #[]
      let mut replaced : Array FVarId := #[]
      let mut stats : Simp.Stats := {}
      let mut done := false
      for fvarId in selection.fvarIds do
        if done then continue
        let localDecl ← fvarId.getDecl
        let type ← instantiateMVars localDecl.type
        let hctx := ctx.setSimpTheorems <|
          ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId)
        let (res, stats', raws) ←
          tracedSimp type hctx simprocs discharge? stats
        stats := stats'
        let hypName := localDecl.userName.toString
        match res.proof? with
        | some _ =>
          match (← applySimpResult mvarIdNew (mkFVar fvarId) type res) with
          | none =>
            addLoc (← buildLocation counters (some hypName) type res raws true)
            done := true
          | some (value, newType) =>
            addLoc (← buildLocation counters (some hypName) type res raws false)
            toAssert := toAssert.push
              { userName := localDecl.userName, type := newType, value }
        | none =>
          if res.expr.isFalse then
            mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
            addLoc (← buildLocation counters (some hypName) type res raws true)
            done := true
          else
            addLoc (← buildLocation counters (some hypName) type res raws false)
            mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId res.expr
            replaced := replaced.push fvarId
      if done then
        return true
      if selection.simplifyTarget then
        let (closedTarget, nextGoal?) ← mvarIdNew.withContext do
          mvarIdNew.checkNotAssigned `simp_trace
          let target ← instantiateMVars (← mvarIdNew.getType)
          let (res, _, raws) ← tracedSimp target ctx simprocs discharge? stats
          if res.expr.isTrue then
            match res.proof? with
            | some proof => mvarIdNew.assign (← mkOfEqTrue proof)
            | none => mvarIdNew.assign (mkConst ``True.intro)
            addLoc (← buildLocation counters none target res raws true)
            return (true, none)
          else
            let next ← applySimpResultToTarget mvarIdNew target res
            addLoc (← buildLocation counters none target res raws false)
            return (false, some next)
        match nextGoal? with
        | some next => mvarIdNew := next
        | none => pure ()
        if closedTarget then
          return true
      let (_, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
      mvarIdNew := mvarIdNew'
      let toClear := selection.fvarIds.filter fun f => !replaced.contains f
      mvarIdNew ← mvarIdNew.tryClearMany toClear
      if ctx.config.failIfUnchanged && goal == mvarIdNew then
        throwError "`simp_trace` made no progress"
      setGoals (mvarIdNew :: tail)
      return false

  if closedAll then
    setGoals tail

  -- Emit the trace.
  let trace : CallTrace := {
    module := (← getEnv).mainModule.toString
    occurrence := toString ((← getRef).getPos?.getD 0)
    call := stx.prettyPrint.pretty.trimAscii.toString
    locations := ← locsRef.get }
  let json := trace.toJson
  match outPath? stx with
  | some path =>
    IO.FS.writeFile path json
  | none =>
    logInfo m!"simp-trace-json:{json}"
  let c ← counters.get
  if c.unknownEq > 0 then
    logInfo m!"simp_trace: {c.unknownEq} `eq` step(s) with by=\"unknown\""
where
  /-- The `(out := "...")` path, when given.  The clause is the last slot. -/
  outPath? (stx : Syntax) : Option String :=
    if stx[6].isNone then none
    else stx[6][0][2].isStrLit?

end ExplicitLean.SimpTrace
