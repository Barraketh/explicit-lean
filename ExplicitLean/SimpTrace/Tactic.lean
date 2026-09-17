/-
The `simp_trace` tactic.

`simp_trace` runs the **forked traversal** (`ExplicitLean/SimpTrace/Traversal.lean`),
which is stock simp's traversal plus position threading and logging, and emits
the trace described in `tracking/SIMP-TRACE-SPEC.md`.  It accepts exactly the
argument forms `simp` accepts, plus an optional trailing `=>trace "<path>"`
clause naming the file to write the trace JSON to.  Without it the JSON is
logged as `simp-trace-json:{...}` so a driver can collect it.

The goal state after `simp_trace` is the state stock `simp` would leave: we
replicate `Meta.simpGoal`'s structure (it does not accept custom `Methods`) and
apply the same results with the same `applySimpResult*` helpers.

**Outcome classification.**  When a call cannot be fully traced — an
unrepresentable step, an unsupported discharger, a simproc equation no ordinary
tactic proves — the tactic still leaves stock simp's goal state *and* reports a
single classified line `simp_trace unresolved: <reason>`.  Never a generic
abort, never a silent drop.

Recorder machinery only.  This module is never imported by translated source.
-/

module

public meta import Lean
public meta import ExplicitLean.SimpTrace.Types
public meta import ExplicitLean.SimpTrace.Traversal
public meta import ExplicitLean.SimpTrace.Recorder
public meta import ExplicitLean.SimpTrace.Position

public meta section

namespace ExplicitLean.SimpTrace

open Lean Meta Elab Tactic Parser.Tactic

/-! ### Syntax

The argument slots mirror `Parser.Tactic.simp` exactly, so we can rebuild a
genuine `simp` syntax node and hand it to stock `mkSimpContext`, which reads its
arguments by position.
-/

/-- The out-clause, written *last* and delimited by `=>trace`.

Delimiter choice is what makes `simp_trace` substitutable for `simp`.  A
*leading* `(out := ...)` makes the parser commit on the first `(` and demand
`out`, so `simp`'s own parenthesized forms (`(config := ...)`,
`(discharger := ...)`, `(disch := ...)`) become unwritable.  A *trailing*
`(out := ...)` is swallowed by `optConfig` when no other argument precedes it,
and a bare trailing `out := ...` is swallowed by the `location` parser in
`simp_trace ... at h`.  A plain keyword atom would parse but is reserved
globally on import, breaking identifiers of that name; a *non-reserved* keyword
is swallowed by the `location` parser again.  `=>trace` is not an identifier at
all, so it is unambiguous for the parser and invisible to the namespace. -/
syntax simpTraceOut := " =>trace " str

syntax (name := simpTrace) "simp_trace" optConfig
  (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (location)? (simpTraceOut)? : tactic

/-! ### Pretty-printing helpers -/

/-- Pretty-print an expression inside a captured local context. -/
def ppIn (c : EvCtx) (e : Expr) : MetaM String :=
  withLCtx c.lctx c.insts do
    return (← ppExpr e).pretty

/-- Pretty-print with `pp.all` for `change` steps. -/
def ppAllIn (c : EvCtx) (e : Expr) : MetaM String :=
  withLCtx c.lctx c.insts do
    withOptions (fun o => (o.setBool `pp.all true)) do
      return (← ppExpr e).pretty

/-! ### Classifying an `eq` step's proving tactic -/

/-- Which ordinary tactic proves the equation `ty`, by actually running the
candidate in a scratch metavariable. -/
def scratchCheckType (ty : Expr) : MetaM String := do
  let rflOk ← try
      withoutModifyingState do
        let mv ← mkFreshExprSyntheticOpaqueMVar ty
        mv.mvarId!.refl
        return true
    catch _ => pure false
  if rflOk then return "rfl"
  let decideOk ← try
      withoutModifyingState do
        let d ← mkDecide ty
        let r ← withDefault <| whnf d
        return r.isConstOf ``true
    catch _ => pure false
  if decideOk then return "decide" else return "unknown"

/--
Decide which `eq`-step tactic proves `lhs = rhs`, by actually running the
candidate in a scratch metavariable.  Returns `"rfl"`, `"decide"` or
`"unknown"`.  A `by` value is never invented: `unknown` makes the call
unresolved (classified), it does not claim a tactic that does not work.

`sideEqs` are equations the simproc established for itself inside its own
nested `simp` — for `reduceIte` on `if c then a else b`, the pair `(c, True)`.
Replay reaches this step with those already rewritten (they are the step's
`side` traces), so the check substitutes them before deciding: the honest
question is whether the equation holds *given the side conditions*, not in
isolation.  Without this, every context-dependent simproc looks unresolvable.
-/
def scratchCheckEq (lhs rhs : Expr) (sideEqs : Array (Expr × Expr) := #[]) :
    MetaM String := do
  let ty ← try mkEq lhs rhs catch _ => return "unknown"
  let direct ← scratchCheckType ty
  if direct != "unknown" then return direct
  if sideEqs.isEmpty then return "unknown"
  -- Substitute each side equation's left-hand side by its right-hand side, as a
  -- replayer will have done, and re-ask.
  let lhs' := sideEqs.foldl (init := lhs) fun acc (a, b) =>
    if a == b then acc else acc.replace fun sub => if sub == a then some b else none
  if lhs' == lhs then return "unknown"
  let ty' ← try mkEq lhs' rhs catch _ => return "unknown"
  scratchCheckType ty'

/-! ### Turning events into spec steps -/

/-- The classified reasons collected while building one call's trace. -/
structure Unresolved where
  reasons : Array String := #[]
  deriving Inhabited

def Unresolved.add (u : Unresolved) (r : String) : Unresolved :=
  if u.reasons.contains r then u else { u with reasons := u.reasons.push r }

/-- Name a rewrite origin.  Returns the name, whether the syntax carried a `←`,
and, for a local hypothesis, the spec's `local` reference object.

An inaccessible name is recorded as the pretty-printed form (`a✝`) plus the raw
user name and the context index, so a replay generator can bind it with
`rename_i`.  Never `eraseMacroScopes`: for an inaccessible `a✝` it yields plain
`a`, which in the same context usually denotes a *different*, accessible local. -/
def originName (o : Origin) (c : EvCtx) (contextualFVars : Array FVarId) :
    MetaM (String × Bool × Option LocalRef) := do
  match o with
  | .decl n _ _ => return (n.toString, false, none)
  | .fvar fvarId =>
    withLCtx c.lctx c.insts do
      match c.lctx.find? fvarId with
      | some d =>
        let n := d.userName
        let inaccessible := n.isInaccessibleUserName || n.hasMacroScopes
        let display := (← ppExpr (mkFVar fvarId)).pretty
        if contextualFVars.contains fvarId then
          return (display, false, some (.contextual d.index))
        else
          return (display, false, some (.ordinary n.toString inaccessible d.index))
      | none => return (fvarId.name.toString, false, none)
  | .stx _ ref =>
    let txt := ref.prettyPrint.pretty.trimAscii.toString
    if txt.startsWith "←" then
      return (txt.drop 1 |>.trimAscii.toString, true, none)
    else if txt.startsWith "<-" then
      return (txt.drop 2 |>.trimAscii.toString, true, none)
    else return (txt, false, none)
  | .other n => return (n.toString, false, none)

mutual

/-- Convert one logged event into a spec `Step`.  `contextualFVars` are the
hypotheses `+contextual` introduced, so they land in the separate `local`
namespace the spec defines. -/
partial def eventToStep (ur : IO.Ref Unresolved) (contextualFVars : Array FVarId)
    (ev : Event) : MetaM (Option Step) := do
  match ev with
  | .rw pos o inv prop? before after c args side =>
    let beforePP ← ppIn c before
    let afterPP ← ppIn c after
    let (lemmaName, rev, localRef?) ← originName o c contextualFVars
    let sideSteps ← side.mapM (sideToTrace ur contextualFVars)
    let argStrs ← args.mapM (ppIn c)
    let propStr? := prop?.map (fun b => if b then "true" else "false")
    let step : Step :=
      { kind := "rw", pos := pos, name? := some lemmaName,
        dir? := some (if inv || rev then "rev" else "fwd"),
        prop? := propStr?, local? := localRef?, args := argStrs,
        before? := some beforePP, after? := some afterPP,
        side := sideSteps }
    return some step
  | .eq pos src? before after c side =>
    let beforePP ← ppIn c before
    let afterPP ← ppIn c after
    let sideSteps ← side.mapM (sideToTrace ur contextualFVars)
    -- Equations the simproc established inside its own nested `simp`; they are
    -- this step's `side` traces, so replay has them in hand.
    let sideEqs : Array (Expr × Expr) := side.filterMap fun r =>
      match r.events.back? with
      | some (.rw _ _ _ _ _ a _ _ _) => some (r.goal, a)
      | some (.eq _ _ _ a _ _) => some (r.goal, a)
      | some (.defeq _ _ _ _ a _) => some (r.goal, a)
      | _ => none
    let proofTac ← withLCtx c.lctx c.insts <| scratchCheckEq before after sideEqs
    if proofTac == "unknown" then
      -- The spec's `eq` kind wants a `by` replay can execute.  We do not invent
      -- one, and we do not *drop* the step either — dropping it would leave a
      -- trace whose steps no longer reach simp's result, which is worse than an
      -- honest gap.  The step is emitted with a classified `unresolved:` `by`
      -- and the call is reported unresolved, naming the simproc.
      let srcName := (src?.map toString).getD "anonymous"
      ur.modify (·.add s!"simproc equation not provable by rfl or decide \
        ({srcName}): {beforePP} = {afterPP}")
      let step : Step :=
        { kind := "eq", pos := pos,
          lhs? := some beforePP, rhs? := some afterPP,
          by_? := some "unresolved:not provable by rfl or decide",
          source? := some srcName,
          before? := some beforePP, after? := some afterPP,
          side := sideSteps }
      return some step
    let src := (src?.map toString).getD
      (if proofTac == "decide" then "decide" else "simproc")
    let step : Step :=
      { kind := "eq", pos := pos,
        lhs? := some beforePP, rhs? := some afterPP,
        by_? := some proofTac, source? := some src,
        before? := some beforePP, after? := some afterPP,
        side := sideSteps }
    return some step
  | .defeq pos kind unfolded before after c =>
    let beforePP ← ppIn c before
    let afterPP ← ppIn c after
    let step : Step := match kind with
      | .unfold =>
        { kind := "unfold", pos := pos, name? := unfolded.map toString,
          before? := some beforePP, after? := some afterPP }
      | .change =>
        -- Filled in below; `pp.all` needs the monad.
        { kind := "change", pos := pos,
          before? := some beforePP, after? := some afterPP }
      | k =>
        { kind := k.toString, pos := pos,
          before? := some beforePP, after? := some afterPP }
    if kind == .change then
      -- Last resort per the spec: a definitional `change` carrying `pp.all`.
      let toPP ← ppAllIn c after
      return some { step with to? := some toPP }
    return some step
  | .introCtx pos fvarId c =>
    let hypName ← withLCtx c.lctx c.insts do
      pure (← ppExpr (mkFVar fvarId)).pretty
    return some { kind := "intro_ctx", pos := pos, name? := some hypName }

/-- Convert a discharged side condition into the spec's nested trace object. -/
partial def sideToTrace (ur : IO.Ref Unresolved) (contextualFVars : Array FVarId)
    (r : SideRec) : MetaM SideTrace := do
  let c := r.evCtx
  let goalPP ← ppIn c r.goal
  let steps ← r.events.filterMapM (eventToStep ur contextualFVars)
  return { goal := goalPP, steps,
           close := r.by_.map fun b => { by_ := b } }

end

/-! ### Building the `simp` syntax we hand to `mkSimpContext` -/

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

/-! ### Output paths

A tactic that writes files must not be able to write anywhere on the machine.
The trace file must resolve under the current package root (the directory
containing `lakefile.toml`) or under a directory named by
`SIMP_TRACE_OUT_ROOT`; anything else — absolute paths elsewhere, or relative
paths escaping via `..`, including through a symlink — is an error.
-/

/-- Environment variable naming an additional permitted output root. -/
def outRootEnvVar : String := "SIMP_TRACE_OUT_ROOT"

/-- Collapse `.` and `..` without touching the filesystem, so containment is
decided on the path itself rather than on what happens to exist. -/
def normalizeComponents (p : System.FilePath) : List String :=
  p.components.foldl (init := []) fun acc c =>
    if c == "" || c == "." then acc
    else if c == ".." then acc.dropLast
    else acc ++ [c]

/-- Is `path` inside `root`? -/
def isInside (root path : System.FilePath) : Bool :=
  let r := normalizeComponents root
  let p := normalizeComponents path
  r.isPrefixOf p

/-- Search upward from the working directory for the package root. -/
partial def findPackageRoot : IO (Option System.FilePath) := do
  let rec go (dir : System.FilePath) (fuel : Nat) : IO (Option System.FilePath) := do
    if fuel == 0 then return none
    if ← (dir / "lakefile.toml").pathExists then return some dir
    match dir.parent with
    | some parent => go parent (fuel - 1)
    | none => return none
  go (← IO.currentDir) 64

/-- Resolve and validate an out path, or throw. -/
def resolveOutPath (path : String) : MetaM System.FilePath := do
  let raw : System.FilePath := path
  let cwd ← IO.currentDir
  let absolute := if raw.isAbsolute then raw else cwd / raw
  let some parent := absolute.parent
    | throwError "simp_trace: out path has no parent directory: {path}"
  -- Create the parent so it can be resolved, then compare *resolved* paths.
  -- Textual `..` collapsing does not see through a symlink, so a symlink
  -- anywhere under the root would otherwise be a write primitive to any path.
  IO.FS.createDirAll parent
  let realParent ← try IO.FS.realPath parent catch _ => pure parent
  let target := realParent / (absolute.fileName.getD "trace.json")
  let mut roots : Array System.FilePath := #[]
  if let some packageRoot ← findPackageRoot then
    roots := roots.push (← try IO.FS.realPath packageRoot catch _ => pure packageRoot)
  if let some envRoot ← IO.getEnv outRootEnvVar then
    if !envRoot.isEmpty then
      let envPath : System.FilePath := envRoot
      roots := roots.push (← try IO.FS.realPath envPath catch _ => pure envPath)
  if roots.isEmpty then
    throwError "simp_trace: no package root found (no lakefile.toml above the \
      working directory) and {outRootEnvVar} is unset; cannot place {path}"
  unless roots.any (isInside · target) do
    throwError "simp_trace: refusing to write outside the package root\n\
      out:      {path}\n  resolves to: {target}\n\
      permitted roots: {roots.map (·.toString)}\n\
      Set {outRootEnvVar} to permit another directory."
  return target

/-! ### The validator (the safety net)

The forked traversal gives exact positions, so nothing here searches.  This is
the independent check that they are right: replay the recorded steps
structurally from the pre-state term — navigate `pos`, check the subterm equals
`before`, substitute `after` — and require the final term to equal simp's own
result.  On mismatch we fail loudly rather than emit a trace a replayer cannot
follow.
-/

/-- Replay `steps` structurally from `pre`, checking every position. -/
def validate (pre : Expr) (result : Expr) (events : Array Event) : MetaM Unit := do
  let mut running := pre
  for ev in events do
    let (pos, before, after, c) ← match ev with
      | .rw pos _ _ _ b a c _ _ => pure (pos, b, a, c)
      | .eq pos _ b a c _ => pure (pos, b, a, c)
      | .defeq pos _ _ b a c => pure (pos, b, a, c)
      | .introCtx .. => continue
    -- The traversal observed the subterm with its enclosing binders as free
    -- variables; the running term still has loose bvars there.  The event
    -- carries exactly the variables the traversal substituted, outermost first,
    -- so nothing has to be inferred from the local context.
    -- Two depths matter (see `abstractSimpFVars`): the traversal's own binder
    -- stack says which *term variables* it substituted, and `navigate?` says
    -- how many binder *nodes* the path crossed — larger when a non-dependent
    -- arrow sits between them, since an arrow binds nothing but still shifts
    -- de Bruijn indices.
    let introduced := c.binders
    let some (sub, binderNodes) := navigate? running pos
      | throwError "simp_trace: validation failed: no subterm at position {pos}\n\
          in: {running}"
    let expected := abstractSimpFVars before introduced binderNodes
    unless sub == expected do
      throwError "simp_trace: validation failed: subterm at {pos} is\n\
        {sub}\nbut the recorded step's `before` is\n{expected}"
    let replacement := abstractSimpFVars after introduced binderNodes
    let some next := replaceAt? running pos replacement
      | throwError "simp_trace: validation failed: cannot replace at {pos}"
    running := next
  unless running == result do
    throwError "simp_trace: validation failed: replayed term does not match \
      simp's result\nreplayed: {running}\nactual:   {result}"

/-! ### The tactic -/

/-- Turn one traced run into a `LocationTrace`. -/
def buildLocation (ur : IO.Ref Unresolved)
    (hyp? : Option String) (pre : Expr) (result : Simp.Result)
    (events : Array Event) (closed : Bool)
    (absurdHyp? : Option String := none) : MetaM LocationTrace := do
  validate pre result.expr events
  -- Hypotheses `+contextual` introduced, so their references land in the
  -- spec's separate `contextual` namespace.
  let contextualFVars : Array FVarId := events.filterMap fun ev =>
    match ev with
    | .introCtx _ fid _ => some fid
    | _ => none
  let steps ← events.filterMapM (eventToStep ur contextualFVars)
  let prePP := (← ppExpr pre).pretty
  let postPP := (← ppExpr result.expr).pretty
  -- Close forms follow the amended spec.  We never guess `rfl`: a location that
  -- closed for a reason we cannot name is reported unresolved.
  let close : Option CloseInfo ←
    if !closed then pure none
    else if result.expr.isTrue then
      pure (some { by_ := "true_intro" })
    else if result.expr.isFalse then
      match absurdHyp? with
      | some h => pure (some { by_ := s!"absurd:{h}" })
      | none =>
        ur.modify (·.add "location closed via False with no named hypothesis")
        pure (some { by_ := "unresolved:False with no named hypothesis" })
    else
      ur.modify (·.add s!"location closed but result is neither True nor False: \
        {(← ppExpr result.expr).pretty}")
      pure (some { by_ := "unresolved:close form not in the spec" })
  return { hyp?, pre := prePP, post? := if closed then none else some postPP,
           steps, close }

/-- The discharger's tactic text, when the call supplied one.  `omega` has its
own close form in the amended spec; anything else is a classified unresolved
outcome.

`Parser.Tactic.discharger` is
`atomic(" (" patternIgnore(&"discharger" <|> &"disch")) " := " tacticSeq ")"`,
whose `patternIgnore` and `atomic` wrappers make the slot index fragile across
Lean versions.  We therefore pretty-print the whole node and strip the fixed
delimiters, which is stable. -/
def dischargerText? (stx : Syntax) : Option String :=
  if stx[2].isNone then none
  else
    let txt := stx[2].prettyPrint.pretty.trimAscii.toString
    -- "(disch := omega)" / "(discharger := omega)" -> "omega"
    let txt := if txt.startsWith "(" then txt.drop 1 |>.toString else txt
    let txt := if txt.endsWith ")" then txt.dropRight 1 else txt
    match txt.splitOn ":=" with
    | _ :: rest => some ((String.intercalate ":=" rest).trimAscii.toString)
    | [] => some txt.trimAscii.toString

@[tactic simpTrace]
def evalSimpTrace : Tactic := fun stx => withMainContext do
  let simpStx := toSimpSyntax stx
  let selection ← elabSelection stx
  let r@{ ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext simpStx (eraseLocal := false)
  if ctx.config.suggestions then
    throwError "+suggestions requires using simp? instead of simp"
  let dtext? := dischargerText? stx
  let ur ← IO.mkRef ({} : Unresolved)
  let locsRef ← IO.mkRef (#[] : Array LocationTrace)
  let addLoc (l : LocationTrace) : MetaM Unit := locsRef.modify (·.push l)

  -- Replicate `Meta.simpGoal`, substituting `runTraced` (the fork) for
  -- `Meta.simp`.
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
        let (res, stats', events, unres) ←
          runTraced type hctx simprocs discharge? dtext? stats
        stats := stats'
        for u in unres do ur.modify (·.add u)
        let hypName := localDecl.userName.toString
        match res.proof? with
        | some _ =>
          match (← applySimpResult mvarIdNew (mkFVar fvarId) type res) with
          | none =>
            addLoc (← buildLocation ur (some hypName) type res events true
              (absurdHyp? := some hypName))
            done := true
          | some (value, newType) =>
            addLoc (← buildLocation ur (some hypName) type res events false)
            toAssert := toAssert.push
              { userName := localDecl.userName, type := newType, value }
        | none =>
          if res.expr.isFalse then
            mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
            addLoc (← buildLocation ur (some hypName) type res events true
              (absurdHyp? := some hypName))
            done := true
          else
            addLoc (← buildLocation ur (some hypName) type res events false)
            mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId res.expr
            replaced := replaced.push fvarId
      if done then
        return true
      if selection.simplifyTarget then
        let (closedTarget, nextGoal?) ← mvarIdNew.withContext do
          mvarIdNew.checkNotAssigned `simp_trace
          let target ← instantiateMVars (← mvarIdNew.getType)
          let (res, _, events, unres) ←
            runTraced target ctx simprocs discharge? dtext? stats
          for u in unres do ur.modify (·.add u)
          if res.expr.isTrue then
            match res.proof? with
            | some proof => mvarIdNew.assign (← mkOfEqTrue proof)
            | none => mvarIdNew.assign (mkConst ``True.intro)
            addLoc (← buildLocation ur none target res events true)
            return (true, none)
          else
            let next ← applySimpResultToTarget mvarIdNew target res
            addLoc (← buildLocation ur none target res events false)
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
    IO.FS.writeFile (← resolveOutPath path) json
  | none =>
    logInfo m!"simp-trace-json:{json}"
  -- One classified line per call, so a driver can catalogue it.  The goal state
  -- is stock simp's either way.
  let u ← ur.get
  unless u.reasons.isEmpty do
    logError m!"simp_trace unresolved: {String.intercalate "; " u.reasons.toList}"
where
  /-- The `=>trace "..."` path, when given.  The clause is the last slot. -/
  outPath? (stx : Syntax) : Option String :=
    if stx[6].isNone then none
    else stx[6][0][1].isStrLit?

end ExplicitLean.SimpTrace
