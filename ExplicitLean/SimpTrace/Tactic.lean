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
public meta import ExplicitLean.ExplicitRw.Basic
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

/-- Pretty-print an `args` entry: a term a replayer writes, so it must be
self-contained and splice into an application.

`pp.proofs` is set because the default elides a proof as `⋯`, which cannot be
elaborated at all; the term-size limits are raised for the same reason.  The
result is parenthesised unless it is already atomic, since the spec has the
replayer splice it after the lemma name and `rw [l if Q then a else b b]` is a
parse error (REVIEW-8 4). -/
def ppArg (c : EvCtx) (e : Expr) : MetaM String :=
  withLCtx c.lctx c.insts do
    if let some (_, handle) := c.introduced.find? (fun (f, _) =>
        e.isFVar && e.fvarId! == f) then
      return s!"introduced_ref {handle}"
    let s ← withOptions (fun o =>
        ((o.setBool `pp.proofs true).setBool `pp.deepTerms true)) do
      pure (← ppExpr e).pretty
    -- Atomic: an identifier, a literal, or already fully bracketed.
    let atomic := !s.any (fun ch => ch == ' ')
    return if atomic then s else "(" ++ s ++ ")"

/-- Pretty-print the target of a `change` step as ordinary Lean source.

This text is consumed by the elaborator in the captured context, so implicit
arguments, instances and universe levels must remain implicit.  Proofs and
deep terms are enabled to avoid the pretty-printer's non-source elision forms;
we do not enable `pp.all`, which exposes implementation names such as
`nat_lit` and inaccessible instance details.  Newlines emitted for layout are
collapsed deterministically because the renderer splices this term into a
single `change` tactic.  We do not rename or sanitize free variables: an
inaccessible local that has no ordinary source name remains a replay failure. -/
def ppChangeTo (c : EvCtx) (e : Expr) : MetaM String :=
  withLCtx c.lctx c.insts do
    withOptions (fun o =>
        let o := o.setBool `pp.all false
        let o := o.setBool `pp.explicit false
        let o := o.setBool `pp.universes false
        let o := o.setBool `pp.instances false
        let o := o.setBool `pp.natLit false
        let o := o.setBool `pp.numericTypes false
        let o := o.setBool `pp.notation true
        let o := o.setBool `pp.proofs true
        let o := o.setBool `pp.deepTerms true
        o.set `format.width (10000 : Nat)) do
      let txt := (← ppExpr e).pretty
      return " ".intercalate
        (txt.splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty))

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

/-! ### Structured validation verdicts

The validator walks the event tree before rendering it.  A call-level reason is
useful for diagnostics, but it is not enough for a consumer of the JSON: a
rewrite in a discharged side goal (or under a dependent congruence node) is a
separate replay action.  Keep a verdict tree parallel to the event tree so the
reason is attached to the exact rendered `Step`.
-/

inductive ValidationVerdict where
  | mk (reason? : Option String)
      (side : Array (Array ValidationVerdict))
      (nested : Array ValidationVerdict)

def ValidationVerdict.reason? : ValidationVerdict → Option String
  | .mk reason? _ _ => reason?

def ValidationVerdict.side : ValidationVerdict → Array (Array ValidationVerdict)
  | .mk _ side _ => side

def ValidationVerdict.nested : ValidationVerdict → Array ValidationVerdict
  | .mk _ _ nested => nested

/-- Name a rewrite origin.  Returns the name, whether the syntax carried a `←`,
and, for a local hypothesis, the spec's `local` reference object.

An inaccessible name is recorded as the pretty-printed form (`a✝`) plus the raw
user name and the context index, so a replay generator can bind it with
`rename_i`.  Never `eraseMacroScopes`: for an inaccessible `a✝` it yields plain
`a`, which in the same context usually denotes a *different*, accessible local. -/
def originName (o : Origin) (c : EvCtx)
    (contextualFVars : Array (FVarId × Nat)) :
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
        if let some (_, handle) := contextualFVars.find? (fun (f, _) => f == fvarId) then
          return (display, false, some (.contextual d.index handle))
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
partial def eventToStep (ur : IO.Ref Unresolved)
    (contextualFVars : Array (FVarId × Nat))
    (ev : Event) : MetaM (Option Step) := do
  match ev with
  | .rw pos o inv prop? before after c args side src? localO proj derivation? _sourceValue? =>
    let beforePP ← ppIn c before
    let afterPP ← ppIn c after
    -- `dir` still comes from the written syntax, which is what carries a
    -- leading `←`; `name` does not.  The spec says `name` is "<lemma or hyp
    -- name>", and pretty-printing the syntax put whole terms there --
    -- `heq_comm (a := a)`, `@forall_eq _ p a`, `if_neg fun h ↦ hb ⟨a, h⟩` --
    -- which no generator can emit as a name.  Take `name` (and the `local`
    -- object) from the *resolved* origin, so `simp [h]` and `simp [*]` agree
    -- and the name is always a bare constant or a local's display name; the
    -- arguments the syntax applied travel in `args` (REVIEW-9 2, 3).
    let (_, rev, _) ← originName o c contextualFVars
    let (baseName, _, localRef?) ← originName localO c contextualFVars
    -- The projection is part of the name a replayer must write.
    let lemmaName := baseName ++ proj
    let sideSteps ← side.mapM (sideToTrace ur contextualFVars)
    let argStrs ← args.mapM (ppArg c)
    let propStr? := prop?.map (fun b => if b then "true" else "false")
    let step : Step :=
      { kind := "rw", pos := pos, name? := some lemmaName,
        dir? := some (if inv || rev then "rev" else "fwd"),
        prop? := propStr?, local? := localRef?, args := argStrs,
        -- Present only when this `rw` came from a simproc whose proof was this
        -- one lemma applied (amended spec): provenance, not a replay input.
        source? := src?.map toString,
        before? := some beforePP, after? := some afterPP,
        side := sideSteps, derivation? := derivation? }
    return some step
  | .eq pos src? before after c side =>
    let beforePP ← ppIn c before
    let afterPP ← ppIn c after
    let sideSteps ← side.mapM (sideToTrace ur contextualFVars)
    -- Equations the simproc established inside its own nested `simp`; they are
    -- this step's `side` traces, so replay has them in hand.
    let sideEqs : Array (Expr × Expr) := side.filterMap fun r =>
      match r.events.back? with
      | some (.rw _ _ _ _ _ a ..) => some (r.goal, a)
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
      -- The amended spec's classified form for a simproc proof that is neither
      -- one lemma applied nor kernel-checkable.
      ur.modify (·.add s!"simproc:{srcName} ({beforePP} = {afterPP})")
      let step : Step :=
        { kind := "eq", pos := pos,
          lhs? := some beforePP, rhs? := some afterPP,
          by_? := some s!"unresolved:simproc:{srcName}",
          source? := some srcName,
          before? := some beforePP, after? := some afterPP,
          side := sideSteps }
      return some step
    -- The spec's `eq` bullet says `"source"` is the simproc's name.  When the
    -- firing registered no origin we do not know it, and a placeholder like
    -- `"simproc"` would name nothing while looking like provenance, so the
    -- field is omitted (REVIEW-4 minor 6).  It is **not** an unresolved
    -- outcome: `source` is optional provenance and the step itself is a
    -- complete, replayable `eq` whose `by` the scratch check confirmed.
    -- Marking it unresolved made `simp_trace` exit 1 on goals stock `simp`
    -- proves, reintroducing REVIEW-3 C1 through the back door (REVIEW-5 3).
    let step : Step :=
      { kind := "eq", pos := pos,
        lhs? := some beforePP, rhs? := some afterPP,
        by_? := some proofTac, source? := src?.map toString,
        before? := some beforePP, after? := some afterPP,
        side := sideSteps }
    return some step
  | .defeq pos kind unfolded before after c =>
    let beforePP ← ppIn c before
    let afterPP ← ppIn c after
    let zetaLocal? ←
      if kind == .zeta && unfolded.isSome && before.isFVar then
        let (_, _, local?) ← originName (.fvar before.fvarId!) c contextualFVars
        pure local?
      else
        pure none
    let step : Step := match kind with
      | .unfold =>
        { kind := "unfold", pos := pos, name? := unfolded.map toString,
          before? := some beforePP, after? := some afterPP }
      | .change =>
        -- Filled in below; printing `change.to` needs the monad.  `name?` carries the
        -- dsimproc's name here, which the spec renders as `source` (e95c745).
        { kind := "change", pos := pos, source? := unfolded.map toString,
          before? := some beforePP, after? := some afterPP }
      | .zeta =>
        -- A `zetaDelta` unfold names the local it replaced, so a replayer knows
        -- *which* one (REVIEW-6 6); a plain `letE` zeta carries no name.
        { kind := "zeta", pos := pos, name? := unfolded.map toString,
          local? := zetaLocal?,
          before? := some beforePP, after? := some afterPP }
      | k =>
        { kind := k.toString, pos := pos,
          before? := some beforePP, after? := some afterPP }
    if kind == .change then
      -- Last resort per the spec: a definitional `change` carrying ordinary
      -- Lean surface syntax, elaborated in the exact captured local context.
      let toPP ← ppChangeTo c after
      return some { step with to? := some toPP }
    return some step
  | .introCtx pos _ _ info =>
    -- Contextual binders have no stable source/display name.  Preserve only
    -- the recorder's operational handle and scope/domain references; the
    -- future renderer resolves these as `introduced_ref <handle>`.
    return some { kind := "intro_ctx", pos := pos, intro? := some info }
  | .introCtxExit .. => return none
  | .congr pos arg nested before after _ _ c =>
    -- Spec 3b17247: `before`/`after` describe the node at `pos`; the nested
    -- steps' positions are relative to argument `arg`.
    let beforePP ← ppIn c before
    let afterPP ← ppIn c after
    let nestedSteps ← nested.filterMapM (eventToStep ur contextualFVars)
    return some { kind := "congr", pos := pos, arg? := some arg,
                  steps := nestedSteps,
                  before? := some beforePP, after? := some afterPP }
  | .transport pos handle domain body before after _ _ _ _ c =>
    let beforePP ← ppIn c before
    let afterPP ← ppIn c after
    let domainSteps ← domain.filterMapM (eventToStep ur contextualFVars)
    let bodySteps ← body.filterMapM (eventToStep ur contextualFVars)
    return some { kind := "transport", pos := pos, handle? := some handle,
                  domain := domainSteps, body := bodySteps,
                  before? := some beforePP, after? := some afterPP }

/-- Convert a discharged side condition into the spec's nested trace object. -/
partial def sideToTrace (ur : IO.Ref Unresolved)
    (contextualFVars : Array (FVarId × Nat))
    (r : SideRec) : MetaM SideTrace := do
  let c := r.evCtx
  let goalPP ← ppIn c r.goal
  let steps ← r.events.filterMapM (eventToStep ur contextualFVars)
  -- Antecedents an implication-shaped congruence hypothesis introduced before
  -- its steps.  Pretty-printed so a generator can `intro` them by name.
  let intros := r.intros
  -- Spec e95c745: a side trace carries `pre`/`post` like a location, so a
  -- replayer can tell what the side goal started as and what remains.
  let prePP ← ppIn c r.pre
  let postPP? ← r.post?.mapM (ppIn c)
  return { goal := goalPP, pre := prePP, post? := postPP?, steps, intros,
           close := r.by_.map fun b => { by_ := b } }

end

/-! ### Building the `simp` syntax we hand to `mkSimpContext` -/

def toSimpSyntax (stx : Syntax) : Syntax :=
  let simpTk := mkAtomFrom stx "simp"
  Syntax.node (SourceInfo.fromRef stx) ``Parser.Tactic.simp
    #[simpTk, stx[1], stx[2], stx[3], stx[4], stx[5]]

/-! ### Source argument registration

Stock `mkSimpContext` keeps the original `Syntax` in every `Origin.stx`, but
its private `elabSimpArgs` result is not exposed.  Register the source facts
from the parser nodes before invoking stock elaboration.  IDs are assigned in
the source argument list (site-local), and origins are joined later by their
exact source range.  This is intentionally not theorem-table enumeration and
does not retain an elaborated term. -/

def scalarOffsetOfByte (source : String) (byteIdx : Nat) : Nat :=
  Id.run do
    let mut pos : String.Pos.Raw := 0
    let mut scalarIdx := 0
    while pos.byteIdx < byteIdx && !pos.atEnd source do
      pos := pos.next source
      scalarIdx := scalarIdx + 1
    return scalarIdx

def firstIdent? (stx : Syntax) : Option Syntax := Id.run do
  for child in stx.topDown do
    match child with
    | .ident .. => return some child
    | _ => pure ()
  return none

def sourceIdentText (stx : Syntax) : String :=
  match stx with
  | .ident _ rawVal _ _ => rawVal.toString
  | _ => stx.getId.toString

def sourceHeadIdentity? (term : Syntax) : TacticM (Option (String × Option Name × Bool)) := do
  let some head := firstIdent? term | return none
  -- Resolve only this source head, never the complete argument.  The local
  -- probe is diagnostic-free and gives us the local-vs-declaration bit before
  -- stock simp elaborates the argument.  Full-term re-elaboration is
  -- intentionally forbidden here: projections such as `(h c).1` contain
  -- synthetic field identifiers that emit diagnostics despite being accepted
  -- by stock simp.
  let localExpr? ← runTermElab (Lean.Elab.Term.isLocalIdent? head)
  if localExpr?.isSome then
    -- A hygienic local identifier can carry a generated Name in Syntax.  The
    -- raw token is the stable source identity; the local probe still
    -- records that it is local and verifies the token resolved in this scope.
    return some (sourceIdentText head, none, true)
  let resolved? ← try
      pure (some (← runTermElab (Lean.resolveGlobalConstNoOverload head)))
    catch _ => pure none
  pure (some (sourceIdentText head, resolved?, false))

def registerSourceArgs (stx : Syntax) : TacticM (Array SourceArg) := do
  if stx[4].isNone then return #[]
  let source := (← getFileMap).source
  let mut result : Array SourceArg := #[]
  for (arg, i) in stx[4][1].getSepArgs.zipIdx do
    let some start := arg.getPos? (canonicalOnly := true) | continue
    let some stop := arg.getTailPos? (canonicalOnly := true) | continue
    let startByte := start.byteIdx
    let endByte := stop.byteIdx
    let isLemma := arg.getKind == ``Parser.Tactic.simpLemma
    let term := if isLemma then arg[2] else arg
    let headInfo? ← if isLemma then sourceHeadIdentity? term else pure none
    let head? := headInfo?.map (·.1)
    let headName? := headInfo?.map (fun h => h.2.1) |>.join
    let headLocal := headInfo?.map (fun h => h.2.2) |>.getD false
    let direction := if isLemma && !arg[1].isNone then "rev" else "fwd"
    let kind := if isLemma then "simp-lemma" else arg.getKind.toString
    result := result.push {
      argId := i, startChar := scalarOffsetOfByte source startByte,
      endChar := scalarOffsetOfByte source endByte,
      startByte, endByte,
      direction, kind, head?, headName?, headLocal }
  return result

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

/-!
### Structural check on every emitted `rw`

`isPlumbingHead` is an allowlist, and an allowlist has to be *complete* to be
correct — the wrong shape to rest on (REVIEW-6 3).  It stays as a fast path, but
correctness rests on this check instead: for every `rw` step the validator
re-elaborates `name` applied to `args`, unifies the appropriate side of the
resulting statement with the recorded `before`, and requires the other side to
equal `after` up to reducible defeq.

That makes a misclassified plumbing head impossible to *ship* as a `rw`:
`rw [propext]` or `rw [Iff.trans]` cannot pass, because `propext`'s statement
does not unify with the subterm being rewritten.  A step that fails is
classified `unresolved:unreplayable_rw:<name>` rather than emitted as a rewrite
a replayer cannot perform.
-/

/-- The statement `name args` proves, as an `Eq` or `Iff` pair, with remaining
implicit and instance arguments left as metavariables to unify. The third
component retains the complete opened telescope, including any explicit
arguments already assigned from `args`, so the validator can close it exactly
as the replayer does. -/
def rwStatement? (o : Origin) (args : Array Expr) (prop? : Option Bool)
    (proj : String := "") : MetaM (Option (Expr × Expr × Array Expr)) := do
  let head? : Option Expr ← match o with
    | .decl declName _ _ =>
      if (← getEnv).find? declName |>.isSome then
        pure (some (← mkConstWithFreshMVarLevels declName))
      else pure none
    | .fvar fvarId =>
      if (← getLCtx).contains fvarId then pure (some (mkFVar fvarId)) else pure none
    -- A `.stx` origin that did not resolve to a local is a user-written term we
    -- cannot reconstruct from the trace alone; a `.other` names no declaration.
    | _ => pure none
  let some head := head? | return none
  -- Apply the recorded projection, so the statement read is the conjunct the
  -- rewrite is actually by: `simp [h.2.1]` with `h : p ∧ q ∧ r` rewrites by
  -- `r`'s sibling, not by the whole conjunction, and validating the unprojected
  -- hypothesis rejects a step that replays perfectly well (REVIEW-9 2).
  let head ←
    if proj.isEmpty then pure head else do
      -- `(h c).1`: the hypothesis is quantified, so its binders must be
      -- instantiated *before* the projection -- `∀ x, P x ∧ Q x` is not a
      -- conjunction until it is applied.  Open them as metavariables, which
      -- the recorded `args` and unification then fix, exactly as for a lemma.
      let (pmvars, pbis, _) ← match o with
        | .fvar _ => forallMetaTelescopeReducing (← inferType head)
        | _ => forallMetaTelescope (← inferType head)
      -- The recorded `args` belong to *this* application (`(h c).1` records
      -- `["c"]`), so assign them to its explicit binders here; the projected
      -- statement below has no binders left for them.
      let mut j := 0
      for mvar in pmvars, bi in pbis do
        if bi == .default then
          if h : j < args.size then
            unless ← isDefEq mvar args[j] do return none
            j := j + 1
      let applied := mkAppN head pmvars
      proj.splitOn "." |>.foldlM (init := applied) fun acc part => do
        match part with
        | "" => pure acc
        | "1" => mkAppM ``And.left #[acc]
        | "2" => mkAppM ``And.right #[acc]
        | _ => pure acc
  -- Open the lemma's whole telescope first: implicits, instances and the
  -- hypotheses of a conditional lemma all become metavariables, exactly as a
  -- replayer's `rw` leaves them for unification and side goals.
  -- **Not** the `Reducing` variant: it whnfs the body, so a Prop-valued lemma's
  -- statement unfolds away from the form simp rewrote (`LeftTotal R` becomes
  -- `∃ b, R a b`, `¬(a ∈ [])` becomes `False`) and no longer matches `before`.
  let (mvars, bis, concl) ← match o with
    | .fvar _ => forallMetaTelescopeReducing (← inferType head)
    | _ => forallMetaTelescope (← inferType head)
  -- Then assign the recorded `args` to the **explicit** positions in order.
  -- `mkAppN head args` would feed them to whatever binder comes first, which is
  -- usually a universe or an implicit, silently producing a different statement
  -- (`if 2 then ?a else ?b` for `ite_cond_eq_true 1 2`).
  -- When a projection consumed the `args` above, the projected statement has
  -- none of its own left to fill.
  let mut i := if proj.isEmpty then 0 else args.size
  -- Assign the recorded `args` to explicit binders, leaving all telescope
  -- metavariables in `mvars` for matching, instance synthesis, side evidence,
  -- and final closure. A lemma can take
  -- an explicit argument that does not occur in its left-hand side -- `dif_pos
  -- (hc : c)` proves the condition, and `dite c t e` mentions `c`, `t` and `e`
  -- but never `hc` -- so unifying the statement with the subterm leaves it
  -- unassigned and a replayer has nothing to write. Retaining the full array
  -- lets the caller apply the same closure check as the replayer (REVIEW-9 2).
  for mvar in mvars, bi in bis do
    if bi == .default then
      if h : i < args.size then
        unless ← isDefEq mvar args[i] do return none
        i := i + 1
  -- More recorded arguments than the lemma has explicit binders: the `args` do
  -- not describe this lemma, so there is nothing to check them against.
  if i < args.size then return none
  let concl ← instantiateMVars concl
  -- The `prop` flag is authoritative when set: simp used this lemma as
  -- `p = True` (or `¬p` as `p = False`) rather than as an equation, and replay
  -- rewrites with `eq_true name` / `eq_false name`.  Checking it first matters
  -- because a Prop-valued lemma's statement can itself unfold to an `Eq`
  -- (`LeftTotal R` is a `∀`-statement about `∃`), which the `eq?` test below
  -- would then read as the rewrite — the wrong pair entirely.
  match prop? with
  | some true => return some (concl, mkConst ``True, mvars)
  | some false =>
    -- `Ne a b` is a *definition* (`a = b → False`), so `not?` returns `none`
    -- on `0 ≠ 1` without unfolding it and the statement becomes `(0 ≠ 1) = False`,
    -- which cannot unify with the recorded `before: "0 = 1"`.  Unfold first, as
    -- the `none` arm below already does, so `a ≠ b` and `¬(a = b)` are treated
    -- the same (REVIEW-8 2).  `Ne` is one of Mathlib's commonest simp shapes.
    if let some p := concl.not? then return some (p, mkConst ``False, mvars)
    let unfolded ← whnfR concl
    if let some p := unfolded.not? then return some (p, mkConst ``False, mvars)
    -- `prop:false` records evidence for `¬ p` (or its `p = False`
    -- conversion), never an arbitrary proof of `p`. Treating an unrelated
    -- proposition proof as `(p, False)` would make e.g. `True.intro` appear to
    -- justify rewriting `True` to `False`.
    return none
  | none =>
    -- Read the statement as written first.  Unfolding is only a fallback, for a
    -- conclusion hidden behind an abbreviation; applying it eagerly rewrites
    -- `p = True` into something that no longer matches the recorded subterm.
    if let some (_, lhs, rhs) := concl.eq? then
      return some (lhs, rhs, mvars)
    if let some (lhs, rhs) := concl.iff? then
      return some (lhs, rhs, mvars)
    let concl ← whnfR concl
    if let some (_, lhs, rhs) := concl.eq? then
      return some (lhs, rhs, mvars)
    if let some (lhs, rhs) := concl.iff? then
      -- `rw` rewrites with an iff through `propext`; both sides are `Prop`.
      return some (lhs, rhs, mvars)
    return none

/-- Read the actual theorem application supplied by a directly authenticated
source argument. Its explicit arguments are already part of `value`; opening
its remaining telescope yields the complete array of arguments that matching,
instance synthesis, side evidence, and final closure must handle. This
expression is validator-only and is never serialized. -/
def rwStatementFromValue? (value : Expr) (prop? : Option Bool) :
    MetaM (Option (Expr × Expr × Array Expr)) := do
  -- Do not let ambient matching fill holes in an incompletely elaborated source
  -- argument. Only an exact elaborated term is suitable as source evidence.
  if ← hasAssignableMVar value then return none
  let (mvars, _, _) ← forallMetaTelescope (← inferType value)
  -- A simp source argument such as `NeZero.ne _` is elaborated into a
  -- telescope-valued rewrite theorem. Its explicit placeholder is abstracted
  -- into the theorem's function type, while simp later matches that parameter
  -- against the selected redex. Inspect the exact source value after applying
  -- those telescope variables; reading its unapplied result type leaves the
  -- source-supplied rewrite as a goal-level metavariable.
  let appliedValue := mkAppN value mvars
  let concl ← instantiateMVars (← inferType appliedValue)
  match prop? with
  | some true =>
    if let some (_, lhs, rhs) := concl.eq? then
      if ← isDefEq rhs (mkConst ``True) then
        return some (lhs, mkConst ``True, mvars)
    return some (concl, mkConst ``True, mvars)
  | some false =>
    -- Proposition rules may already have been converted by `eq_false` at the
    -- authenticated source application boundary. Preserve that exact
    -- equality instead of treating the whole equality proposition as the
    -- proposition to rewrite.
    if let some (_, lhs, rhs) := concl.eq? then
      if ← isDefEq rhs (mkConst ``False) then
        return some (lhs, mkConst ``False, mvars)
    if let some p := concl.not? then return some (p, mkConst ``False, mvars)
    let unfolded ← whnfR concl
    if let some p := unfolded.not? then return some (p, mkConst ``False, mvars)
    -- Match the proposition-proof contract in `elabProposition`: a proof of
    -- an arbitrary proposition cannot justify replacing it by `False`.
    return none
  | none =>
    if let some (_, lhs, rhs) := concl.eq? then return some (lhs, rhs, mvars)
    if let some (lhs, rhs) := concl.iff? then return some (lhs, rhs, mvars)
    let concl ← whnfR concl
    if let some (_, lhs, rhs) := concl.eq? then return some (lhs, rhs, mvars)
    if let some (lhs, rhs) := concl.iff? then return some (lhs, rhs, mvars)
    return none

/-- The origin to *validate* against: a `.stx` names no declaration, so
`rwStatement?` cannot read a statement from it and the step went unchecked
entirely -- which is how `dif_pos`, whose explicit condition proof `rw` cannot
recover, shipped without ever being validated.  The resolved origin is the
constant or local the syntax elaborated to, which is also what `name` now
reports (REVIEW-9 2). -/
def resolvedOrigin (o localO : Origin) : Origin :=
  match o with
  | .stx .. => localO
  | _ => o

/--
Check that a recorded `rw` step is one a replayer can actually perform: `name`
applied to `args` rewrites `before` to `after` in the direction recorded.

Returns `none` on success, or a classified reason.
-/
def checkRwStep (o : Origin) (args : Array Expr) (inv : Bool)
    (prop? : Option Bool) (before after : Expr) (c : EvCtx)
    (sides : Array SideRec) (proj : String) (sourceValue? : Option Expr)
    (localEvidence : Bool := false) :
    MetaM (Option String) :=
  withLCtx c.lctx c.insts do

    let name ← match o with
      | .decl n _ _ => pure n.toString
      -- The *display* name, as `name` and `local` report it; the raw
      -- `_uniq.8929.19` names nothing a reader can act on.
      | .fvar f => pure ((← ppExpr (mkFVar f)).pretty)
      | .stx _ r => pure (r.prettyPrint.pretty.trimAscii.toString)
      | .other n => pure n.toString
    try
      withoutModifyingState do
        if localEvidence then
          match o, sourceValue? with
          | .fvar fvarId, some proof =>
            unless (← getLCtx).contains fvarId && proof.containsFVar fvarId do
              return some s!"unreadable_local_evidence:{name}"
          | _, _ => return some s!"unreadable_local_evidence:{name}"
        let statement? ← match sourceValue? with
          | some value => rwStatementFromValue? value prop?
          | none => rwStatement? o args prop? proj
        let some (lhs, rhs, _) := statement?
          -- No statement to read means the step cannot be verified at all.
          -- Round 7 made an unresolvable *origin* classified; this is the other
          -- half — a resolvable origin whose statement we cannot read — and
          -- leaving it a silent pass is what let `simp [h.mp hp]` ship an
          -- unverified `rw` with the wrong `args` (REVIEW-8 8).
          -- "None" is never a pass.
          | -- A `.stx` origin that stayed unresolved is already reported as
            -- `unresolved:origin` by the recorder; do not double-report it.
            if o matches .stx .. then return none
            else return some s!"unreadable_rw_statement:{name}"
        -- `dir: "rev"` means simp used the equation right-to-left.
        let (src, tgt) := if inv then (rhs, lhs) else (lhs, rhs)
        -- Unify with instances resolvable: the statement's instance arguments
        -- are metavariables here and `before` carries the concrete instance
        -- simp used, which plain `isDefEq` at reducible transparency will not
        -- assign.
        -- simp applies a partially-matching lemma to extra arguments
        -- (`Simp.Result.addExtraArgs`), so the recorded subterm can be the
        -- lemma's LHS applied to more: `curry_uncurry`'s `curry (uncurry ?f)`
        -- against a recorded `curry (uncurry f) a`.  Peel the same number of
        -- trailing arguments off both sides before unifying, exactly as
        -- `tryTheoremCore` does.
        -- Peel only when the lemma's own left-hand side is a *rigid*
        -- application with fewer arguments than the subterm: `curry (uncurry ?f)`
        -- against `curry (uncurry f) a`.  A bare metavariable LHS (`?p`, as in
        -- `eq_true_of_decide : decide p = true → p = True`) matches the whole
        -- subterm, so peeling would strip it down to its head.
        let peel := !src.getAppFn.isMVar && src.getAppNumArgs > 0
          && before.getAppNumArgs > src.getAppNumArgs
        let extra := if peel then before.getAppNumArgs - src.getAppNumArgs else 0
        let extraArgs := before.getAppArgs.extract (before.getAppNumArgs - extra)
                           before.getAppNumArgs
        let beforeCore := if extra == 0 then before else
          mkAppN before.getAppFn (before.getAppArgs.extract 0
            (before.getAppNumArgs - extra))
        -- Unify the rewritten side with `before`, then require the other side
        -- to match `after`.  Instances are resolvable during unification: the
        -- statement's are metavariables here while `before` carries the
        -- concrete one simp used.
        -- Unify **both** sides together rather than left-to-right.  A
        -- higher-order metavariable in the conclusion (a congruence theorem's
        -- `?q'`, the body as a function of the antecedent) is determined by the
        -- *other* side, so committing to `src` first can strand it and reject a
        -- step that replays perfectly well — which is what made
        -- `exists_prop_congr` a false positive (REVIEW-7 2).
        let bothOk ← withReducibleAndInstances do
          if ← isDefEq src beforeCore then
            isDefEq (mkAppN (← instantiateMVars tgt) extraArgs) after
          else pure false
        unless bothOk do
          -- Try the other order before giving up: unifying the result side
          -- first can fix a higher-order mvar that then determines `src`.
          let flipped ← withReducibleAndInstances do
            if ← isDefEq (mkAppN tgt extraArgs) after then
              isDefEq src beforeCore
            else pure false
          unless flipped do
            -- A congruence theorem's higher-order argument (`?q'`, the body as
            -- a function of the antecedent) is determined by the step's `side`
            -- traces, not by its conclusion, so a `rw` carrying `side` entries
            -- is checked against those instead: each side trace is one
            -- hypothesis, and a replayer supplies them in signature order.
            -- Rejecting here would be a false positive on every user
            -- congruence theorem (REVIEW-7 2).
            if !sides.isEmpty then return none
            return some s!"unreplayable_rw:{name}"
          return none
        -- A conditional or higher-order lemma can leave the other side with
        -- metavariables the conclusion alone does not determine (a congruence
        -- theorem's `?q'`); unifying it with `after` is what fixes them, and is
        -- also exactly what a replayer's `rw` does.

        -- An explicit argument the recorded `args` did not supply and
        -- unification did not determine is one a replayer has no way to write:
        -- `dif_pos (hc : c)` takes the condition's proof explicitly, and
        -- `dite c t e` does not mention it, so `rw [dif_pos]` leaves it
        -- unassigned.  Such a step elaborated here but cannot replay, so it is
        -- classified rather than shipped -- unless the step carries `side`
        -- traces, which is exactly how a replayer discharges such an argument
        -- (REVIEW-9 2).
        -- A replayer's `rw [name]` unifies the lemma's *left-hand side* with
        -- the subterm and nothing else, so an explicit argument that the LHS
        -- does not mention stays unassigned for it even though unifying the
        -- other side with `after` determines it here.  `dif_pos (hc : c)` is
        -- exactly that: `dite c t e` mentions `c`, `t` and `e` but never `hc`.
        -- Checking against `after` as well made this validator strictly more
        -- permissive than the tactic it is meant to protect, so the step
        -- shipped and failed at replay with "still has an unassigned
        -- argument". Re-check explicit binders against the LHS alone. Any
        -- remaining proof binders must correspond, in order and by exact type,
        -- to the captured side traces; side presence alone is not evidence.
        -- Proposition steps are replayed by `ExplicitRw.elabProposition`,
        -- which opens the proof's complete telescope and matches the resulting
        -- proposition against the selected redex.  Validate the same contract
        -- below: every binder not supplied in `args` must be fixed by matching
        -- the proposition itself.  An earlier guard rejected every explicit
        -- binder before performing this check; that guard predated quantified
        -- proposition replay and incorrectly classified rules such as
        -- `Std.le_refl`, `exists_apply_eq_apply`, and quantified local evidence.
        let lhsOnly ← withoutModifyingState do
          let statement? ← if localEvidence then
              -- Replay names the local, not the recorder's instantiated proof
              -- snapshot. Validate that the local telescope itself can recover
              -- every explicit binder from the selected rewrite side.
              rwStatement? o args prop? proj
            else match sourceValue? with
              | some value => rwStatementFromValue? value prop?
              | none => rwStatement? o args prop? proj
          let some (l, r, unf) := statement? | pure false
          -- The side `rw` matches against, in the recorded direction. Keep the
          -- match assignments alive through the same instance, side-goal and
          -- final-closure checks that `ExplicitRw.runRwStep` performs. The
          -- enclosing snapshot restores every assignment before validation
          -- returns, so this oracle cannot specialize the caller's mvars.
          let matched := if inv then r else l
          unless ← ExplicitLean.ExplicitRw.matchRewriteSource matched beforeCore do
            return false
          try
            ExplicitLean.ExplicitRw.synthesizeInstanceMVars 0 m!"`{name}`" unf beforeCore
            let proofMVars ← ExplicitLean.ExplicitRw.unassignedRewritePropMVars unf
            if proofMVars.size != sides.size then return false
            for i in [0 : sides.size] do
              let .mvar mid := ← instantiateMVars proofMVars[i]! | return false
              let ty ← instantiateMVars (← mid.getType)
              let side := sides[i]!
              let some close := side.by_ | return false
              if close.startsWith "unresolved:" then return false
              let goal ← instantiateMVars side.goal
              if ← hasAssignableMVar ty then return false
              if ← hasAssignableMVar goal then return false
              let sameType ← withLCtx side.evCtx.lctx side.evCtx.insts do
                isDefEq ty goal
              unless sameType do return false
            let mut sideIds : Array MVarId := #[]
            for m in proofMVars do
              if let .mvar mid := m then sideIds := sideIds.push mid
            let remaining ← unf.filterM fun m => do
              match ← instantiateMVars m with
              | .mvar mid =>
                if ← mid.isAssigned then pure false
                else pure (!sideIds.contains mid)
              | _ => pure false
            ExplicitLean.ExplicitRw.closeLemmaMVars 0 m!"`{name}`" remaining
            pure true
          catch _ => pure false
        unless lhsOnly do
          return some s!"unassigned_explicit_argument:{name}"
        return none
    catch _ =>
      return some s!"unreplayable_rw:{name}"

mutual

/-- Classify one event and all of its nested side/congruence event trees. -/
partial def classifyEventTree (ur : IO.Ref Unresolved) (ev : Event) :
    MetaM ValidationVerdict := do
  match ev with
  | .rw _ o inv prop? b a c args sides _ lo pj derivation? sourceValue? =>
    let sourceKind? := derivation?.bind fun d => d.source?
    let sourceArgId? := derivation?.bind fun d => d.argId?
    let sourceMarked := sourceKind? == some "simp-argument"
    let localEvidenceMarked := sourceKind? == some "local-evidence"
    let sourceError? :=
      if sourceMarked && sourceArgId?.isNone then some "unauthenticated_source_application"
      else if sourceMarked && sourceValue?.isNone then some "missing_source_application"
      else if localEvidenceMarked && sourceValue?.isNone then some "missing_local_evidence"
      else if !sourceMarked && !localEvidenceMarked && sourceValue?.isSome then
        some "untrusted_source_application"
      else none
    let reason? ← match sourceError? with
      | some reason => pure (some reason)
      | none => do
        let value? := if sourceMarked || localEvidenceMarked then sourceValue? else none
        checkRwStep (resolvedOrigin o lo) args inv prop? b a c sides pj value?
          localEvidenceMarked
    if let some reason := reason? then ur.modify (·.add reason)
    let sideVerdicts ← sides.mapM fun sd => classifyEventArray ur sd.events
    return .mk reason? sideVerdicts #[]
  | .eq _ _ _ _ _ sides =>
    let sideVerdicts ← sides.mapM fun sd => classifyEventArray ur sd.events
    return .mk none sideVerdicts #[]
  | .defeq .. => return .mk none #[] #[]
  | .introCtx .. | .introCtxExit .. => return .mk none #[] #[]
  | .congr _ arg nested before _ argBefore argAfter c =>
    let nestedVerdicts ← validateNested ur c arg before nested argBefore argAfter
    return .mk none #[] nestedVerdicts
  | .transport _ _ domain body _ _ domainBefore domainAfter bodyBefore bodyAfter _ =>
    -- Transport children are independent event runs rooted at their captured
    -- domain/body terms. Replay them here (rather than merely classifying their
    -- leaves), so this remains true when the transport is itself nested under
    -- a congruence argument.
    let domainVerdicts ← validate ur domainBefore domainAfter domain
    let bodyVerdicts ← validate ur bodyBefore bodyAfter body
    return .mk none #[] (domainVerdicts ++ bodyVerdicts)

/-- Classify an event array, retaining one verdict per event. -/
partial def classifyEventArray (ur : IO.Ref Unresolved) (events : Array Event) :
    MetaM (Array ValidationVerdict) := do
  let mut out : Array ValidationVerdict := #[]
  for ev in events do
    out := out.push (← classifyEventTree ur ev)
  return out

/- Replay a `congr` step's nested steps against the argument they describe.
Positions are relative to the argument, per the spec. -/
partial def validateNested (ur : IO.Ref Unresolved) (c : EvCtx)
    (arg : Nat) (congrBefore : Expr) (nested : Array Event)
    (argBefore argAfter : Expr) :
    MetaM (Array ValidationVerdict) := do
  let congrArgs := congrBefore.getAppArgs
  unless arg < congrArgs.size && congrArgs[arg]! == argBefore do
    throwError "simp_trace: validation failed: nested congruence root does not match the recorded application argument"
  -- The event paths belong to the exact expression captured by Traversal.
  -- Keep that raw syntax as the navigation/replacement tree: instantiating a
  -- metavariable before following a path can expose a different subtree and
  -- silently invalidate the recorded position.  Instantiate only the
  -- compared expressions below, not the tree that gives positions meaning.
  let mut running := argBefore
  let mut verdicts : Array ValidationVerdict := #[]
  let mut lastStep? : Option (Pos × Expr × Expr) := none
  for ev in nested do
    let verdict ← classifyEventTree ur ev
    verdicts := verdicts.push verdict
    let (pos, before, after, ec) ← match ev with
      | .rw pos _ _ _ b a ec .. => pure (pos, b, a, ec)
      | .eq pos _ b a ec _ => pure (pos, b, a, ec)
      | .defeq pos _ _ b a ec => pure (pos, b, a, ec)
      | .congr pos _ _ b a _ _ ec => pure (pos, b, a, ec)
      | .transport pos _ _ _ b a _ _ _ _ ec => pure (pos, b, a, ec)
      | .introCtx .. | .introCtxExit .. => continue
    let priorSummary := match lastStep? with
      | some (p, b, a) => s!"pos={p}; before={reprStr b}; after={reprStr a}"
      | none => "none"
    let eventKind := match ev with
      | .rw .. => "rw"
      | .eq .. => "eq"
      | .defeq _ kind .. => s!"defeq:{kind.toString}"
      | .congr .. => "congr"
      | .transport .. => "transport"
      | .introCtx .. => "introCtx"
      | .introCtxExit .. => "introCtxExit"
    let some (sub, binderNodes) := navigate? running pos
      | throwError "simp_trace: validation failed: `congr` nested step has no \
          subterm at relative position {pos} ({eventKind})\n  in: {running}\n  running raw: {reprStr running}\n\
          recorded before: {before}\n  before raw: {reprStr before}\n\
          prior event: {priorSummary}"
    let expected ← abstractSimpFVars before ec.binderSpine pos binderNodes
    let sub ← instantiateMVars sub
    let expected ← instantiateMVars expected
    unless (← withLCtx ec.lctx ec.insts (eqUpToProofs sub expected)) do
      throwError "simp_trace: validation failed: `congr` nested subterm at \
        relative {pos} is\n{sub}\nbut the step's `before` is\n{expected}"
    let replacement ← abstractSimpFVars after ec.binderSpine pos binderNodes
    let some next := replaceAt? running pos replacement
      | throwError "simp_trace: validation failed: `congr` nested step cannot \
          replace at relative {pos}"
    running := next
    lastStep? := some (pos, before, after)
  let replayed ← instantiateMVars running
  let argAfter ← instantiateMVars argAfter
  unless (← withLCtx c.lctx c.insts (eqUpToProofs replayed argAfter)) do
    throwError "simp_trace: validation failed: `congr` nested steps do not \
      reach the argument's result\nreplayed: {replayed}\nactual:   {argAfter}"
  return verdicts

/-- Replay `steps` structurally from `pre`, checking every position.

Returns one structured verdict for every event, so classifications can be
attached recursively to the exact rendered step. -/
partial def validate (ur : IO.Ref Unresolved) (pre : Expr) (result : Expr)
    (events : Array Event) : MetaM (Array ValidationVerdict) := do
  -- Instance arguments can still be unassigned metavariables at the moment a
  -- step is recorded and get assigned later in the run, so a recorded subterm
  -- and the running term can differ only by `?m` versus its assignment.  Both
  -- sides are instantiated before every comparison.
  let mut running ← instantiateMVars pre
  let mut verdicts : Array ValidationVerdict := #[]
  for ev in events do
    let verdict ← classifyEventTree ur ev
    verdicts := verdicts.push verdict
    let (pos, before, after, c) ← match ev with
      | .rw pos _ _ _ b a c .. =>
        pure (pos, b, a, c)
      | .eq pos _ b a c _ => pure (pos, b, a, c)
      | .defeq pos _ _ b a c => pure (pos, b, a, c)
      | .congr pos _ _ b a _ _ c =>
        -- Keeping the `congr` kind honest needs both halves checked: the node's
        -- whole before/after is verified below exactly like any other step, and
        -- the nested steps must independently replay the *argument* from
        -- `argBefore` to `argAfter` at positions relative to it.
        pure (pos, b, a, c)
      | .transport pos _ _ _ b a _ _ _ _ c => pure (pos, b, a, c)
      | .introCtx .. | .introCtxExit .. =>
        continue
    -- The traversal observed the subterm with enclosing term binders as free
    -- variables; the running term still has loose bvars there. Each crossed
    -- binder has a path-tagged slot, including non-dependent arrows, so their
    -- ordering is not reconstructed from separate counts.
    let before ← instantiateMVars before
    let after ← instantiateMVars after
    let some (sub, binderNodes) := navigate? running pos
      | throwError "simp_trace: validation failed: no subterm at position {pos}\n\
          in: {running}"
    let expected ← abstractSimpFVars before c.binderSpine pos binderNodes
    unless (← withLCtx c.lctx c.insts (eqUpToProofs sub expected)) do
      -- When the two differ *only* in proof subterms, the step is real and the
      -- positions are right; what the validator cannot confirm is the identity
      -- of a proof simp transported along a rewrite of its own proposition
      -- (`by_cases h : p` leaves the running term with `True` where the
      -- recorded proof still has type `p`).  That is a gap in what we can
      -- check, not a wrong trace, so it is classified rather than fatal —
      -- a hard error here is neither a trace nor a classified outcome, which
      -- is what crashed four stock-provable `Logic/Basic` calls (REVIEW-7 4).
      if ← withLCtx c.lctx c.insts (eqIgnoringProofs sub expected) then
        ur.modify (·.add "transported proof term at a rewritten proposition; \
positions checked, proof identity not")
      else
        throwError "simp_trace: validation failed: subterm at {pos} is\n\
          {sub}\nbut the recorded step's `before` is\n{expected}"
    let replacement ← abstractSimpFVars after c.binderSpine pos binderNodes
    let some next := replaceAt? running pos replacement
      | throwError "simp_trace: validation failed: cannot replace at {pos}"
    running ← instantiateMVars next
  let result ← instantiateMVars result
  unless (← eqUpToProofs running result) do
    throwError "simp_trace: validation failed: replayed term does not match \
      simp's result\nreplayed: {running}\nactual:   {result}"
  return verdicts

end

/-! ### The tactic -/

mutual

partial def attachStep (st : Step) (v : ValidationVerdict) : Step :=
  let side := st.side.mapIdx fun i sd =>
    let nested := v.side.getD i #[]
    { sd with steps := attachSteps sd.steps nested }
  if st.kind == "transport" then
    let all := attachSteps (st.domain ++ st.body) v.nested
    let domain := all.take st.domain.size
    let body := all.extract st.domain.size all.size
    { st with unresolved? := v.reason?, side := side, domain := domain, body := body }
  else
    let nested := if st.kind == "congr" then attachSteps st.steps v.nested else st.steps
    { st with unresolved? := v.reason?, side := side, steps := nested }

partial def attachSteps (steps : Array Step)
    (verdicts : Array ValidationVerdict) : Array Step := Id.run do
  let mut out : Array Step := #[]
  let mut stepIndex := 0
  for v in verdicts do
    if stepIndex < steps.size then
      out := out.push (attachStep steps[stepIndex]! v)
      stepIndex := stepIndex + 1
  return out

end

/-! ### Contextual scope assembly

`intro_ctx` enter/exit events are recorder-internal delimiters.  The consumer
needs the enclosed events as the scoped step list required by T33, so assemble
that structure before converting events to wire steps.  Keeping this at the
recorder boundary is important: the finalizer intentionally copies locations
verbatim and must not infer scope from invocation files or display names. -/

partial def scopedEvents (events : Array Event) (start : Nat) (scopeId : Nat) :
    Array Event × Nat := Id.run do
  let mut body : Array Event := #[]
  let mut i := start
  while h : i < events.size do
    match events[i] with
    | .introCtxExit _ info =>
      if info.scope.id == scopeId then
        return (body, i + 1)
      body := body.push events[i]
      i := i + 1
    | ev =>
      body := body.push ev
      i := i + 1
  return (body, i)

partial def eventsToSteps (ur : IO.Ref Unresolved)
    (contextualFVars : Array (FVarId × Nat))
    (events : Array Event) : MetaM (Array Step) := do
  let mut out : Array Step := #[]
  let mut i := 0
  while h : i < events.size do
    match events[i] with
    | .introCtx pos fvar ctx info =>
      let (body, next) := scopedEvents events (i + 1) info.scope.id
      let step? ← eventToStep ur contextualFVars events[i]
      if let some base := step? then
        -- T33's inner list is rooted at the introduced arrow body, i.e. the
        -- forall node's body child, not at the enclosing source location.
        -- Recorder events retain absolute positions for the outer validator;
        -- strip that body prefix only when moving them into the scoped list.
        let bodyRoot := info.scope.enter.push 1
        let nested ← eventsToSteps ur contextualFVars
          (body.map (Event.strip bodyRoot))
        out := out.push { base with steps := nested }
      i := next
    | .introCtxExit .. =>
      -- A malformed/unpaired exit is not a source-facing step.  The enclosing
      -- validator still owns the event stream; dropping this delimiter cannot
      -- invent a replay action.
      i := i + 1
    | ev =>
      if let some step ← eventToStep ur contextualFVars ev then
        out := out.push step
      i := i + 1
  return out

/-- Turn one traced run into a `LocationTrace`. -/
def buildLocation (ur : IO.Ref Unresolved)
    (hyp? : Option String) (pre : Expr) (result : Simp.Result)
    (events : Array Event) (closed : Bool)
    (absurdHyp? : Option String := none) : MetaM LocationTrace := do
  let verdicts ← validate ur pre result.expr events
  -- Hypotheses `+contextual` introduced, so their references land in the
  -- spec's separate `contextual` namespace.  Preserve the operational handle
  -- alongside the fvar identity: side traces often carry the local reference
  -- after the intro event itself, and a display name is not a stable join key.
  let contextualFVars : Array (FVarId × Nat) := events.filterMap fun ev =>
    match ev with
    | .introCtx _ fid _ info => some (fid, info.handle)
    | _ => none
  let rawSteps ← eventsToSteps ur contextualFVars events
  let steps := attachSteps rawSteps verdicts
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
    let txt := if txt.endsWith ")" then txt.dropEnd 1 |>.toString else txt
    match txt.splitOn ":=" with
    | _ :: rest => some ((String.intercalate ":=" rest).trimAscii.toString)
    | [] => some txt.trimAscii.toString

@[tactic simpTrace]
def evalSimpTrace : Tactic := fun stx => withMainContext do
  let simpStx := toSimpSyntax stx
  let sourceArgs ← registerSourceArgs stx
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
          runTraced type hctx simprocs discharge? dtext? stats sourceArgs
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
            runTraced target ctx simprocs discharge? dtext? stats sourceArgs
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
    sourceArgs := sourceArgs
    locations := ← locsRef.get }
  let json := trace.toJson
  match outPath? stx with
  | some path =>
    -- A single *syntactic* site can run many times -- `by_cases h : P <;>
    -- simp_trace ...` runs it once per branch, on a different goal each time,
    -- with a different hypothesis of the same name in scope.  Writing them all
    -- to one path let the last branch silently overwrite the others, so the
    -- surviving trace named `h` while replay applied it to every branch, where
    -- `h : P` in some and `h : ¬P` in others.  Give each run after the first
    -- its own `.<n>.json`, so no invocation is lost (REVIEW-9 1).
    let base ← resolveOutPath path
    let mut target := base
    let mut n := 1
    let mut placed := false
    while !placed do
      if !(← target.pathExists) then
        placed := true
      else if (← IO.FS.readFile target) == json then
        -- Lean can elaborate a declaration more than once; an identical trace
        -- is that same invocation seen again, not another goal.  Overwrite it,
        -- or the file count drifts between identical runs.
        placed := true
      else
        let stem := base.toString.dropRight ".json".length
        target := System.FilePath.mk s!"{stem}.{n}.json"
        n := n + 1
    IO.FS.writeFile target json
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
