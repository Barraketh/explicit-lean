/-
Trace data model for `simp_trace`, mirroring `tracking/SIMP-TRACE-SPEC.md`
(schema `simp-trace-v1`).

This module is recorder machinery, not product code: it names `Lean.Meta.Simp`
types on purpose.  Nothing here is imported by translated Mathlib source.
-/

module

public meta import Lean
public meta import Lean.Meta.AbstractMVars

public meta section

namespace ExplicitLean.SimpTrace

open Lean
open Lean.Meta

/-- A position is a list of child indices from the root of the location, using
the `SubExpr.Pos` child convention described in the spec.  We keep the explicit
array rather than a packed `SubExpr.Pos` because the spec's wire form is the
array and because packed positions cap the coordinate at `maxChildren`. -/
abbrev Pos := Array Nat

/-- One crossed binder node in the traversal's exact positional spine.

`dummy` denotes a non-dependent binder (an arrow) which shifts de Bruijn
indices but introduces no term variable. `fvar` records the free variable used
when a dependent binder was opened. `bodyPos` is the path to that binder's
body, allowing events emitted at a rebuilt ancestor to select only the binders
actually crossed by their position. -/
inductive BinderSlot where
  | fvar (bodyPos : Pos) (id : FVarId)
  | dummy (bodyPos : Pos)
  deriving Inhabited, Repr, BEq

/-- A reference to a local hypothesis, per the amended spec. -/
inductive LocalRef where
  /-- An ordinary local: its user name, whether that name is inaccessible, and
  its `LocalDecl.index` in the local context at the point of use.

  Per the spec, `ctxIndex` **identifies the declaration; it is not a `rename_i`
  argument.** It counts every declaration from the front of the context,
  including ones the user never sees (the auxiliary recursion declaration,
  section variables), whereas `rename_i` names the *trailing* inaccessible
  hypotheses right to left. A generator derives `rename_i` names from the order
  of inaccessible declarations in the context; the `name` field's
  pretty-printed form (`a✝¹`) already carries that right-to-left rank. -/
  | ordinary (userName : String) (inaccessible : Bool) (ctxIndex : Nat)
  /-- A hypothesis introduced by contextual simp, in its own namespace. -/
  | contextual (ctxIndex : Nat) (handle : Nat)
  deriving Inhabited, Repr

/-- How a location (goal or hypothesis) was closed, if it was. -/
structure CloseInfo where
  /-- `rfl`, `true_intro`, `assumption:<name>`, `absurd:<hyp>`, `decide`, or —
  for a side condition — `omega` or a classified `unresolved:<text>`. -/
  by_ : String
  deriving Inhabited, Repr

/-! ### Operational theorem derivations

These records deliberately contain only replay provenance.  In particular they
do not contain the matcher assignment, a proof expression, or any other term
payload.  The replayer repeats matching at `redex`.
-/

structure BinderDerivation where
  id : Nat
  classification : String
  deriving Inhabited, Repr

structure DischargeDerivation where
  binder : Nat
  provenance : String
  deriving Inhabited, Repr

/-! ### Contextual-introduction handles

`intro_ctx` introduces a local that has no source-level name.  A pretty-printed
inaccessible name (for example `a✝`) is not a replay identity: it can be
reused by a later binder and changes when surrounding binders are renamed.
The recorder therefore carries an operational reference only.  The handle is
allocated in traversal order for one traced call; the domain is identified by
the arrow-domain position and the local declaration indices it depends on.
No type, proof, or expression is serialized here. -/

structure IntroDomainRef where
  position : Pos
  dependencies : Array Nat := #[]
  deriving Inhabited, Repr

structure IntroScope where
  id : Nat
  owner : String
  enter : Pos
  exit : Pos
  deriving Inhabited, Repr

structure IntroCtxInfo where
  handle : Nat
  operation : String
  domain : IntroDomainRef
  scope : IntroScope
  deriving Inhabited, Repr

/-! ### Direct source-argument identity

The source argument is registered once, before stock simp elaboration.  The
metadata below is deliberately not an elaborated term: `head?` is only the
declaration/local identity observed at registration time.  `startChar` and
`endChar` are Unicode-scalar source positions (end exclusive); the internal
byte range is retained only for joining `Origin.stx`, so repeated argument text
remains distinguishable. -/
structure SourceTermValue where
  /-- Universe parameters replacing elaborator metavariables at capture time. -/
  levelParams : Array Name
  /-- Number of elaborator metavariables abstracted into `expr`'s lambda. -/
  numMVars : Nat
  /-- A lambda-abstracted elaboration of the exact parser term. -/
  expr : Expr
  deriving Inhabited, Repr

namespace SourceTermValue

/-- Abstract the term-local expression and universe metavariables, rejecting
anything owned by an enclosing elaboration context. -/
def capture? (value : Expr) : MetaM (Option SourceTermValue) := do
  let abstracted ← abstractMVars value
  if abstracted.expr.hasExprMVar || abstracted.expr.hasLevelMVar then
    return none
  return some {
    levelParams := abstracted.paramNames
    numMVars := abstracted.mvars.size
    expr := abstracted.expr
  }

/-- Reopen an exact source-term snapshot with fresh metavariables in the
current validation context. The captured expression itself contains no
metavariable IDs, so it is safe to retain across temporary MetaM contexts. -/
def instantiate (snapshot : SourceTermValue) : MetaM Expr := do
  let levels ← snapshot.levelParams.mapM fun _ => mkFreshLevelMVar
  let expr := snapshot.expr.instantiateLevelParamsArray snapshot.levelParams levels
  let (_, _, value) ← lambdaMetaTelescope expr (some snapshot.numMVars)
  return value

end SourceTermValue

structure SourceArg where
  argId      : Nat
  startChar  : Nat
  endChar    : Nat
  direction  : String
  kind       : String
  head?      : Option String := none
  /-- Internal elaborated identity; omitted by the wire representation. -/
  headName?  : Option Name := none
  headLocal  : Bool := false
  /-- Exact parser-term elaboration, with its temporary metavariables
  abstracted; validation-only and omitted by the wire representation. -/
  termValue? : Option SourceTermValue := none
  /-- Parser byte range used only for the in-memory `Origin.stx` join. -/
  startByte  : Nat := 0
  endByte    : Nat := 0
  deriving Inhabited, Repr

/-! A deliberately small, term-free recipe for the two common conditional
simprocs.  The selected theorem is named by the rendered `rw` step; this
record carries only the operational facts needed to audit that selection. -/
structure SimprocDerivation where
  source : String
  redex : Pos
  extraArgs : Nat
  branch : String
  constructor : String
  deriving Inhabited, Repr

structure RuleDerivation where
  origin : String
  source? : Option String := none
  /-- Direct site-local identity of the source argument that registered this
  theorem.  This is never inferred from theorem-table order. -/
  argId? : Option Nat := none
  /-- Direction written at the source argument, when this is a source rule. -/
  direction? : Option String := none
  preprocess : Array String := #[]
  redex : Pos := #[]
  extraArgs : Nat := 0
  binders : Array BinderDerivation := #[]
  discharge : Array DischargeDerivation := #[]
  simproc? : Option SimprocDerivation := none
  deriving Inhabited, Repr

mutual

/-- A recorded step.  `kind` discriminates; unused fields stay `none`/empty. -/
structure Step where
  kind    : String
  pos     : Pos
  /-- Lemma, hypothesis or constant name (`rw`, `unfold`, `intro_ctx`). -/
  name?   : Option String := none
  /-- `"fwd"` or `"rev"` for `rw`. -/
  dir?    : Option String := none
  /-- The amended spec's `prop` flag: `"true"` when the named lemma is
  Prop-valued and simp used it as `P = True`, `"false"` when as `P = False`.
  Absent when the lemma really is an equation or an iff.  Replay rewrites with
  `eq_true name` / `eq_false name` respectively. -/
  prop?   : Option String := none
  /-- For a local-hypothesis reference: the spec's `local` object.  Either an
  ordinary local (`userName`/`inaccessible`/`ctxIndex`) or a hypothesis
  introduced by contextual simp (`contextual`/`ctxIndex`).  The two namespaces
  never collide, so an inaccessible hypothesis is replayable (a generator names
  it with `rename_i`) and can never be mistaken for a contextual label. -/
  local?  : Option LocalRef := none
  /-- Explicit argument terms needed for replay. -/
  args    : Array String := #[]
  /-- `eq` steps: the computed equation and how replay should prove it. -/
  lhs?    : Option String := none
  rhs?    : Option String := none
  by_?    : Option String := none
  source? : Option String := none
  /-- `change` steps: an ordinary Lean surface term, elaborated in the
  captured context. -/
  to?     : Option String := none
  /-- `congr` steps: which argument of the application was rewritten. -/
  arg?    : Option Nat := none
  /-- `congr` steps: the nested steps, with positions relative to `arg`. -/
  steps   : Array Step := #[]
  /-- `transport` steps: the stable handle of the binder introduced while
  simplifying the dependent body.  The handle is local to this trace call and
  is never recovered from a printed name. -/
  handle? : Option Nat := none
  /-- `transport` steps: domain steps are rooted at the forall's domain. -/
  domain  : Array Step := #[]
  /-- `transport` steps: body steps are rooted at the forall's body, with the
  introduced binder available through `introduced_ref handle`. -/
  body    : Array Step := #[]
  /-- Operational identity for a contextual binder introduction.  This is
  deliberately separate from `name`: no inaccessible display name is needed
  to replay an `introduced_ref`. -/
  intro?  : Option IntroCtxInfo := none
  before? : Option String := none
  after?  : Option String := none
  /-- Side-condition sub-traces, one per discharged hypothesis. -/
  side    : Array SideTrace := #[]
  /-- Event-time theorem construction provenance.  This is intentionally
  term-free; it is an operational recipe, not a serialized proof. -/
  derivation? : Option RuleDerivation := none
  /-- Set when the in-tactic validator classified *this step*: the step is
  recorded as observed, but a consumer must not replay it.  The classification
  used to exist only as a compile-time `logError`, invisible to anything
  reading the JSON, so a renderer emitted the step anyway and it failed at
  replay (REVIEW-9 2). -/
  unresolved? : Option String := none

/-- A side-condition sub-trace: the same `steps`/`close` shape as a location. -/
structure SideTrace where
  goal  : String
  /-- Like a location, the side goal before and after its steps; `post?` is
  `none` when the side goal was closed (spec e95c745). -/
  pre   : String := ""
  post? : Option String := none
  steps : Array Step := #[]
  close : Option CloseInfo := none
  /-- Antecedents introduced before the steps, for an implication-shaped
  congruence hypothesis (`c → x = u`); spec 2e73661.  Empty otherwise. -/
  intros : Array String := #[]

end

instance : Inhabited Step := ⟨{ kind := "", pos := #[] }⟩
instance : Inhabited SideTrace := ⟨{ goal := "" }⟩

/-- One simplified location: the goal or a named hypothesis. -/
structure LocationTrace where
  /-- `none` means the goal; `some n` means hypothesis `n`. -/
  hyp?  : Option String
  pre   : String
  /-- `none` when the location was closed. -/
  post? : Option String
  steps : Array Step := #[]
  close : Option CloseInfo := none
  deriving Inhabited

/-- One executed `simp_trace` call. -/
structure CallTrace where
  module     : String
  occurrence : String
  call       : String
  /-- Source arguments registered for this exact call. -/
  sourceArgs : Array SourceArg := #[]
  locations  : Array LocationTrace := #[]
  deriving Inhabited

/-! ## JSON rendering

We emit JSON by hand so the shape matches the spec exactly (optional keys are
omitted rather than emitted as `null`, except where the spec asks for `null`).
-/

/-- Escape a string for JSON. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        let hex := String.ofList (Nat.toDigits 16 c.toNat)
        acc ++ "\\u" ++ "".pushn '0' (4 - hex.length) ++ hex
      else acc ++ c.toString

def str (s : String) : String := "\"" ++ escape s ++ "\""

def strArray (xs : Array String) : String :=
  "[" ++ String.intercalate "," (xs.toList.map str) ++ "]"

def posJson (p : Pos) : String :=
  "[" ++ String.intercalate "," (p.toList.map toString) ++ "]"

def IntroDomainRef.toJson (d : IntroDomainRef) : String :=
  "{\"position\":" ++ posJson d.position ++
    ",\"dependencies\":[" ++ String.intercalate "," (d.dependencies.toList.map toString) ++ "]}"

def IntroScope.toJson (s : IntroScope) : String :=
  "{\"id\":" ++ toString s.id ++ ",\"owner\":" ++ str s.owner ++
    ",\"enter\":" ++ posJson s.enter ++ ",\"exit\":" ++ posJson s.exit ++ "}"

def IntroCtxInfo.toJson (i : IntroCtxInfo) : String :=
  "{\"handle\":" ++ toString i.handle ++ ",\"operation\":" ++ str i.operation ++
    ",\"domain\":" ++ i.domain.toJson ++ ",\"scope\":" ++ i.scope.toJson ++ "}"

/-- Join the non-empty field renderings into an object. -/
private def obj (fields : Array (String × Option String)) : String :=
  let parts := fields.filterMap fun (k, v?) => v?.map fun v => str k ++ ":" ++ v
  "{" ++ String.intercalate "," parts.toList ++ "}"

def LocalRef.toJson : LocalRef → String
  | .ordinary userName inaccessible ctxIndex =>
    "{\"userName\":" ++ str userName ++
    ",\"inaccessible\":" ++ (if inaccessible then "true" else "false") ++
    ",\"ctxIndex\":" ++ toString ctxIndex ++ "}"
  | .contextual ctxIndex handle =>
    "{\"contextual\":true,\"ctxIndex\":" ++ toString ctxIndex ++
    ",\"handle\":" ++ toString handle ++ "}"

def CloseInfo.toJson (c : CloseInfo) : String :=
  obj #[("by", some (str c.by_))]

def BinderDerivation.toJson (b : BinderDerivation) : String :=
  obj #[ ("id", some (toString b.id)), ("classification", some (str b.classification)) ]

def DischargeDerivation.toJson (d : DischargeDerivation) : String :=
  obj #[ ("binder", some (toString d.binder)), ("provenance", some (str d.provenance)) ]

def SimprocDerivation.toJson (d : SimprocDerivation) : String :=
  obj #[ ("source", some (str d.source)), ("redex", some (posJson d.redex)),
    ("extraArgs", some (toString d.extraArgs)), ("branch", some (str d.branch)),
    ("constructor", some (str d.constructor)) ]

def RuleDerivation.toJson (d : RuleDerivation) : String :=
  obj #[
    ("origin", some (str d.origin)),
    ("source", d.source?.map str),
    ("argId", d.argId?.map toString),
    ("direction", d.direction?.map str),
    ("preprocess", if d.preprocess.isEmpty then none else some (strArray d.preprocess)),
    ("redex", some (posJson d.redex)),
    ("extraArgs", some (toString d.extraArgs)),
    ("binders", if d.binders.isEmpty then none else
      some ("[" ++ String.intercalate "," (d.binders.toList.map BinderDerivation.toJson) ++ "]")),
    ("discharge", if d.discharge.isEmpty then none else
      some ("[" ++ String.intercalate "," (d.discharge.toList.map DischargeDerivation.toJson) ++ "]")),
    ("simproc", d.simproc?.map SimprocDerivation.toJson)]

mutual

partial def Step.toJson (s : Step) : String :=
  let sourceBacked := match s.derivation? with
    | some derivation => derivation.source? == some "simp-argument"
    | none => false
  obj #[
    ("kind", some (str s.kind)),
    ("pos", some (posJson s.pos)),
    ("name", s.name?.map str),
    ("dir", s.dir?.map str),
    ("prop", s.prop?.map str),
    ("local", s.local?.map LocalRef.toJson),
    -- A source-backed step is replayed from its exact `sourceArgs` span, not
    -- from printer-reconstructed expressions. Keep recorder-side validation
    -- arguments internal so a hidden/discharger-supplied proof cannot look
    -- like part of the user's source spelling.
    ("args", if sourceBacked || s.args.isEmpty then none else some (strArray s.args)),
    ("lhs", s.lhs?.map str),
    ("rhs", s.rhs?.map str),
    ("by", s.by_?.map str),
    ("source", s.source?.map str),
    ("to", s.to?.map str),
    ("arg", s.arg?.map toString),
    ("steps", if s.kind != "congr" && s.kind != "intro_ctx" then none else
      some ("[" ++ String.intercalate ","
        (s.steps.toList.map Step.toJson) ++ "]")),
    ("handle", if s.kind != "transport" then none else s.handle?.map toString),
    ("domain", if s.kind != "transport" then none else
      some ("[" ++ String.intercalate ","
        (s.domain.toList.map Step.toJson) ++ "]")),
    ("body", if s.kind != "transport" then none else
      some ("[" ++ String.intercalate ","
        (s.body.toList.map Step.toJson) ++ "]")),
    ("intro", s.intro?.map IntroCtxInfo.toJson),
    ("before", s.before?.map str),
    ("after", s.after?.map str),
    ("side", if s.side.isEmpty then none else
      some ("[" ++ String.intercalate ","
        (s.side.toList.map SideTrace.toJson) ++ "]")),
    ("derivation", s.derivation?.map RuleDerivation.toJson),
    ("unresolved", s.unresolved?.map str)]

partial def SideTrace.toJson (t : SideTrace) : String :=
  obj #[
    ("goal", some (str t.goal)),
    ("pre", some (str t.pre)),
    ("post", some (match t.post? with | none => "null" | some p => str p)),
    ("intros", if t.intros.isEmpty then none else some (strArray t.intros)),
    ("steps", some ("[" ++ String.intercalate ","
      (t.steps.toList.map Step.toJson) ++ "]")),
    ("close", some (match t.close with
      | none => "null"
      | some c => c.toJson))]

end

def LocationTrace.toJson (l : LocationTrace) : String :=
  obj #[
    ("loc", some (match l.hyp? with
      | none => str "goal"
      | some n => "{" ++ str "hyp" ++ ":" ++ str n ++ "}")),
    ("pre", some (str l.pre)),
    ("post", some (match l.post? with
      | none => "null"
      | some p => str p)),
    ("steps", some ("[" ++ String.intercalate ","
      (l.steps.toList.map Step.toJson) ++ "]")),
    ("close", some (match l.close with
      | none => "null"
      | some c => c.toJson))]

def CallTrace.toJson (t : CallTrace) : String :=
  obj #[
    ("schema", some (str "simp-trace-v1")),
    ("module", some (str t.module)),
    ("occurrence", some (str t.occurrence)),
    ("call", some (str t.call)),
    ("sourceArgs", some ("[" ++ String.intercalate ","
      (t.sourceArgs.toList.map fun a => obj #[
        ("argId", some (toString a.argId)),
        ("startChar", some (toString a.startChar)),
        ("endChar", some (toString a.endChar)),
        ("direction", some (str a.direction)),
        ("kind", some (str a.kind)),
        ("head", a.head?.map str)]) ++ "]")),
    ("locations", some ("[" ++ String.intercalate ","
      (t.locations.toList.map LocationTrace.toJson) ++ "]"))]

end ExplicitLean.SimpTrace
