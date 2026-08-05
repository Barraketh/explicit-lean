import ExplicitLean.Capture

/-!
# v0 admission

Decides whether a captured module is inside the v0 source feature set, and
produces a structured unsupported diagnostic when it is not.

An unsupported construct is a normal diagnosed result. It must not fall through
to an approximate lowering, so admission runs before lowering depends on
anything it checks.

Three levels are checked:

- which commands a module may contain;
- which declaration kinds and modifiers are accepted; and
- which completed expression forms may appear in an accepted declaration's type
  and value.
-/

open Lean

namespace ExplicitLean

/-- The v0 source feature set identifier, recorded in the manifest
`configuration` as `sourceFeatureSet`. -/
def sourceFeatureSet : String := "v0"

private def unsupported (code message : String) (range : Option (Nat × Nat))
    (file : String) : Diagnostic :=
  { code, message, phase := .admission
    span := match range with
      | some (s, e) => some { file, startByte := s, endByte := e }
      | none => none }

/-! ## Commands -/

/-- Command syntax kinds v0 accepts.

These are the commands needed to elaborate accepted declarations: namespace and
section structure, the context commands that shape name resolution and
declaration headers, and the one permitted option. `declaration` covers the
declaration commands, whose individual kinds are checked separately. -/
def acceptedCommandKinds : Array Name := #[
  ``Parser.Command.declaration,
  ``Parser.Command.namespace,
  ``Parser.Command.section,
  ``Parser.Command.«end»,
  ``Parser.Command.open,
  ``Parser.Command.variable,
  ``Parser.Command.universe,
  ``Parser.Command.set_option,
  -- `open ... in <decl>` and similar scoped-prefix forms.
  ``Parser.Command.in,
  -- The end-of-input marker the frontend appends; it is not source syntax.
  ``Parser.Command.eoi
]

/-- The only `set_option` v0 accepts is the `autoImplicit` guard.

Any other option can change how the source elaborates, and v0 makes no claim to
reproduce that choice in generated output. -/
private def checkSetOption (stx : Syntax) : Bool := Id.run do
  -- `set_option ident value ...`: the option name is the first identifier.
  for arg in stx.getArgs do
    if arg.isIdent then
      return arg.getId == `autoImplicit
  return false

/-! ### Rejected source syntax

Several rejected constructs elaborate to completed terms that are
indistinguishable from accepted ones. A tactic proof produces the same kind of
proof term a term-style proof does, and `do` notation produces ordinary monadic
applications. Nothing in the completed expression records that a tactic or `do`
block produced it, so these can only be rejected from the source syntax.

v0 also does not rerun the source mechanism in generated output, so admitting
one of these would mean claiming that a term the compiler cannot reconstruct
from source structure is nevertheless faithfully reproduced. -/

/-- Syntax kinds that reject a declaration wherever they appear inside it, with
the reason code and description used to report them. -/
def rejectedSyntaxKinds : Array (Name × String × String) := #[
  (``Parser.Term.byTactic, "UNSUPPORTED-TACTIC-BLOCK", "a tactic block"),
  (``Parser.Term.match, "UNSUPPORTED-MATCH", "a match expression"),
  (``Parser.Term.nomatch, "UNSUPPORTED-MATCH", "a nomatch expression"),
  -- The alternatives of a pattern-matching lambda. Rejecting `matchAlts` rather
  -- than `fun` is what distinguishes `fun | 0 => a | _ => b` from the ordinary
  -- `fun x => e`, which is accepted and parses as the same `fun` kind with a
  -- `basicFun` body.
  (``Parser.Term.matchAlts, "UNSUPPORTED-MATCH", "a pattern-matching lambda"),
  (``Parser.Term.do, "UNSUPPORTED-DO-NOTATION", "do notation"),
  (``Parser.Term.letrec, "UNSUPPORTED-LET-REC", "a let rec binding"),
  (``Parser.Command.declValEqns, "UNSUPPORTED-EQUATION-DECLARATION",
    "an equation-style declaration body"),
  (``Parser.Term.whereDecls, "UNSUPPORTED-WHERE", "a where clause"),
  -- v0 accepts public declarations only. `private` and `protected` change the
  -- name a reference must use, which G1 handles through separate exceptions
  -- that v0 does not implement. The enclosing `visibility` parser does not
  -- appear as a node kind, so these two are the ones that match.
  (``Parser.Command.«protected», "UNSUPPORTED-VISIBILITY",
    "a protected declaration"),
  (``Parser.Command.«private», "UNSUPPORTED-VISIBILITY", "a private declaration"),
  (``Parser.Term.sorry, "UNSUPPORTED-SORRY", "sorry"),
  (``Parser.Term.attributes, "UNSUPPORTED-ATTRIBUTE", "a declaration attribute"),
  -- Modifiers outside grammar version 1.
  (``Parser.Command.«unsafe», "UNSUPPORTED-MODIFIER", "an unsafe declaration"),
  (``Parser.Command.«partial», "UNSUPPORTED-MODIFIER", "a partial declaration"),
  (``Parser.Command.«noncomputable», "UNSUPPORTED-MODIFIER",
    "a noncomputable declaration"),
  (``Parser.Command.«nonrec», "UNSUPPORTED-MODIFIER", "a nonrec declaration"),
  -- One derived class. The enclosing `optDeriving` node is present even when no
  -- deriving clause was written, so rejecting that instead would reject every
  -- inductive-like declaration for the wrong reason.
  (``Parser.Command.derivingClass, "UNSUPPORTED-DERIVING", "a deriving clause"),
  (``Parser.Command.docComment, "UNSUPPORTED-DOC-COMMENT",
    "a documentation comment")
]

/-- Walk a syntax tree looking for a rejected kind.

Returns the first rejection in a left-to-right traversal, with the range of the
offending node so the diagnostic points at the construct rather than the whole
declaration. -/
partial def findRejectedSyntax (stx : Syntax) :
    Option (String × String × Option (Nat × Nat)) :=
  let kind := stx.getKind
  match rejectedSyntaxKinds.find? fun (k, _, _) => k == kind with
  | some (_, code, description) => some (code, description, syntaxRange stx)
  | none => stx.getArgs.findSome? findRejectedSyntax

/-- Check that every captured command is one v0 accepts, and that no accepted
command contains rejected syntax. -/
def checkCommands (path : String) (m : CapturedModule) : Array Diagnostic := Id.run do
  let mut ds : Array Diagnostic := #[]
  for cmd in m.commands do
    let kind := cmd.stx.getKind
    if !acceptedCommandKinds.contains kind then
      ds := ds.push (unsupported "UNSUPPORTED-COMMAND"
        s!"command '{kind}' is not in the v0 source feature set"
        cmd.range path)
    else if kind == ``Parser.Command.set_option && !checkSetOption cmd.stx then
      ds := ds.push (unsupported "UNSUPPORTED-SET-OPTION"
        "the only option v0 accepts is 'set_option autoImplicit false'"
        cmd.range path)
    else if let some (code, description, range) := findRejectedSyntax cmd.stx then
      ds := ds.push (unsupported code
        s!"{description} is not in the v0 source feature set"
        (range.orElse fun _ => cmd.range) path)
  return ds

/-! ## Declarations -/

/-- Is this constant one of the declaration kinds v0 accepts?

v0 accepts `def`, `abbrev`, and `opaque` (all `definition` or `opaque` in the
environment) and `theorem`. `abbrev` is a `definition` with reducible hints, so
the environment does not distinguish it here; the declaration command does. -/
def acceptedDeclarationKind : ConstantInfo → Bool
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

/-- Human-readable name of a rejected declaration kind, with its article, for
the diagnostic. -/
private def kindName : ConstantInfo → String
  | .axiomInfo _ => "an axiom"
  | .defnInfo _ => "a definition"
  | .thmInfo _ => "a theorem"
  | .opaqueInfo _ => "an opaque declaration"
  | .quotInfo _ => "a quotient primitive"
  | .inductInfo _ => "an inductive type"
  | .ctorInfo _ => "a constructor"
  | .recInfo _ => "a recursor"

/-! ## Completed expressions

Every accepted completed term must be closed relative to its declaration
telescope, contain no metavariable, and be printable using the non-matching
productions of G8 with G9 and G10, without reconstructing source-only
structure. -/

/-- Why a completed expression is outside the v0 accepted set.

Only two rejections are reachable. Every other `Expr` constructor is either
accepted outright or, like a matcher application, rejected by a declaration-level
check instead: both `Expr.lit` cases are exactly the literals G10 permits, and a
`let rec` reaches the environment as a separate generated constant rather than as
a self-referential `letE`. -/
inductive TermRejection where
  /-- A metavariable survived instantiation. Capture already rejects this;
  admission checks it again because lowering depends on it. -/
  | metavariable
  /-- A free variable not bound by the declaration telescope. -/
  | looseFreeVariable
  deriving Repr, BEq, DecidableEq

def TermRejection.code : TermRejection → String
  | .metavariable => "UNSUPPORTED-METAVARIABLE"
  | .looseFreeVariable => "UNSUPPORTED-LOOSE-FREE-VARIABLE"

def TermRejection.describe : TermRejection → String
  | .metavariable => "an unresolved metavariable"
  | .looseFreeVariable => "a free variable outside the declaration telescope"

/-- Check a completed expression against the accepted term forms.

Sorts, bound variables, constants with universe instantiation, application,
`forall`, lambda, nonrecursive `let`, projections, metadata, and the two
primitive literals are accepted. Every constructor is listed rather than matched
with a wildcard, so adding an `Expr` constructor to the language is a build
error here rather than a silently accepted term. -/
partial def checkTerm (e : Expr) : Option TermRejection :=
  go e
where
  go (e : Expr) : Option TermRejection :=
    match e with
    | .mvar _ => some .metavariable
    | .fvar _ => some .looseFreeVariable
    | .bvar _ => none
    | .sort _ => none
    | .const _ _ => none
    | .lit (.natVal _) => none
    | .lit (.strVal _) => none
    | .app f a => go f |>.orElse fun _ => go a
    | .lam _ t b _ => go t |>.orElse fun _ => go b
    | .forallE _ t b _ => go t |>.orElse fun _ => go b
    | .letE _ t v b _ => go t |>.orElse fun _ => go v |>.orElse fun _ => go b
    | .mdata _ b => go b
    | .proj _ _ b => go b

/-- Check a declaration's type and value against the accepted term forms.

An expression is checked after the frontend has instantiated it, so a surviving
metavariable is a defect rather than a pending elaboration. Free variables are
rejected because a completed `ConstantInfo` closes over its telescope with bound
variables; an `fvar` here means the expression escaped its local context. -/
def checkDeclarationTerms (path : String) (d : CapturedDeclaration) :
    Array Diagnostic := Id.run do
  let mut ds : Array Diagnostic := #[]
  if let some r := checkTerm d.info.type then
    ds := ds.push (unsupported r.code
      s!"the type of '{d.name}' contains {r.describe}" none path)
  if let some v := d.value? then
    if let some r := checkTerm v then
      ds := ds.push (unsupported r.code
        s!"the value of '{d.name}' contains {r.describe}" none path)
  return ds

/-! ## Declaration admission -/

/-- Does this definition refer to itself?

v0 accepts only nonrecursive, nonmutual declarations. A definition Lean compiled
by structural or well-founded recursion refers to its own name, or to a
same-command auxiliary that does; either way the reference appears in the
completed value. -/
def isSelfReferential (name : Name) (info : ConstantInfo) : Bool :=
  match info.value? (allowOpaque := true) with
  | some v => v.getUsedConstants.contains name
  | none => false

/-- Check one captured declaration. -/
def checkDeclaration (path : String) (m : CapturedModule) (d : CapturedDeclaration) :
    Array Diagnostic := Id.run do
  let range := m.commands[d.commandOrdinal]?.bind (·.range)
  if !acceptedDeclarationKind d.info then
    return #[unsupported "UNSUPPORTED-DECLARATION-KIND"
      s!"'{d.name}' is {kindName d.info}, which is not in the v0 source feature set"
      range path]

  let mut ds : Array Diagnostic := #[]
  if isSelfReferential d.name d.info then
    -- Compiling a recursive definition can introduce an auxiliary such as
    -- `f._unsafe_rec` that carries the self-reference, so the constant named
    -- here is often one the source never wrote. It is named anyway because it
    -- is the constant the check actually rejected, and the span already points
    -- at the source command the user needs to change.
    ds := ds.push (unsupported "UNSUPPORTED-RECURSIVE-DECLARATION"
      s!"'{d.name}' refers to itself; v0 accepts only nonrecursive declarations"
      range path)
  ds := ds ++ checkDeclarationTerms path d
  return ds

/-- Admit a captured module, or produce the diagnostics that reject it.

Command checks run first: a module containing a command v0 cannot elaborate
should be reported as such rather than through whatever declarations that
command happened to produce. -/
def admitModule (path : String) (m : CapturedModule)
    (delta : Array CapturedDeclaration) : Array Diagnostic := Id.run do
  let commandDiags := checkCommands path m
  if !commandDiags.isEmpty then
    return commandDiags
  let mut ds : Array Diagnostic := #[]
  for d in delta do
    ds := ds ++ checkDeclaration path m d
  return ds

end ExplicitLean
