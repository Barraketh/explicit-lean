import ExplicitLean.Print.Doc
import ExplicitLean.Print.Level
import ExplicitLean.Print.Name

/-!
# Terms

Prints completed expressions as [G8](../../GRAMMAR.md#g8-terms) terms.

Every elaboration choice the source made is printed explicitly: universe
arguments appear in the referenced declaration's environment order, and `@`
exposes stock implicit and instance binders where they exist, so that the
captured application spine is reproduced without any insertion happening again
during output elaboration.

Binders are converted from de Bruijn indices to names here. A meaningful source
binder name is retained when it does not collide at its binding site; otherwise
the printer synthesizes one from the L2 role bases.
-/

open Lean

namespace ExplicitLean

/-- Why a term could not be printed. -/
structure PrintError where
  code : String
  message : String
  deriving Repr

/-- The naming context while printing one declaration.

`binders` holds the printed name of each enclosing binder, innermost last, so a
de Bruijn index counts back from the end. `used` holds every name currently
visible, which is what a fresh name must avoid. -/
structure NameContext where
  binders : Array String := #[]
  used : Array String := #[]
  deriving Inhabited

namespace NameContext

/-- The printed name for a de Bruijn index, or `none` when the index is
loose. -/
def lookup (ctx : NameContext) (i : Nat) : Option String :=
  if i < ctx.binders.size then
    some ctx.binders[ctx.binders.size - 1 - i]!
  else
    none

/-- The L2 role base for a binder, chosen from its type and source name.

`u` is for a universe, `inst` for an instance, `h` for a proof, and `x`
otherwise. v0 has no recursive callbacks, so the `rec` base is unused. -/
def roleBase (binderInfo : BinderInfo) (type : Expr) : String :=
  if binderInfo == .instImplicit then "inst"
  else if type.isProp then "h"
  else "x"

/-- Choose a printable name for a binder.

A meaningful source name is retained when it is plainly printable and unused;
otherwise the role base followed by the least positive integer that is free. -/
def freshName (ctx : NameContext) (suggested : Name) (binderInfo : BinderInfo)
    (type : Expr) : String :=
  let candidate :=
    match suggested with
    | .str _ s =>
      -- An inaccessible name ends in a macro-scope marker and is not meaningful.
      if isPlainIdentifier s && !s.contains '✝' then some s else none
    | _ => none
  match candidate with
  | some s => if ctx.used.contains s then numbered s else s
  | none => numbered (roleBase binderInfo type)
where
  numbered (base : String) : String :=
    let rec go (n : Nat) (fuel : Nat) : String :=
      match fuel with
      | 0 => s!"{base}_overflow"
      | fuel + 1 =>
        let candidate := s!"{base}{n}"
        if ctx.used.contains candidate then go (n + 1) fuel else candidate
    go 1 (ctx.used.size + 1)

/-- Push a binder, returning its printed name and the extended context. -/
def push (ctx : NameContext) (name : String) : NameContext :=
  { binders := ctx.binders.push name, used := ctx.used.push name }

end NameContext

/-- Precedence contexts a term can be printed in.

G8's productions are unambiguous once parentheses are inserted where Lean's
parser requires them. The printer never emits redundant parentheses, so each
context records exactly what must be wrapped. -/
inductive Prec where
  /-- Anywhere a complete term is expected. Nothing needs parentheses. -/
  | top
  /-- An argument of an application, or the domain of an arrow: every compound
  form must be parenthesized. -/
  | arg
  /-- The function of an application: an application need not be parenthesized,
  but every other compound form must be. -/
  | fn
  deriving Inhabited, Repr, BEq

/-- Print a string literal with the canonical G10 encoding.

`"` and `\` are escaped, carriage return, line feed, and tab use their short
escapes, every other scalar in U+0000–U+001F or U+007F–U+009F becomes `\uNNNN`
with exactly four uppercase hexadecimal digits, and every other Unicode scalar
is emitted directly.

Note the deliberate difference from M1 canonical JSON, which uses lowercase hex
and a different escape set: these are two separate encodings and must not be
shared. -/
def printStringLiteral (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\r' => acc ++ "\\r"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | c =>
      let n := c.val.toNat
      if n < 0x20 || (n ≥ 0x7f && n ≤ 0x9f) then
        let digit (i : Nat) : Char :=
          if i < 10 then Char.ofNat (i + '0'.toNat) else Char.ofNat (i - 10 + 'A'.toNat)
        acc ++ "\\u"
          |>.push (digit ((n / 4096) % 16))
          |>.push (digit ((n / 256) % 16))
          |>.push (digit ((n / 16) % 16))
          |>.push (digit (n % 16))
      else
        acc.push c
  "\"" ++ body ++ "\""

/-- The universe parameters of a constant, in environment order. -/
private def constantUniverses (env : Environment) (n : Name) : Option (List Name) :=
  (env.find? n).map (·.levelParams)

/-- Does this constant's type have a binder that elaboration would fill in?

A reference to such a constant needs `@` so that the captured spine is printed
without any argument being inserted again. A constant whose binders are all
explicit does not, and G8 forbids the redundant marker. -/
private partial def hasNonExplicitBinder (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some info => go info.type
  | none => false
where
  go : Expr → Bool
    | .forallE _ _ body info => info != .default || go body
    | _ => false

/-- Wrap a document in parentheses when the context requires it.

The printer inserts only the parentheses Lean's parser requires and never emits
redundant ones. -/
private def paren (needed : Bool) (doc : Doc) : Doc :=
  if needed then Doc.text "(" ++ doc ++ Doc.text ")" else doc

/-- Print a completed expression as a G8 term.

Every reference prints its complete universe instantiation, so the application
spine is reproduced exactly as captured rather than reconstructed by
elaboration.

G8 requires `@` exactly when exposing a non-explicit binder is necessary, and
forbids redundant syntax otherwise, so it is printed for a constant whose type
has any implicit, strict-implicit, or instance binder and omitted for one whose
binders are all explicit. -/
partial def printTerm (env : Environment) (ctx : NameContext) (prec : Prec) (e : Expr) :
    Except PrintError Doc := do
  match e with
  | .bvar i =>
    match ctx.lookup i with
    | some name => return .text name
    | none =>
      .error { code := "PRINT-LOOSE-BOUND-VARIABLE"
               message := s!"bound variable index {i} has no enclosing binder" }

  | .fvar _ =>
    .error { code := "PRINT-FREE-VARIABLE"
             message := "a free variable escaped its declaration telescope" }

  | .mvar _ =>
    .error { code := "PRINT-METAVARIABLE"
             message := "an unresolved metavariable reached the printer" }

  | .sort l => return .text (printSort l)

  | .const n levels =>
    let some name := printGlobalName n
      | .error { code := "PRINT-UNPRINTABLE-NAME"
                 message := s!"constant '{n}' has no printable identifier" }
    -- A polymorphic reference prints all universe arguments in the referenced
    -- declaration's environment order; a monomorphic one prints none.
    let expected := (constantUniverses env n).getD []
    if expected.length != levels.length then
      .error { code := "PRINT-UNIVERSE-ARITY"
               message := s!"constant '{n}' expects {expected.length} universe \
arguments but the captured reference supplies {levels.length}" }
    let atSign := if hasNonExplicitBinder env n then "@" else ""
    if levels.isEmpty then
      return .text s!"{atSign}{name}"
    else
      let rendered := levels.map printLevel
      -- A universe suffix is one indivisible token: G1 forbids breaking inside
      -- it, so it is emitted as a single text item.
      return .text s!"{atSign}{name}.\{{String.intercalate ", " rendered}}"

  -- `nat_lit n` is two tokens, so it is parenthesized wherever a single argument
  -- is expected; a string literal is one token and never needs parentheses.
  | .lit (.natVal n) => return paren (prec != .top) (.text s!"nat_lit {n}")
  | .lit (.strVal s) => return .text (printStringLiteral s)

  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let fnDoc ← printTerm env ctx .fn fn
    let argDocs ← args.mapM fun a => printTerm env ctx .arg a
    -- Each maximal application spine is a group, and a broken spine nests its
    -- arguments one level.
    let spine := Doc.group (.nest (Doc.joinSoft (fnDoc :: argDocs.toList)))
    return paren (prec == .arg) spine

  | .lam .. => printBinderChain env ctx prec e (isLambda := true)
  | .forallE .. => printBinderChain env ctx prec e (isLambda := false)

  | .letE name type value body _ =>
    let typeDoc ← printTerm env ctx .top type
    let valueDoc ← printTerm env ctx .top value
    let printed := ctx.freshName name .default type
    let inner := ctx.push printed
    let bodyDoc ← printTerm env inner .top body
    -- The bound value may break; the body always starts a new line, since a
    -- `let` chain reads as a sequence of steps.
    let header :=
      Doc.group (.nest (Doc.text s!"let {printed} : " ++ typeDoc ++ .text " :=" ++ .soft ++ valueDoc))
    return paren (prec != .top) (header ++ .text ";" ++ .hard ++ bodyDoc)

  | .mdata _ inner =>
    -- Expression metadata carries no semantic content that G8 can state, and
    -- L4 authorizes discarding it after its contents are lowered.
    printTerm env ctx prec inner

  | .proj structName idx _ =>
    -- G8 has no numeric projection, so an `Expr.proj` would have to be printed
    -- as the named projection function applied to the structure's parameters
    -- and receiver. Those parameters are not present in the `proj` node and
    -- would have to be recovered by inferring the receiver's type, which is
    -- reconstruction rather than printing a recorded choice.
    --
    -- No v0-admitted module reaches this: source field access, including
    -- `p.fst` and `s.val`, elaborates to an ordinary projection-function
    -- application, and `Expr.proj` was observed only inside the constants
    -- generated for a `structure`, which v0 rejects. Rejecting here rather than
    -- guessing keeps the printer's output a record of what was captured. The
    -- rule arrives with the structure support that makes it reachable.
    .error { code := "PRINT-STRUCTURE-PROJECTION"
             message := s!"a structure projection of '{structName}' at index {idx} \
has no grammar-version-1 spelling in v0" }

where
  /-- Print a run of consecutive lambda or `forall` binders as one binder list.

  G8's `lambda` and `forallTerm` take one or more binders, so a chain is printed
  as a single form rather than nested ones. -/
  printBinderChain (env : Environment) (ctx : NameContext) (prec : Prec) (e : Expr)
      (isLambda : Bool) : Except PrintError Doc := do
    let mut binders : Array Doc := #[]
    let mut current := e
    let mut inner := ctx
    repeat
      match current, isLambda with
      | .lam name type body info, true =>
        let typeDoc ← printTerm env inner .top type
        let printed := inner.freshName name info type
        binders := binders.push (.text s!"({printed} : " ++ typeDoc ++ .text ")")
        inner := inner.push printed
        current := body
      | .forallE name type body info, false =>
        let typeDoc ← printTerm env inner .top type
        let printed := inner.freshName name info type
        binders := binders.push (.text s!"({printed} : " ++ typeDoc ++ .text ")")
        inner := inner.push printed
        current := body
      | _, _ => break
    let bodyDoc ← printTerm env inner .top current
    -- A binder list may soft-break between complete binders, never inside one.
    let binderDoc := Doc.group (.nest (Doc.joinSoft binders.toList))
    let keyword := if isLambda then Doc.text "fun " else Doc.text "forall "
    let separator := if isLambda then Doc.text " =>" else Doc.text ","
    let doc := Doc.group (.nest (keyword ++ binderDoc ++ separator ++ .soft ++ bodyDoc))
    return paren (prec != .top) doc

end ExplicitLean
