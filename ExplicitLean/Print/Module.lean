import ExplicitLean.Print.Term
import ExplicitLean.Admission

/-!
# Declarations and modules

Prints a captured module as a grammar-version-1 Explicit Lean module under
[G2](../../GRAMMAR.md#g2-modules-and-commands), [G3](../../GRAMMAR.md#g3-declaration-modifiers-and-names),
[G4](../../GRAMMAR.md#g4-binders-and-declaration-headers), and
[G5](../../GRAMMAR.md#g5-definitions-theorems-axioms-and-aliases), following
[L2](../../LOWERING.md#l2-declaration-inventory-names-namespaces-and-imports)
and [L4](../../LOWERING.md#l4-declaration-telescopes-and-binder-annotations).

A generated module is imports, the fixed `set_option autoImplicit false`
directive, namespaces, and declarations. Output is UTF-8 with LF line endings,
no byte-order mark, no tabs, no comments, and no trailing whitespace.
-/

open Lean

namespace ExplicitLean

/-- The declaration keyword for a captured constant.

`abbrev` is not distinguished here: the environment records it as a definition
with reducible hints, and v0 prints it as `def`, which has the same meaning for
every check v0 performs. -/
def declarationKeyword : ConstantInfo → Option String
  | .defnInfo _ => some "def"
  | .thmInfo _ => some "theorem"
  | .opaqueInfo _ => some "opaque"
  | _ => none

/-- Split a declaration's type into its header binders and result type.

L4 keeps the boundary between declaration parameters and a function-valued
result, so this peels exactly as many `forall` binders as the value has leading
lambdas. A declaration whose value is not a lambda states its complete type as
the result and has no header binders. -/
partial def splitTelescope (env : Environment) (ctx : NameContext)
    (type : Expr) (value : Option Expr) :
    Except PrintError (Array Doc × Doc × Option Doc) := do
  go ctx type value #[]
where
  go (ctx : NameContext) (type : Expr) (value : Option Expr) (binders : Array Doc) :
      Except PrintError (Array Doc × Doc × Option Doc) := do
    match type, value with
    | .forallE tName tType tBody _, some (.lam vName _ vBody info) =>
      -- The value's binder name is the meaningful one: it is what the source
      -- wrote at the binding site.
      let typeDoc ← printTerm env ctx .top tType
      let suggested := if vName.isAnonymous then tName else vName
      let printed := ctx.freshName suggested info tType
      let inner := ctx.push printed
      go inner tBody (some vBody)
        (binders.push (.text s!"({printed} : " ++ typeDoc ++ .text ")"))
    | _, _ =>
      let resultDoc ← printTerm env ctx .top type
      let valueDoc ← match value with
        | some v => some <$> printTerm env ctx .top v
        | none => pure none
      return (binders, resultDoc, valueDoc)

/-- Print one declaration as a G5 `defDecl`, `theoremDecl`, or `opaqueDecl`.

`namespaceDepth` is how many leading components of the declaration's name are
already open as namespace blocks. A declaration inside `namespace Outer` states
only the remaining components, since stock Lean prefixes the open namespace to
whatever name the declaration states. -/
def printDeclaration (env : Environment) (namespaceDepth : Nat) (d : CapturedDeclaration) :
    Except PrintError Doc := do
  let some keyword := declarationKeyword d.info
    | .error { code := "PRINT-UNSUPPORTED-DECLARATION"
               message := s!"'{d.name}' has no grammar-version-1 declaration form" }
  let relative :=
    (d.name.componentsRev.reverse.drop namespaceDepth).foldl
      (init := Name.anonymous) fun acc c =>
        match c with
        | .str _ s => acc.mkStr s
        | .num _ i => acc.mkNum i
        | .anonymous => acc
  let some declName := printName relative
    | .error { code := "PRINT-UNPRINTABLE-NAME"
               message := s!"declaration '{d.name}' has no printable identifier" }

  -- Every universe parameter occurs in the binder, in environment order. An
  -- empty universe binder is forbidden, so a monomorphic declaration omits it.
  let universeBinder ←
    if d.info.levelParams.isEmpty then pure ""
    else
      let names ← d.info.levelParams.mapM fun u =>
        match printName u with
        | some text => pure text
        | none => .error { code := "PRINT-UNPRINTABLE-NAME"
                           message := s!"universe parameter '{u}' has no printable identifier" }
      pure s!".\{{String.intercalate ", " names}}"

  let (binders, resultDoc, valueDoc) ←
    splitTelescope env {} d.info.type d.value?

  match valueDoc with
  | some value =>
    -- The declaration header is a group: a long binder list soft-breaks between
    -- complete binders, and the body soft-breaks after `:=` and nests one level.
    let binderDoc :=
      if binders.isEmpty then Doc.empty
      else Doc.soft ++ Doc.joinSoft binders.toList
    let header :=
      Doc.group (.nest (Doc.text s!"{keyword} {declName}{universeBinder}"
        ++ binderDoc ++ .soft ++ .text ": " ++ resultDoc ++ .text " :="))
    return header ++ .nest (.hard ++ value)
  | none =>
    .error { code := "PRINT-MISSING-VALUE"
             message := s!"'{d.name}' has no value; grammar version 1 has no bodyless \
declaration outside `axiom`, which v0 does not accept" }

/-- The namespace components of a declaration name, excluding its final
component. -/
def declarationNamespace (n : Name) : Array String :=
  let components := n.componentsRev.reverse
  (components.dropLast).toArray.filterMap fun c =>
    match c with
    | .str _ s => some s
    | _ => none

/-- Print the module's imports.

Grammar version 1 conservatively retains legal source imports in source order.
v0 translates one module at a time with no generated dependencies, so every
import is a pinned base module retained exactly.

Lean's implicit prelude import and a module's own `import Init` appear as
separate header entries that differ only in flags; they collapse to one import
command because G2 has no syntax for that distinction and importing a module
twice is not meaningful. -/
def printImports (m : CapturedModule) : Except PrintError (Array String) := do
  let mut seen : Array Name := #[]
  let mut lines : Array String := #[]
  for imp in m.finalEnv.header.imports do
    if !seen.contains imp.module then
      seen := seen.push imp.module
      let some text := printName imp.module
        | .error { code := "PRINT-UNPRINTABLE-NAME"
                   message := s!"import '{imp.module}' has no printable identifier" }
      lines := lines.push s!"import {text}"
  return lines

/-- Print a complete generated module.

Declarations are emitted in captured source order. v0 accepts only nonrecursive,
nonmutual declarations, and a later declaration can only refer to an earlier one,
so source order already satisfies the L2 requirement that dependencies precede
consumers; the general topological sort arrives with the declaration forms that
need it.

Namespaces are opened and closed by the L2 longest-common-prefix procedure. -/
def printModule (env : Environment) (m : CapturedModule)
    (delta : Array CapturedDeclaration) : Except PrintError String := do
  let imports ← printImports m

  let mut lines : Array String := imports
  if !imports.isEmpty then
    lines := lines.push ""
  lines := lines.push "set_option autoImplicit false"

  let mut stack : Array String := #[]
  let mut first := true
  for d in delta do
    let target := declarationNamespace d.name
    -- Close components not shared with this declaration's namespace, then open
    -- the remaining ones.
    let shared := commonPrefixLength stack target
    for _ in [shared:stack.size] do
      let closing := stack.back!
      stack := stack.pop
      lines := lines.push (indent stack.size ++ s!"end {closing}")
    for i in [shared:target.size] do
      lines := lines.push ""
      lines := lines.push (indent stack.size ++ s!"namespace {target[i]!}")
      stack := stack.push target[i]!
      first := true

    if !first || shared == stack.size then
      lines := lines.push ""
    first := false

    -- A namespace nests its items by one level per component, so the
    -- declaration is wrapped in that many `nest`s before rendering. The width
    -- budget then accounts for the indentation, which is what keeps a deeply
    -- nested declaration inside the 100-column limit.
    let doc ← printDeclaration env stack.size d
    -- Rendering a leading hard break inside the nesting puts the very first
    -- line at the namespace indentation too, so the layout engine's column
    -- budget accounts for it on every line rather than only after a break. The
    -- resulting empty first line is dropped.
    let rendered := Doc.render (nestBy stack.size (.hard ++ doc))
    for line in (rendered.splitOn "\n").drop 1 do
      lines := lines.push line

  for _ in [0:stack.size] do
    let closing := stack.back!
    stack := stack.pop
    lines := lines.push ""
    lines := lines.push (indent stack.size ++ s!"end {closing}")

  return String.intercalate "\n" lines.toList ++ "\n"
where
  indent (depth : Nat) : String := String.ofList (List.replicate (depth * 2) ' ')

  /-- Wrap a document in `depth` nesting levels. -/
  nestBy (depth : Nat) (doc : Doc) : Doc :=
    match depth with
    | 0 => doc
    | d + 1 => .nest (nestBy d doc)

  commonPrefixLength (a b : Array String) : Nat := Id.run do
    let mut i := 0
    while i < a.size do
      if i < b.size then
        if a[i]! == b[i]! then i := i + 1 else break
      else break
    return i

end ExplicitLean
