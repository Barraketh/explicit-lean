import ExplicitLean.Capture

/-!
# Identifiers and canonical names

Prints Lean identifiers under [G1](../../GRAMMAR.md#g1-notation-and-lexical-layer)
and [L2 canonical names](../../LOWERING.md#l2-canonical-names).

A normal global reference is rooted: the `_root_.` prefix is mandatory even when
a shorter name would resolve uniquely, so that no output reference depends on
what happens to be in scope.
-/

open Lean

namespace ExplicitLean

/-- Lean keywords that cannot be used as a bare identifier.

A retained source name that collides with one of these is escaped rather than
renamed, since escaping preserves the meaningful name L2 asks us to keep. -/
def leanKeywords : Array String := #[
  "abbrev", "at", "attribute", "axiom", "by", "calc", "case", "catch", "class",
  "def", "deriving", "do", "else", "end", "example", "exists", "extends",
  "finally", "for", "forall", "from", "fun", "have", "if", "import", "in",
  "inductive", "instance", "let", "macro", "match", "mut", "mutual",
  "namespace", "noncomputable", "notation", "opaque", "open", "partial",
  "private", "protected", "return", "section", "set_option", "show", "structure",
  "syntax", "then", "theorem", "this", "try", "universe", "unsafe", "variable",
  "where", "while", "with"
]

/-- Can this string be printed as an ordinary Lean identifier component?

Lean identifiers begin with a letter or one of a small set of symbols and
continue with letters, digits, `_`, `'`, `!`, or `?`. Anything else, including a
keyword, needs the escaped-identifier token. -/
def isPlainIdentifier (s : String) : Bool :=
  !s.isEmpty
    && !leanKeywords.contains s
    && isFirst (s.front)
    && s.all fun c => isFirst c || c.isDigit || c == '\'' || c == '!' || c == '?'
where
  isFirst (c : Char) : Bool :=
    c.isAlpha || c == '_' || Lean.isLetterLike c

/-- Print one name component, escaping it when it is not a plain identifier.

Lean's escaped-identifier token is `«…»`. A component containing `»` cannot be
escaped this way; such a name is rejected rather than mangled, because silently
changing an identifier would break the correspondence the manifest records. -/
def printComponent (s : String) : Option String :=
  if isPlainIdentifier s then some s
  else if s.any (· == '»') then none
  else some s!"«{s}»"

/-- Print a name as dot-separated components, or `none` when a component cannot
be printed. -/
def printName (n : Name) : Option String := do
  let components := n.componentsRev.reverse
  if components.isEmpty then none
  else
    let parts ← components.mapM fun c =>
      match c with
      | .str _ s => printComponent s
      | .num _ i =>
        -- A numeric component has no ordinary identifier spelling. L2 requires
        -- these to be replaced by deterministic names before printing.
        let _ := i
        none
      | .anonymous => none
    some (String.intercalate "." parts)

/-- Print a global reference with the mandatory `_root_.` prefix. -/
def printGlobalName (n : Name) : Option String := do
  let text ← printName n
  some s!"_root_.{text}"

end ExplicitLean
