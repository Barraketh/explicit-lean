/-!
# Grouped document renderer

The deterministic layout engine required by
[G1 canonical layout](../../GRAMMAR.md#g1-canonical-layout).

Artifact-convention set 1 uses a maximum width of 100 Unicode scalar columns and
two spaces per nesting level. A hard line always breaks. A soft line renders as
one ASCII space when its complete enclosing group fits in the remaining columns
through the next hard line; otherwise every soft line in that group breaks.

Fitting and rendering scan left to right, never consult terminal width or
locale, and permit an indivisible token to exceed 100 columns.
-/

namespace ExplicitLean

/-- A layout document. -/
inductive Doc where
  /-- Literal text containing no line break. -/
  | text (s : String)
  /-- A break that always renders as a newline. -/
  | hard
  /-- A break that renders as one ASCII space when its enclosing group fits, and
  as a newline otherwise. -/
  | soft
  | concat (a b : Doc)
  /-- Nest the enclosed document one further indentation level. -/
  | nest (inner : Doc)
  /-- A group: every soft break inside it breaks together, or none does. -/
  | group (inner : Doc)
  deriving Inhabited

namespace Doc

instance : Append Doc := ⟨.concat⟩

/-- The empty document. -/
def empty : Doc := .text ""

/-- Concatenate documents, separating adjacent ones with a soft break. -/
def joinSoft (docs : List Doc) : Doc :=
  match docs with
  | [] => empty
  | d :: rest => rest.foldl (init := d) fun acc x => acc ++ .soft ++ x

/-- Concatenate documents, separating adjacent ones with a hard break. -/
def joinHard (docs : List Doc) : Doc :=
  match docs with
  | [] => empty
  | d :: rest => rest.foldl (init := d) fun acc x => acc ++ .hard ++ x

/-- Maximum line width in Unicode scalar columns. -/
def maxWidth : Nat := 100

/-- Columns per nesting level. -/
def indentWidth : Nat := 2

/-- Whether the soft breaks of the group being measured are flattened. -/
private inductive Mode where
  | flat
  | break_
  deriving BEq

/-- Does the remaining document fit in `available` columns, up to the next
break that is rendered as a newline?

This is the left-to-right fitting scan: it stops at the first hard break, or at
the first soft break in a group that is already broken, because everything after
that starts a fresh line. -/
private partial def fits (available : Nat) (items : List (Nat × Mode × Doc)) : Bool :=
  match items with
  | [] => true
  | (indent, mode, doc) :: rest =>
    match doc with
    | .text s =>
      -- Width is counted in Unicode scalars, not bytes, so a multi-byte
      -- identifier occupies the columns it actually displays.
      let width := s.length
      if width > available then false else fits (available - width) rest
    | .hard => true
    | .soft =>
      match mode with
      | .flat => if available < 1 then false else fits (available - 1) rest
      | .break_ => true
    | .concat a b => fits available ((indent, mode, a) :: (indent, mode, b) :: rest)
    | .nest inner => fits available ((indent + 1, mode, inner) :: rest)
    -- A nested group is measured flattened: the question is whether the whole
    -- thing fits on this line.
    | .group inner => fits available ((indent, .flat, inner) :: rest)

/-- Render a document. -/
partial def render (doc : Doc) : String :=
  go 0 [(0, .break_, doc)] ""
where
  go (column : Nat) (items : List (Nat × Mode × Doc)) (acc : String) : String :=
    match items with
    | [] => acc
    | (indent, mode, doc) :: rest =>
      match doc with
      | .text s => go (column + s.length) rest (acc ++ s)
      | .hard =>
        let padding := String.ofList (List.replicate (indent * indentWidth) ' ')
        go (indent * indentWidth) rest (acc ++ "\n" ++ padding)
      | .soft =>
        match mode with
        | .flat => go (column + 1) rest (acc ++ " ")
        | .break_ =>
          let padding := String.ofList (List.replicate (indent * indentWidth) ' ')
          go (indent * indentWidth) rest (acc ++ "\n" ++ padding)
      | .concat a b => go column ((indent, mode, a) :: (indent, mode, b) :: rest) acc
      | .nest inner => go column ((indent + 1, mode, inner) :: rest) acc
      | .group inner =>
        -- A group is flattened exactly when its complete contents fit in the
        -- remaining columns through the next hard break.
        let remaining := if column ≥ maxWidth then 0 else maxWidth - column
        let mode' :=
          if fits remaining ((indent, .flat, inner) :: rest) then Mode.flat else Mode.break_
        go column ((indent, mode', inner) :: rest) acc

end Doc

end ExplicitLean
