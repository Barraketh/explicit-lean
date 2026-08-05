import ExplicitLean.Capture

/-!
# Universe levels and sorts

Canonicalizes and prints `Level` values under
[L3](../../LOWERING.md#l3-universes-and-sorts) and
[G9](../../GRAMMAR.md#g9-universes-and-sorts).

Before printing, levels are canonicalized by applying `Lean.Level.normalize` to
a fixed point, combining successors into one offset, flattening and
deduplicating `max`, removing neutral `0` operands, sorting the remaining `max`
operands, and rebuilding a right-associated `max` tree while preserving the
argument order of any surviving `imax`.
-/

open Lean

namespace ExplicitLean

/-- A canonicalized level, in the shape G9 prints.

Separating this from `Lean.Level` makes the canonical form explicit: an offset
is one number rather than a chain of successors, and a `max` is a sorted list
rather than a nested tree. -/
inductive CLevel where
  /-- A literal universe. -/
  | lit (n : Nat)
  /-- A universe parameter with an offset, `u` when the offset is zero. -/
  | param (name : Name) (offset : Nat)
  /-- `max` over two or more operands, in canonical order, plus an offset. -/
  | max (operands : Array CLevel) (offset : Nat)
  /-- `imax`, whose operand order is meaningful and therefore preserved. -/
  | imax (lhs rhs : CLevel) (offset : Nat)
  deriving Inhabited, Repr, BEq

namespace CLevel

/-- Render a canonical level as the G9 `level` production. `prec` is the
precedence of the context: an offset binds less tightly than a level atom, so an
offset operand of `max` or `imax` is parenthesized. -/
partial def render (l : CLevel) (parenthesizeOffset : Bool := false) : String :=
  let withOffset (base : String) (offset : Nat) : String :=
    if offset == 0 then base
    else
      let text := s!"{base}+{offset}"
      if parenthesizeOffset then s!"({text})" else text
  match l with
  | .lit n => toString n
  | .param n offset => withOffset (nameText n) offset
  | .max operands offset =>
    -- `max` is binary in the grammar, so a sorted operand list rebuilds a
    -- right-associated tree.
    let base := renderMax operands
    withOffset base offset
  | .imax lhs rhs offset =>
    let base := s!"imax {argument lhs} {argument rhs}"
    withOffset base offset
where
  /-- A level in argument position is parenthesized unless it is an atom. -/
  argument (l : CLevel) : String :=
    match l with
    | .lit n => toString n
    | .param n 0 => nameText n
    | _ => s!"({render l})"

  renderMax (operands : Array CLevel) : String :=
    match operands.toList with
    | [] => "0"
    | [x] => render x
    | x :: rest =>
      s!"max {argument x} {argument (rebuild rest)}"

  /-- Rebuild the remaining operands as a right-associated `max`. -/
  rebuild : List CLevel → CLevel
    | [] => .lit 0
    | [x] => x
    | x :: rest => .max #[x, rebuild rest] 0

  nameText (n : Name) : String := n.toString

/-- Order canonical levels for the `max` operand sort.

Any total order works as long as it is deterministic and does not depend on how
the level was built, so this compares the rendered text. -/
def lt (a b : CLevel) : Bool := CJson.utf8Lt a.render b.render

end CLevel

/-- Strip successors from a level, returning the base and the offset count. -/
private partial def peelOffset (l : Level) (acc : Nat := 0) : Level × Nat :=
  match l with
  | .succ inner => peelOffset inner (acc + 1)
  | _ => (l, acc)

/-- Canonicalize an elaborated `Level`.

`Lean.Level.normalize` does most of the work; this converts the result into the
explicit canonical shape, flattening nested `max`, removing neutral `0`
operands, deduplicating, and sorting. -/
partial def canonicalLevel (l : Level) : CLevel :=
  go l.normalize
where
  go (l : Level) : CLevel :=
    let (base, offset) := peelOffset l
    match base with
    | .zero => .lit offset
    | .param n => .param n offset
    | .succ _ =>
      -- `peelOffset` removed every successor, so this cannot occur.
      .lit offset
    | .max a b =>
      let operands := (flatten a ++ flatten b)
      -- A literal operand is absorbed into the largest literal rather than
      -- repeated, and `0` is neutral.
      let (literals, others) := operands.partition fun o => o matches .lit _
      let literalMax := literals.foldl (init := 0) fun acc o =>
        match o with
        | .lit n => Nat.max acc n
        | _ => acc
      let deduped := dedupe (others.qsort CLevel.lt)
      let final :=
        if literalMax == 0 then deduped
        else dedupe ((deduped.push (.lit literalMax)).qsort CLevel.lt)
      match final.toList with
      | [] => .lit offset
      | [x] => addOffset x offset
      | _ => .max final offset
    | .imax a b =>
      -- `normalize` has already simplified what it can; the surviving operand
      -- order is meaningful and is preserved.
      .imax (go a) (go b) offset
    | .mvar _ =>
      -- Universe metavariables must be assigned before lowering, and admission
      -- rejects any that survive.
      .lit offset

  flatten (l : Level) : Array CLevel :=
    let (base, offset) := peelOffset l
    match base, offset with
    | .max a b, 0 => flatten a ++ flatten b
    | _, _ => #[go l]

  dedupe (sorted : Array CLevel) : Array CLevel :=
    sorted.foldl (init := #[]) fun acc x =>
      if acc.back? == some x then acc else acc.push x

  /-- Add an offset to an already-canonical level. -/
  addOffset (l : CLevel) (offset : Nat) : CLevel :=
    if offset == 0 then l
    else
      match l with
      | .lit n => .lit (n + offset)
      | .param n o => .param n (o + offset)
      | .max ops o => .max ops (o + offset)
      | .imax a b o => .imax a b (o + offset)

/-- Print a level as it appears inside a `universeInst` suffix. -/
def printLevel (l : Level) : String := (canonicalLevel l).render

/-- Print a sort using the canonical G9 spellings.

`Sort 0` is `Prop`, `Sort (u + 1)` is `Type u`, and every other sort is
`Sort u`. Thus the ordinary type universe is `Type 0`, never bare `Type`. -/
def printSort (l : Level) : String :=
  match canonicalLevel l with
  | .lit 0 => "Prop"
  | .lit n => s!"Type {n - 1}"
  | c =>
    -- A composite level after `Type` or `Sort` is parenthesized by `sortLevel`.
    let spell (keyword : String) (inner : CLevel) : String :=
      match inner with
      | .lit n => s!"{keyword} {n}"
      | .param n 0 => s!"{keyword} {n}"
      | _ => s!"{keyword} ({inner.render})"
    match c with
    | .param n offset => if offset == 0 then spell "Sort" c else spell "Type" (.param n (offset - 1))
    | .max ops offset => if offset == 0 then spell "Sort" c else spell "Type" (.max ops (offset - 1))
    | .imax a b offset => if offset == 0 then spell "Sort" c else spell "Type" (.imax a b (offset - 1))
    | .lit _ => spell "Sort" c

end ExplicitLean
