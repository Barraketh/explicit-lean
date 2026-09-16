/-
Trace data model for `simp_trace`, mirroring `tracking/SIMP-TRACE-SPEC.md`
(schema `simp-trace-v1`).

This module is recorder machinery, not product code: it names `Lean.Meta.Simp`
types on purpose.  Nothing here is imported by translated Mathlib source.
-/

module

public meta import Lean

public meta section

namespace ExplicitLean.SimpTrace

open Lean

/-- A position is a list of child indices from the root of the location, using
the `SubExpr.Pos` child convention described in the spec.  We keep the explicit
array rather than a packed `SubExpr.Pos` because the spec's wire form is the
array and because packed positions cap the coordinate at `maxChildren`. -/
abbrev Pos := Array Nat

/-- How a location (goal or hypothesis) was closed, if it was. -/
structure CloseInfo where
  /-- `rfl`, `trivial`, `assumption:<name>`, `eq_self` or `decide`. -/
  by_ : String
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
  /-- Explicit argument terms needed for replay. -/
  args    : Array String := #[]
  /-- `eq` steps: the computed equation and how replay should prove it. -/
  lhs?    : Option String := none
  rhs?    : Option String := none
  by_?    : Option String := none
  source? : Option String := none
  /-- `change` steps: the `pp.all` target term. -/
  to?     : Option String := none
  before? : Option String := none
  after?  : Option String := none
  /-- Side-condition sub-traces, one per discharged hypothesis. -/
  side    : Array SideTrace := #[]

/-- A side-condition sub-trace: the same `steps`/`close` shape as a location. -/
structure SideTrace where
  goal  : String
  steps : Array Step := #[]
  close : Option CloseInfo := none

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

/-- Join the non-empty field renderings into an object. -/
private def obj (fields : Array (String × Option String)) : String :=
  let parts := fields.filterMap fun (k, v?) => v?.map fun v => str k ++ ":" ++ v
  "{" ++ String.intercalate "," parts.toList ++ "}"

def CloseInfo.toJson (c : CloseInfo) : String :=
  obj #[("by", some (str c.by_))]

mutual

partial def Step.toJson (s : Step) : String :=
  obj #[
    ("kind", some (str s.kind)),
    ("pos", some (posJson s.pos)),
    ("name", s.name?.map str),
    ("dir", s.dir?.map str),
    ("args", if s.args.isEmpty then none else some (strArray s.args)),
    ("lhs", s.lhs?.map str),
    ("rhs", s.rhs?.map str),
    ("by", s.by_?.map str),
    ("source", s.source?.map str),
    ("to", s.to?.map str),
    ("before", s.before?.map str),
    ("after", s.after?.map str),
    ("side", if s.side.isEmpty then none else
      some ("[" ++ String.intercalate ","
        (s.side.toList.map SideTrace.toJson) ++ "]"))]

partial def SideTrace.toJson (t : SideTrace) : String :=
  obj #[
    ("goal", some (str t.goal)),
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
    ("locations", some ("[" ++ String.intercalate ","
      (t.locations.toList.map LocationTrace.toJson) ++ "]"))]

end ExplicitLean.SimpTrace
