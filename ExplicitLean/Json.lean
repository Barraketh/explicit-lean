/-!
# Canonical JSON

[M1](../MANIFEST.md#m1-file-encoding-and-canonical-json) canonical JSON, used by
both the `json` diagnostic format and (later) the phase-one manifest.

Lean's `Lean.Json` is unsuitable: its numbers are `JsonNumber` (with a negative
exponent) and its escaping differs from M1, which forbids `null` and
floating-point numbers, and requires object keys sorted by unescaped UTF-8 bytes.
-/

namespace ExplicitLean

/-- A canonical-JSON value. M1 permits only objects, arrays, strings, booleans,
and arbitrary-precision nonnegative integers. -/
inductive CJson where
  | str (s : String)
  | bool (b : Bool)
  /-- A nonnegative integer in canonical decimal notation. -/
  | num (n : Nat)
  | arr (xs : Array CJson)
  /-- Object fields. Rendering sorts them by key; duplicates are a caller error. -/
  | obj (fields : Array (String × CJson))
  deriving Inhabited, Repr, BEq

namespace CJson

/-- Compare two strings by their UTF-8 bytes.

`String`'s `<` is a lexicographic comparison of Unicode scalar values, which for
UTF-8 induces the same order as byte comparison: UTF-8 preserves code point
order. We compare bytes directly anyway so the ordering rule is evident and does
not depend on that argument holding for future encodings. -/
def utf8Lt (a b : String) : Bool :=
  go a.toUTF8 b.toUTF8 0
where
  go (x y : ByteArray) (i : Nat) : Bool :=
    if h : i < x.size then
      if h' : i < y.size then
        let xi := x[i]
        let yi := y[i]
        if xi == yi then go x y (i + 1) else xi < yi
      else
        -- `y` is a proper prefix of `x`, so `y` sorts first.
        false
    else
      -- `x` is exhausted: it sorts first iff `y` is strictly longer.
      i < y.size
  termination_by x.size - i

/-- Escape a string per M1: escape `"`, `\`, and U+0000–U+001F, preferring the
short escapes `\b \t \n \f \r` and lowercase `\u00xx` otherwise. `/` and
non-ASCII scalars are not escaped. -/
def escapeString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\x08' => acc ++ "\\b"
    | '\t' => acc ++ "\\t"
    | '\n' => acc ++ "\\n"
    | '\x0c' => acc ++ "\\f"
    | '\r' => acc ++ "\\r"
    | c =>
      if c.val < 0x20 then
        let hexDigit (n : Nat) : Char :=
          if n < 10 then Char.ofNat (n + '0'.toNat) else Char.ofNat (n - 10 + 'a'.toNat)
        let n := c.val.toNat
        acc ++ "\\u00"
          |>.push (hexDigit ((n / 16) % 16))
          |>.push (hexDigit (n % 16))
      else
        acc.push c

/-- Render a value as canonical JSON with no insignificant whitespace. -/
partial def render (j : CJson) : String :=
  match j with
  | .str s => "\"" ++ escapeString s ++ "\""
  | .bool true => "true"
  | .bool false => "false"
  | .num n => toString n
  | .arr xs =>
    let body := xs.foldl (init := "") fun acc x =>
      (if acc.isEmpty then acc else acc ++ ",") ++ render x
    "[" ++ body ++ "]"
  | .obj fields =>
    let sorted := fields.qsort fun a b => utf8Lt a.1 b.1
    let body := sorted.foldl (init := "") fun acc (k, v) =>
      (if acc.isEmpty then acc else acc ++ ",")
        ++ "\"" ++ escapeString k ++ "\":" ++ render v
    "{" ++ body ++ "}"

end CJson

end ExplicitLean
