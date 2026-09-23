/-
Focused real-Lean regression for `change.to` surface printing.  The checker
`check_change_surface_printer.py` substitutes the `simp_trace` calls with the
rendered production replay, then compiles that copy in the same declaration
contexts.
-/
import ExplicitLean.SimpTrace
import ExplicitLean.ExplicitRw
import Mathlib.Algebra.Group.Basic

namespace ExplicitLean.SimpTrace.ChangeSurfaceFixture

inductive StringTag : String → Prop where
  | intro (s : String) : StringTag s

/- A `dreduceIte` step records the ordinary numeral 3.  Its elaborated term
uses `OfNat Nat 3`, but the instance and internal `nat_lit` representation
must remain hidden from the source printer. -/
example (f : Nat → Nat) :
    (∀ x : Fin (if True then (3 : Nat) else 4), f x.val = f x.val) := by
  simp_trace =>trace ".lake/private/change-surface-fixture-nat.json"

/- A second `dreduceIte` step selects an `a + 0` index.  Its ordinary surface
term uses `HAdd Nat Nat Nat` implicitly; the instance implementation must not
be exposed by the executable-term printer. -/
example (a : Nat) : ∀ x : Fin (if True then a + 0 else 4), x = x := by
  simp_trace [-Nat.add_zero] =>trace ".lake/private/change-surface-fixture-instance.json"

/- `dreduceIte` in a hypothesis type selects this literal.  Its contents look
like a universe annotation to the old renderer, but are an authenticated Lean
string literal and must survive rendering unchanged. -/
example (h : StringTag (if True then "literal.{abc}" else "other")) : True := by
  simp_trace at h =>trace ".lake/private/change-surface-fixture-string.json"
  exact True.intro

end ExplicitLean.SimpTrace.ChangeSurfaceFixture
