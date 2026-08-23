import ExplicitLean.SimpExplicit
import Mathlib.Algebra.Algebra.Spectrum.Basic

/- A bare polymorphic declaration must stay generic while the simp theorem is
   built.  Using a type with no default instance catches accidental term
   elaboration that specializes `Set.mem_neg` before the goal is known. -/
structure O6fMemNegType where
  value : Nat

instance : Neg O6fMemNegType where
  neg x := x

open scoped Pointwise

set_option explicitLean.simpExplicit.report true in
example (s : Set O6fMemNegType) (a : O6fMemNegType) :
    a ∈ -s ↔ -a ∈ s := by
  simp_explicit? [Set.mem_neg]

section

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

example (a : A) (x : R) : x ∈ resolventSet R (-a) ↔ x ∈ -resolventSet R a := by
  simp_explicit [
    spectrum.mem_resolventSet_iff,
    sub_neg_eq_add,
    Set.mem_neg,
    spectrum.mem_resolventSet_iff,
    map_neg,
    ← neg_add',
    IsUnit.neg_iff
  ]

example (a : A) (x : R) : x ∈ -resolventSet R a ↔ -x ∈ resolventSet R a := by
  simp_explicit [Set.mem_neg]

end
