import ExplicitLean.SimpExplicit
import Mathlib.Data.List.DropRight
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/- Focused O3 attribution fixtures. The report checker inspects the emitted
   traces: these are intentionally shaped like the abandoned-candidate cases
   from DropRight and the conditional lattice rewrite. -/

set_option explicitLean.simpExplicit.report true in
example {α : Type*} (l : List α) : List.rdrop l 0 = l := by
  simp_explicit? only [List.rdrop, Nat.sub_zero, List.take_length]

set_option explicitLean.simpExplicit.report true in
example {α : Type*} (xs : List α) (x : α) :
    (xs ++ [x]).take (xs.length + 1) = xs ++ [x] := by
  simp_explicit? [List.take_length_add_append]

set_option explicitLean.simpExplicit.report true in
example {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (x : R) (s : Set A) :
    Algebra.adjoin R (insert (algebraMap R A x) s) = Algebra.adjoin R s := by
  rw [Set.insert_eq, Algebra.adjoin_union]
  simp_explicit?

set_option explicitLean.simpExplicit.report true in
example (n : Nat) : n + 0 = n := by
  simp_explicit? (config := { index := false })
