import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import ExplicitLean.SimpTrace

open Finsupp CategoryTheory

/- `Finsupp.sum_sum_index` has two explicit proposition premises, `h_zero`
and `h_add`. Each is discharged by a nested simp. Rewrites in the second
discharger must not consume the first discharger's queued side trace. -/
example {R : Type*} [CommRing R] {C : Type u} [Category.{v} C]
    {W X Y Z : C} (f : (W ⟶ X) →₀ R) (g : (X ⟶ Y) →₀ R)
    (h : (Y ⟶ Z) →₀ R) :
    ((f.sum (fun f1 s => g.sum (fun g1 t => single (f1 ≫ g1) (s * t)))).sum
      (fun f2 s2 => h.sum (fun g2 t2 => single (f2 ≫ g2) (s2 * t2)))) =
    (f.sum (fun f3 s3 =>
      (g.sum (fun f4 s4 => h.sum (fun g3 t3 => single (f4 ≫ g3) (s4 * t3)))).sum
        (fun g4 t4 => single (f3 ≫ g4) (s3 * t4)))) := by
  simp_trace [sum_sum_index, add_mul, mul_add, Category.assoc, mul_assoc]
    =>trace "DISCHARGE_SIDE_PREFIX_TRACE_PATH"
