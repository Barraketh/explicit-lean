/- Focused regression for de Bruijn depth across an interleaved binder spine. -/
import Mathlib.Algebra.Algebra.Operations
import ExplicitLean.SimpTrace

namespace ExplicitLean.SimpTrace.T77BinderSpine

example (P : Nat → Prop) :
    (∀ x : Nat, x + 0 = 0 → ∃ y : Nat, y + 0 = 0 ∧ P x) ↔
      (∀ x : Nat, x = 0 → ∃ y : Nat, y = 0 ∧ P x) := by
  simp_trace only [Nat.add_zero]

end ExplicitLean.SimpTrace.T77BinderSpine

namespace Submodule

universe u v
variable {R : Type u} [CommSemiring R] {A : Type v} [CommSemiring A] [Algebra R A]

theorem map_div_binder_spine_smoke {B : Type*} [CommSemiring B] [Algebra R B]
    (I J : Submodule R A) (h : A ≃ₐ[R] B) :
    (I / J).map h.toLinearMap = I.map h.toLinearMap / J.map h.toLinearMap := by
  ext x
  simp_trace only [mem_map, mem_div_iff_forall_mul_mem, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hx _ hy, map_mul h x y⟩
  · rintro hx
    refine ⟨h.symm x, fun z hz => ?_, h.apply_symm_apply x⟩
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩
    convert! xz_mem
    apply h.injective
    rw [map_mul, h.apply_symm_apply, hxz]

end Submodule
