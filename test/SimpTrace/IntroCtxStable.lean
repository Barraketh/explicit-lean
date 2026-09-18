/-
Focused T34 fixture: the contextual `simp` at Function.Basic site 7.

The two examples are alpha-renamed copies of the same dependent-function
shape.  Their recorder payloads must allocate contextual handles in the same
introduction order, without recovering an inaccessible display name.
-/
import ExplicitLean.SimpTrace
import Mathlib.Logic.Function.Basic

namespace ExplicitLean.SimpTrace.IntroCtxStable

open Function

universe u v

example {α : Sort u} {β : α → Sort v} [DecidableEq α]
    (f : ∀ a, β a) {a : α} {b : β a}
    (p : ∀ a, β a → Prop) :
  (∀ x, p x (update f a b x)) ↔ p a b ∧ ∀ x, x ≠ a → p x (f x) := by
  classical
  rw [← and_forall_ne a, update_self]
  simp_trace (config := { failIfUnchanged := false }) +contextual
    only [Function.update_of_ne] =>trace "test/SimpTrace/out/t34_intro_ctx_final_renamed.json"
  constructor
  · rintro ⟨h, hall⟩
    refine ⟨h, ?_⟩
    intro x hx
    have hpx := hall x hx
    rw [Function.update_of_ne hx] at hpx
    exact hpx
  · rintro ⟨h, hall⟩
    refine ⟨h, ?_⟩
    intro x hx
    rw [Function.update_of_ne hx]
    exact hall x hx

example {ι : Sort u} {γ : ι → Sort v} [DecidableEq ι]
    (g : ∀ i, γ i) {i : ι} {z : γ i}
    (q : ∀ i, γ i → Prop) :
  (∀ j, q j (update g i z j)) ↔ q i z ∧ ∀ j, j ≠ i → q j (g j) := by
  classical
  rw [← and_forall_ne i, update_self]
  simp_trace (config := { failIfUnchanged := false }) +contextual
    only [Function.update_of_ne] =>trace "test/SimpTrace/out/t34_intro_ctx_final_alpha.json"
  constructor
  · rintro ⟨h, hall⟩
    refine ⟨h, ?_⟩
    intro j hj
    have hpj := hall j hj
    rw [Function.update_of_ne hj] at hpj
    exact hpj
  · rintro ⟨h, hall⟩
    refine ⟨h, ?_⟩
    intro j hj
    rw [Function.update_of_ne hj]
    exact hall j hj

end ExplicitLean.SimpTrace.IntroCtxStable
