/- Focused consumer fixture for Function.Basic site ordinal 7.  The contextual
   arrow is replayed as a closed scope; its proof is available only through the
   recorded introduced handle. -/
import ExplicitLean.ExplicitRw
import Mathlib.Logic.Function.Basic

namespace ExplicitRwTest.IntroCtx

open Function

universe u v

theorem function_basic_site_7 {α : Sort u} {β : Sort v} [DecidableEq α]
    (f : α → β) (a : α) (b : β) (p : α → β → Prop) :
    (∀ x, p x (update f a b x)) ↔ p a b ∧ ∀ x, x ≠ a → p x (f x) := by
  rw [← and_forall_ne a, update_self]
  explicit_rw [intro_ctx 0 domain at [0, 1, 1, 1, 0] deps [1, 8, 5]
    scope 0 enter at [0, 1, 1, 1] exit at [0, 1, 1, 1]
    with [Function.update_of_ne (introduced_ref 0) at [1]] at [0, 1, 1, 1]]
  rfl

end ExplicitRwTest.IntroCtx
