/- Focused source-argument replay fixtures for explicit `@` applications. -/

import Mathlib.Logic.Basic
import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.SourceAtArguments

example {a b : Prop} : Xor a b ↔ (¬a ↔ b) := by
  explicit_rw [← @xor_not_left _ b at [1], Classical.not_not at [1, 0, 1],
    iff_self at []] then exact True.intro

example {α : Sort*} [DecidableEq α] {p : α → Prop} (a : α) :
    (p a ∧ ∀ b, b ≠ a → p b) ↔ ∀ b, p b := by
  explicit_rw [← @forall_eq _ p a at [0, 1, 0, 1], ← forall_and at [0, 1],
    ← or_imp at [0, 1, 1], prop_true Decidable.em at [0, 1, 1, 0],
    forall_const at [0, 1, 1], iff_self at []] then exact True.intro

end ExplicitRwTest.SourceAtArguments
