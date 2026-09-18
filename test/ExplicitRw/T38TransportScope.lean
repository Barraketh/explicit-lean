import Mathlib.Logic.Function.Basic
import ExplicitLean.ExplicitRw

namespace ExplicitLean.ExplicitRw.T38

universe u v

example {α : Type u} (f : α → Type max u v) : ¬ Function.Surjective f := by
  intro hf
  let T : Type max u v := Sigma f
  cases hf (Set T) with | intro U hU =>
  let g : Set T → T := fun s ↦ ⟨U, cast hU.symm s⟩
  have hg : Function.Injective g := by
    intro s t h
    suffices cast hU (g s).2 = cast hU (g t).2 by
      explicit_rw [congr 3 [proj at []] at [0, 1], cast_cast at [0, 1], cast_eq at [0, 1],
        congr 3 [proj at []] at [1], cast_cast at [1], cast_eq at [1]] at this
      assumption
    congr
  exact Function.cantor_injective g hg

example {α β γ : Type*} {f : α → β} [Nontrivial γ] :
    Function.Surjective (fun g : β → γ ↦ g ∘ f) ↔ Function.Injective f := by
  classical
  refine ⟨not_imp_not.mp fun not_inj surj ↦ not_subsingleton γ ⟨fun c c' ↦ ?_⟩,
    (·.surjective_comp_right)⟩
  explicit_rw [unfold Function.Injective at [1], Classical.not_forall at [],
    Classical.not_forall at [1, 1], Classical.not_forall at [1, 1, 1, 1]] at not_inj
  have ⟨a₁, a₂, eq, ne⟩ := not_inj
  have ⟨f', hf⟩ := surj (if · = a₂ then c else c')
  have h₁ := congr_fun hf a₁
  have h₂ := congr_fun hf a₂
  change (f' ∘ f) a₁ = _ at h₁
  change (f' ∘ f) a₂ = _ at h₂
  rw [Function.comp_apply] at h₁ h₂
  rw [if_neg ne] at h₁
  rw [if_pos rfl] at h₂
  rw [← h₁, eq, h₂]

end ExplicitLean.ExplicitRw.T38
