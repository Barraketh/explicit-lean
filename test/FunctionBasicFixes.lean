import Mathlib.Logic.Function.Basic

open Function

theorem test_injective_comp_right_iff_surjective_step {α β γ : Type*} [DecidableEq β] (f : α → β)
    (b₀ : β) (hb : ¬∃ a, f a = b₀) (c c' : γ) (a : α) :
    (fun x => c) (f a) = (if f a = b₀ then c' else c) := by
  classical
  rw [if_neg]
  intro h
  exact hb ⟨a, h⟩

theorem test_midline (f : α → β) (b₀ : β) (hb : ¬∃ a, f a = b₀) (c c' : γ) :
    (fun g : β → γ => g ∘ f) (fun _ => c) =
      (fun g : β → γ => g ∘ f) (fun x => if x = b₀ then c' else c) := by
  funext a
  change c = if f a = b₀ then c' else c
  rw [if_neg (fun h => hb ⟨a, h⟩)]

theorem test_isPartialInv_comp {α β γ : Type*} {f : α → β} {g : β → Option α}
    {h : β → γ} {i : γ → Option β}
    (hf : IsPartialInv f g) (hh : IsPartialInv h i) :
    IsPartialInv (h ∘ f) (i · |>.bind g) := by
  intros a b
  constructor
  · intro hab
    obtain ⟨x, hix, hxa⟩ := Option.bind_eq_some_iff.mp hab
    change h (f a) = b
    have hxb : h x = b := (hh x b).mp hix
    have hax : f a = x := (hf a x).mp hxa
    exact (congrArg h hax).trans hxb
  · intro hab
    rw [Option.bind_eq_some_iff]
    refine ⟨f a, (hh (f a) b).mpr ?_, (hf a (f a)).mpr ?_⟩
    · change h (f a) = b
      exact hab
    · rfl

theorem test_invFun_eq {α β : Sort*} [Nonempty α] {f : α → β} {b : β}
    (h : ∃ a, f a = b) : f (invFun f b) = b := by
  unfold invFun
  rw [dif_pos h]
  exact h.choose_spec

theorem test_update_apply {α : Type*} [DecidableEq α] {β : Sort*} (f : α → β) (a' : α) (b : β) (a : α) :
    update f a' b a = if a = a' then b else f a := by
  rcases Decidable.eq_or_ne a a' with rfl | hne
  · rw [update_self, if_pos rfl]
  · rw [update_of_ne hne, if_neg hne]

theorem test_pi_map_update {ι : Type*} [DecidableEq ι] {α β : ι → Sort*}
    {f : ∀ i, α i → β i} (g : ∀ i, α i) (i : ι) (a : α i) :
    Pi.map f (Function.update g i a) = Function.update (Pi.map f g) i (f i a) := by
  ext j
  obtain rfl | hij := eq_or_ne j i
  · rw [Pi.map_apply, Function.update_self, Function.update_self]
  · rw [Pi.map_apply, Function.update_of_ne hij, Function.update_of_ne hij, Pi.map_apply]

theorem test_extend_injective {α β γ : Type*} {f : α → β} (hf : Injective f) (e' : β → γ) :
    Injective fun g ↦ extend f g e' := by
  intro g₁ g₂ hg
  refine funext fun x ↦ ?_
  have H := congr_fun hg (f x)
  change extend f g₁ e' (f x) = extend f g₂ e' (f x) at H
  rw [hf.extend_apply, hf.extend_apply] at H
  exact H

theorem test_surjective_comp_right_step {α β γ : Type*} {f : α → β} (a₁ a₂ : α)
    (c c' : γ) (g : β → γ) (eq : f a₁ = f a₂)
    (h₁ : g (f a₁) = c') (h₂ : g (f a₂) = c) : c' = c := by
  exact h₁.symm.trans ((congrArg g eq).trans h₂)

theorem test_surjective_comp_right_change {α β γ : Type*} [DecidableEq α] {f : α → β}
    (a₁ a₂ : α) (c c' : γ) (g : β → γ)
    (hf : (fun g : β → γ => g ∘ f) g = (fun x => if x = a₂ then c else c'))
    (ne : a₁ ≠ a₂) (eq : f a₁ = f a₂) : c' = c := by
  classical
  have h₁ := congr_fun hf a₁
  have h₂ := congr_fun hf a₂
  change g _ = (if a₁ = a₂ then c else c') at h₁
  change g _ = (if a₂ = a₂ then c else c') at h₂
  rw [if_neg ne] at h₁
  rw [if_pos rfl] at h₂
  rw [← h₁, eq, h₂]

theorem test_curry_update {α α' β : Type*} [DecidableEq α] [DecidableEq α']
    (f : α × α' → β) (aa' : α × α') (b : β) :
    curry (Function.update f aa' b) =
      Function.update (curry f) aa'.1 (Function.update (curry f aa'.1) aa'.2 b) := by
  ext a a'
  let ⟨a₂, a₂'⟩ := aa'
  rw [Function.curry_apply]
  by_cases ha : a = a₂
  · subst a
    by_cases ha' : a' = a₂'
    · subst a'
      rw [update_self, update_self, update_self]
    · rw [update_of_ne (a := (a₂, a')) (a' := (a₂, a₂')) (by
        intro h
        exact ha' (Prod.mk.inj h).2), update_self, update_of_ne ha']
      rw [Function.curry_apply]
  · by_cases ha' : a' = a₂'
    · subst a'
      rw [update_of_ne (a := (a, a₂')) (a' := (a₂, a₂')) (by
        intro h
        exact ha (Prod.mk.inj h).1), update_of_ne ha]
      rw [Function.curry_apply]
    · rw [update_of_ne (a := (a, a')) (a' := (a₂, a₂')) (by
        intro h
        exact ha (Prod.mk.inj h).1), update_of_ne ha]
      rw [Function.curry_apply]
