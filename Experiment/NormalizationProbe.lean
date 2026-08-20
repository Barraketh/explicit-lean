import ExplicitLean.Normalize
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Algebra.DualNumber
import Mathlib.CategoryTheory.Localization.SmallHom
import Mathlib.Data.List.DropRight

open ExplicitLean CategoryTheory CategoryTheory.Category

private theorem alternate_comp_id {C : Type*} [Category C]
    {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := Category.comp_id f

attribute [local simp 2000] alternate_comp_id

-- The direct normalizer must not depend on the category laws being simp rules.
attribute [-simp] Category.assoc Category.id_comp Category.comp_id

example {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    ((𝟙 W ≫ f) ≫ g) ≫ h = f ≫ g ≫ h := by
  normalize_category

set_option linter.unusedTactic false in
example {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (k : W ⟶ Z)
    (canonical : f ≫ g ≫ h = k) :
    ((𝟙 W ≫ f) ≫ g) ≫ h ≫ 𝟙 Z = k := by
  normalize_category
  normalize_category
  exact canonical

/-- The direct category normalizer ignores the higher-priority local simp rule. -/
example {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by
  normalize_category

example {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) :
    F.map ((𝟙 W ≫ f) ≫ g) = F.map f ≫ F.map g := by
  normalize_category
  normalize_functor

example {R : Type*} [Ring R] (x y : R) :
    ((0 + x) * 1 + y * 0) - 0 = x := by
  normalize_algebra

example {R : Type*} [Semiring R] (l : List R) (x : R) :
    ((l ++ [x]).reverse).reverse = l ++ [x] := by
  normalize_list

example (x : ℂ) : (x + Complex.I).re = x.re := by
  normalize_complex
  normalize_algebra

namespace CategoryTheory.Localization.SmallHom

universe w v u

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}
variable {X Y Z T : C}

example [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocalizedHom.{w} W X Z]
    [HasSmallLocalizedHom.{w} W X T] [HasSmallLocalizedHom.{w} W Y Z]
    [HasSmallLocalizedHom.{w} W Y T] [HasSmallLocalizedHom.{w} W Z T]
    (α : SmallHom.{w} W X Y) (β : SmallHom.{w} W Y Z) (γ : SmallHom.{w} W Z T) :
    (α.comp β).comp γ = α.comp (β.comp γ) := by
  apply (equiv W W.Q).injective
  simp only [equiv_comp]
  normalize_category

end CategoryTheory.Localization.SmallHom
