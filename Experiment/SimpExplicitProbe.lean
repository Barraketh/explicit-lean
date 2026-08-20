import ExplicitLean.SimpExplicit
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.CategoryTheory.Category.Basic

open ExplicitLean CategoryTheory CategoryTheory.Category

example (n : Nat) : n + 0 = n := by
  simp_explicit?

example (p : Prop) : p ↔ p := by
  simp_explicit?

example (p : Prop) : p ↔ p := by
  simp_explicit []

example (n : Nat) : n + 0 = n := by
  simp_explicit? only [↓ Nat.add_zero]

example (n : Nat) : n + 0 = n := by
  simp_explicit [
    ↓ Nat.add_zero
  ]

example (n : Nat) : n.succ = n + 1 := by
  simp_explicit? only [← Nat.succ_eq_add_one]

example (n : Nat) : n.succ = n + 1 := by
  simp_explicit [
    ← Nat.succ_eq_add_one
  ]

example (a b : Nat) (h : a = b) : a = b := by
  simp_explicit? only [h]

example (a b : Nat) (h : a = b) : a = b := by
  simp_explicit [
    h
  ]

example (n : Nat) : n + 0 = n := by
  simp_explicit [
    add_zero
  ]

example {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) :
    ((𝟙 W ≫ f) ≫ g) ≫ 𝟙 Y = f ≫ g := by
  simp_explicit? only [Category.assoc, Category.id_comp, Category.comp_id]

example {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) :
    ((𝟙 W ≫ f) ≫ g) ≫ 𝟙 Y = f ≫ g := by
  normalize_category

example {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) (k : W ⟶ Y)
    (h : f ≫ g = k) : ((𝟙 W ≫ f) ≫ g) ≫ 𝟙 Y = k := by
  simp_explicit? only [Category.assoc, Category.id_comp, Category.comp_id, h]

example {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) (k : W ⟶ Y)
    (h : f ≫ g = k) : ((𝟙 W ≫ f) ≫ g) ≫ 𝟙 Y = k := by
  normalize_category
  simp_explicit [h]

example {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) (k : W ⟶ Y)
    (h : f ≫ g = 𝟙 W ≫ k) : ((𝟙 W ≫ f) ≫ g) ≫ 𝟙 Y = k := by
  simp_explicit? only [Category.assoc, Category.id_comp, Category.comp_id, h]

example {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) (k : W ⟶ Y)
    (h : f ≫ g = 𝟙 W ≫ k) : ((𝟙 W ≫ f) ≫ g) ≫ 𝟙 Y = k := by
  normalize_category
  simp_explicit [h]
  normalize_category

private def wrappedComp {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) : W ⟶ Y := (𝟙 W ≫ f) ≫ g

theorem wrappedComp_eq {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) : wrappedComp f g = (𝟙 W ≫ f) ≫ g := rfl

example {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) : wrappedComp f g = f ≫ g := by
  simp_explicit? only [wrappedComp_eq, Category.assoc, Category.id_comp, Category.comp_id]

example {C : Type*} [Category C] {W X Y : C}
    (f : W ⟶ X) (g : X ⟶ Y) : wrappedComp f g = f ≫ g := by
  simp_explicit [wrappedComp_eq]
  normalize_category

example {K : Type*} {g : GenContFract K} [DivisionRing K]
    {gp : GenContFract.Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by
  simp_explicit? [GenContFract.num_eq_conts_a,
    GenContFract.first_cont_eq zeroth_s_eq]

example {K : Type*} {g : GenContFract K} [DivisionRing K]
    {gp : GenContFract.Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by
  simp_explicit [
    GenContFract.num_eq_conts_a,
    GenContFract.first_cont_eq zeroth_s_eq
  ]

private theorem alternate_add_zero (n : Nat) : n + 0 = n := Nat.add_zero n
attribute [local simp 2000] alternate_add_zero

/-- Replay ignores the higher-priority local simp lemma above. -/
example (n : Nat) : n + 0 = n := by
  simp_explicit [
    add_zero
  ]

/-- A stale traversal position is rejected instead of initiating a search. -/
example (n : Nat) : n + 0 = n := by
  fail_if_success
    simp_explicit [
      10 => add_zero
    ]
  simp_explicit [
    11 => add_zero
  ]

example {R : Type*} [Semiring R] (x : DualNumber R) :
    Commute DualNumber.eps x := by
  ext <;> simp_explicit?

example {R : Type*} [Semiring R] (x : DualNumber R) :
    Commute DualNumber.eps x := by
  ext
  · simp_explicit [
      TrivSqZeroExt.fst_mul,
      DualNumber.fst_eps,
      zero_mul,
      TrivSqZeroExt.fst_mul,
      mul_zero
    ]
  · simp_explicit [
      TrivSqZeroExt.snd_mul,
      DualNumber.fst_eps,
      smul_eq_mul,
      zero_mul,
      DualNumber.snd_eps,
      MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op,
      one_mul,
      zero_add,
      TrivSqZeroExt.snd_mul,
      smul_eq_mul,
      mul_one,
      MulOpposite.op_zero,
      zero_smul,
      add_zero
    ]
