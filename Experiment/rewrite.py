#!/usr/bin/env python3
"""Create body-rewritten copies of the representative Mathlib modules."""

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MATHLIB = ROOT / ".lake" / "packages" / "mathlib"
EXPORTS = ROOT / ".lake" / "proof-term-probe"
OUTPUT = EXPORTS / "rewritten"
PLACEHOLDER = re.compile(r"(?<![\w])_(?![\w])")
ORIGINAL_BODY = re.compile(r":=\s*(.*)\Z", re.DOTALL)


CASES = {
    "Mathlib/SetTheory/Cardinal/NatCount.lean": [
        (
            "Nat_count_le_cardinal",
            """theorem count_le_cardinal : (count p n : Cardinal) ≤ Cardinal.mk { k | p k } := by
  rw [count_eq_card_fintype, ← Cardinal.mk_fintype]
  exact Cardinal.mk_subtype_mono fun x hx ↦ hx.2""",
            """theorem count_le_cardinal {p : ℕ → Prop}
    [decidablePredP : DecidablePred p] (n : ℕ) :
    (count p n : Cardinal) ≤ Cardinal.mk { k | p k } :=
{body}""",
        ),
        (
            "Nat_count_le_setENCard",
            """theorem count_le_setENCard : count p n ≤ Set.encard { k | p k } := by
  simp only [Set.encard, ENat.card, Set.coe_setOf, Cardinal.natCast_le_toENat]
  exact Nat.count_le_cardinal n""",
            """theorem count_le_setENCard {p : ℕ → Prop} [decidablePredP : DecidablePred p] (n : ℕ) :
    count p n ≤ Set.encard { k | p k } :=
{body}""",
        ),
        (
            "Nat_count_le_setNCard",
            """theorem count_le_setNCard (h : { k | p k }.Finite) : count p n ≤ Set.ncard { k | p k } := by
  rw [Set.ncard_def, ← ENat.coe_le_coe, ENat.coe_toNat (by simpa)]
  exact count_le_setENCard n""",
            """theorem count_le_setNCard {p : ℕ → Prop}
    [decidablePredP : DecidablePred p] (n : ℕ)
    (h : { k | p k }.Finite) : count p n ≤ Set.ncard { k | p k } :=
{body}""",
        ),
    ],
    "Mathlib/Algebra/DualNumber.lean": [
        (
            "DualNumber_commute_eps_left",
            """theorem commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x := by
  ext <;> simp""",
            """theorem commute_eps_left {R : Type*} [semiringR : Semiring R] (x : DualNumber R) :
    Commute ε x :=
{body}""",
        ),
        (
            "DualNumber_commute_eps_right",
            """theorem commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε := (commute_eps_left x).symm""",
            """theorem commute_eps_right {R : Type*} [semiringR : Semiring R] (x : DualNumber R) :
    Commute x ε :=
{body}""",
        ),
        (
            "DualNumber_ringHom_ext",
            """lemma ringHom_ext {R' : Type*} [CommSemiring R'] {f g : R[ε] →+* R'}
    (h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε]))
    (hε : f ε = g ε) : f = g := by
  letI : Algebra R R' := by
    letI := f.toAlgebra
    exact Algebra.compHom _ (algebraMap R R[ε])
  let f' : R[ε] →ₐ[R] R' :=
    { toRingHom := f
      commutes' _ := rfl }
  let g' : R[ε] →ₐ[R] R' :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  exact congr_arg AlgHom.toRingHom (show f' = g' from algHom_ext hε)""",
            """lemma ringHom_ext {R : Type*} [commSemiringR : CommSemiring R]
    {R' : Type*} [commSemiringR' : CommSemiring R'] {f g : R[ε] →+* R'}
    (h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε]))
    (hε : f ε = g ε) : f = g :=
{body}""",
        ),
        (
            "DualNumber_range_lift",
            """theorem range_lift
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (lift fe).range = fe.1.1.range ⊔ R[fe.1.2] := by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_eps, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, Set.image_singleton, lift_apply_eps, lift_comp_inlHom,
    Algebra.map_top]""",
            """theorem range_lift {R : Type*} {B : Type*} {A : Type*}
    [commSemiringR : CommSemiring R] [semiringA : Semiring A] [semiringB : Semiring B]
    [algebraRA : Algebra R A] [algebraRB : Algebra R B]
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (lift fe).range = fe.1.1.range ⊔ R[fe.1.2] :=
{body}""",
        ),
    ],
    "Mathlib/Algebra/ContinuedFractions/Translations.lean": [
        (
            "GenContFract_terminatedAt_iff_s_terminatedAt",
            """theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := by rfl""",
            """theorem terminatedAt_iff_s_terminatedAt {α : Type*}
    {g : GenContFract α} {n : ℕ} : g.TerminatedAt n ↔ g.s.TerminatedAt n :=
{body}""",
        ),
        (
            "GenContFract_partNum_none_iff_s_none",
            """theorem partNum_none_iff_s_none : g.partNums.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.get? n <;> simp [partNums, s_nth_eq]""",
            """theorem partNum_none_iff_s_none {α : Type*}
    {g : GenContFract α} {n : ℕ} :
    g.partNums.get? n = none ↔ g.s.get? n = none :=
{body}""",
        ),
        (
            "GenContFract_first_num_eq",
            """theorem first_num_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by simp [num_eq_conts_a, first_cont_eq zeroth_s_eq]""",
            """theorem first_num_eq {K : Type*} {g : GenContFract K}
    [divisionRingK : DivisionRing K] {gp : Pair K}
    (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a :=
{body}""",
        ),
    ],
    "Mathlib/Data/List/Range.lean": [
        (
            "List_isChain_range",
            """theorem isChain_range (r : ℕ → ℕ → Prop) (n : ℕ) :
    IsChain r (range n) ↔ ∀ m < n - 1, r m m.succ := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp only [range_succ, Nat.add_one_sub_one, Nat.lt_sub_iff_add_lt] at hn ⊢
    cases n with
    | zero => simp
    | succ n =>
      simp only [range_succ, Nat.add_lt_add_iff_right, succ_eq_add_one, append_assoc, cons_append,
        nil_append, isChain_append_cons_cons, IsChain.singleton, and_true] at hn ⊢
      rw [hn, forall_lt_succ_right]""",
            """theorem isChain_range (r : ℕ → ℕ → Prop) (n : ℕ) :
    IsChain r (range n) ↔ ∀ m < n - 1, r m m.succ :=
{body}""",
        ),
        (
            "List_ranges_disjoint",
            """theorem ranges_disjoint (l : List ℕ) :
    Pairwise Disjoint (ranges l) := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rw [mem_range] at hu
      lia
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel""",
            """theorem ranges_disjoint (l : List ℕ) :
    Pairwise Disjoint (ranges l) :=
{body}""",
        ),
    ],
    "Mathlib/Topology/Basic.lean": [
        (
            "TopologicalSpace_ext_iff",
            """protected theorem TopologicalSpace.ext_iff {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ s, IsOpen[t] s ↔ IsOpen[t'] s :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩""",
            """protected theorem TopologicalSpace.ext_iff {X : Type u}
    {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ s, IsOpen[t] s ↔ IsOpen[t'] s :=
{body}""",
        ),
        (
            "IsOpen_union",
            """theorem IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]; exact isOpen_iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)""",
            """theorem IsOpen.union {X : Type u} {s₁ s₂ : Set X}
    [topologicalSpaceX : TopologicalSpace X]
    (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂) :=
{body}""",
        ),
        (
            "isOpen_iff_of_cover",
            """lemma isOpen_iff_of_cover {f : α → Set X} (ho : ∀ i, IsOpen (f i)) (hU : (⋃ i, f i) = univ) :
    IsOpen s ↔ ∀ i, IsOpen (f i ∩ s) := by
  refine ⟨fun h i ↦ (ho i).inter h, fun h ↦ ?_⟩
  rw [← s.inter_univ, inter_comm, ← hU, iUnion_inter]
  exact isOpen_iUnion fun i ↦ h i""",
            """lemma isOpen_iff_of_cover {X : Type u} {α : Type*} {s : Set X}
    [topologicalSpaceX : TopologicalSpace X] {f : α → Set X}
    (ho : ∀ i, IsOpen (f i)) (hU : (⋃ i, f i) = univ) :
    IsOpen s ↔ ∀ i, IsOpen (f i ∩ s) :=
{body}""",
        ),
        (
            "Set_Finite_isOpen_sInter",
            """theorem Set.Finite.isOpen_sInter {s : Set (Set X)} (hs : s.Finite) (h : ∀ t ∈ s, IsOpen t) :
    IsOpen (⋂₀ s) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => rw [sInter_empty]; exact isOpen_univ
  | insert _ _ ih =>
    simp only [sInter_insert, forall_mem_insert] at h ⊢
    exact h.1.inter (ih h.2)""",
            """theorem Set.Finite.isOpen_sInter {X : Type u}
    [topologicalSpaceX : TopologicalSpace X] {s : Set (Set X)}
    (hs : s.Finite) (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋂₀ s) :=
{body}""",
        ),
    ],
    "Mathlib/NumberTheory/Divisors.lean": [
        (
            "Nat_divisor_le",
            """theorem divisor_le {m : ℕ} : n ∈ divisors m → n ≤ m := by
  rcases m with - | m
  · simp
  · simp only [mem_divisors, Nat.succ_ne_zero m, and_true, Ne, not_false_iff]
    exact Nat.le_of_dvd (Nat.succ_pos m)""",
            """theorem divisor_le {n m : ℕ} : n ∈ divisors m → n ≤ m :=
{body}""",
        ),
        (
            "Nat_card_divisors_le_self",
            """theorem card_divisors_le_self (n : ℕ) : #n.divisors ≤ n := calc
  _ ≤ #(Ico 1 (n + 1)) := by
    apply card_le_card
    simp only [divisors, filter_subset]
  _ = n := by rw [card_Ico, add_tsub_cancel_right]""",
            """theorem card_divisors_le_self (n : ℕ) : #n.divisors ≤ n :=
{body}""",
        ),
        (
            "Nat_divisors_subset_of_dvd",
            """theorem divisors_subset_of_dvd {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
  Finset.subset_iff.2 fun _x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩""",
            """theorem divisors_subset_of_dvd {n m : ℕ}
    (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
{body}""",
        ),
    ],
}


def original_body_comment(declaration: str, stem: str) -> str:
    """Recover the source body and format it beside its generated replacement."""
    match = ORIGINAL_BODY.search(declaration)
    if match is None:
        raise RuntimeError(f"could not find original body for {stem}")
    return f"/-\nOriginal body:\n{match.group(1)}\n-/"


def main() -> None:
    for relative_path, replacements in CASES.items():
        source = MATHLIB / relative_path
        text = source.read_text(encoding="utf-8")
        for stem, original, replacement in replacements:
            occurrences = text.count(original)
            if occurrences != 1:
                raise RuntimeError(
                    f"expected one declaration block for {stem}, found {occurrences}"
                )
            body = (EXPORTS / f"{stem}.shared-body.lean").read_text(
                encoding="utf-8"
            ).rstrip("\n")
            if PLACEHOLDER.search(body):
                raise RuntimeError(f"generated body for {stem} contains an _ placeholder")
            if "✝" in body:
                raise RuntimeError(f"generated body for {stem} contains an inaccessible name")
            comparison = f"{original_body_comment(original, stem)}\n{body}"
            text = text.replace(original, replacement.replace("{body}", comparison), 1)

        destination = OUTPUT / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text, encoding="utf-8")
        print(destination.relative_to(ROOT))


if __name__ == "__main__":
    main()
