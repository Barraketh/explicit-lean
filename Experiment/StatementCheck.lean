import Mathlib.SetTheory.Cardinal.NatCount
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Data.List.Range
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.Divisors

open Lean Elab Command

namespace StatementProbe

axiom Nat_count_le_cardinal {p : ℕ → Prop} [decidablePredP : DecidablePred p] (n : ℕ) :
    (Nat.count p n : Cardinal) ≤ Cardinal.mk { k | p k }

axiom Nat_count_le_setENCard {p : ℕ → Prop} [decidablePredP : DecidablePred p] (n : ℕ) :
    Nat.count p n ≤ Set.encard { k | p k }

axiom Nat_count_le_setNCard {p : ℕ → Prop} [decidablePredP : DecidablePred p] (n : ℕ)
    (h : { k | p k }.Finite) : Nat.count p n ≤ Set.ncard { k | p k }

axiom DualNumber_commute_eps_left {R : Type*} [semiringR : Semiring R]
    (x : DualNumber R) : Commute DualNumber.eps x

axiom DualNumber_commute_eps_right {R : Type*} [semiringR : Semiring R]
    (x : DualNumber R) : Commute x DualNumber.eps

axiom DualNumber_ringHom_ext {R : Type*} [commSemiringR : CommSemiring R]
    {R' : Type*} [commSemiringR' : CommSemiring R'] {f g : DualNumber R →+* R'}
    (h₀ : f.comp (algebraMap R (DualNumber R)) = g.comp (algebraMap R (DualNumber R)))
    (hε : f DualNumber.eps = g DualNumber.eps) : f = g

axiom DualNumber_range_lift {R : Type*} {B : Type*} {A : Type*}
    [commSemiringR : CommSemiring R] [semiringA : Semiring A] [semiringB : Semiring B]
    [algebraRA : Algebra R A] [algebraRB : Algebra R B]
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (DualNumber.lift fe).range = fe.1.1.range ⊔ Algebra.adjoin R {fe.1.2}

axiom GenContFract_first_num_eq {K : Type*} {g : GenContFract K}
    [divisionRingK : DivisionRing K] {gp : GenContFract.Pair K}
    (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a

axiom GenContFract_terminatedAt_iff_s_terminatedAt {α : Type*}
    {g : GenContFract α} {n : ℕ} : g.TerminatedAt n ↔ g.s.TerminatedAt n

axiom GenContFract_partNum_none_iff_s_none {α : Type*}
    {g : GenContFract α} {n : ℕ} :
    g.partNums.get? n = none ↔ g.s.get? n = none

axiom List_isChain_range (r : ℕ → ℕ → Prop) (n : ℕ) :
    List.IsChain r (List.range n) ↔ ∀ m < n - 1, r m m.succ

axiom List_ranges_disjoint (l : List ℕ) :
    List.Pairwise List.Disjoint (List.ranges l)

axiom TopologicalSpace_ext_iff {X : Type*} {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ s, @IsOpen X t s ↔ @IsOpen X t' s

axiom IsOpen_union {X : Type*} {s₁ s₂ : Set X}
    [topologicalSpaceX : TopologicalSpace X]
    (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂)

axiom isOpen_iff_of_cover {X : Type*} {α : Type*} {s : Set X}
    [topologicalSpaceX : TopologicalSpace X] {f : α → Set X}
    (ho : ∀ i, IsOpen (f i)) (hU : (⋃ i, f i) = Set.univ) :
    IsOpen s ↔ ∀ i, IsOpen (f i ∩ s)

axiom Set_Finite_isOpen_sInter {X : Type*}
    [topologicalSpaceX : TopologicalSpace X] {s : Set (Set X)}
    (hs : s.Finite) (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋂₀ s)

axiom Nat_divisor_le {n m : ℕ} : n ∈ Nat.divisors m → n ≤ m

axiom Nat_card_divisors_le_self (n : ℕ) : (Nat.divisors n).card ≤ n

axiom Nat_divisors_subset_of_dvd {n m : ℕ}
    (hzero : n ≠ 0) (h : m ∣ n) : Nat.divisors m ⊆ Nat.divisors n

end StatementProbe

/-- Compare theorem types modulo binder names. Top-level binder annotations are
checked separately because `Expr.eqv` deliberately ignores them. -/
private partial def sameTheoremType : Expr → Expr → Bool
  | .forallE _ lhsType lhsBody lhsInfo, .forallE _ rhsType rhsBody rhsInfo =>
      lhsInfo == rhsInfo && lhsType.eqv rhsType && sameTheoremType lhsBody rhsBody
  | lhs, rhs => lhs.eqv rhs

private def checkSameStatement (original probe : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some originalInfo := env.find? original
    | throwError "unknown original declaration '{original}'"
  let some probeInfo := env.find? probe
    | throwError "unknown probe declaration '{probe}'"
  unless originalInfo.levelParams.length = probeInfo.levelParams.length do
    throwError "universe-parameter count changed for '{original}'"
  let levels := originalInfo.levelParams.mapIdx fun index _ =>
    Level.param <| Name.mkSimple s!"statement_check_u_{index}"
  let originalType := originalInfo.type.instantiateLevelParams originalInfo.levelParams levels
  let probeType := probeInfo.type.instantiateLevelParams probeInfo.levelParams levels
  unless sameTheoremType originalType probeType do
    throwError "statement changed for '{original}'"

run_cmd checkSameStatement `Nat.count_le_cardinal `StatementProbe.Nat_count_le_cardinal
run_cmd checkSameStatement `Nat.count_le_setENCard `StatementProbe.Nat_count_le_setENCard
run_cmd checkSameStatement `Nat.count_le_setNCard `StatementProbe.Nat_count_le_setNCard
run_cmd checkSameStatement `DualNumber.commute_eps_left `StatementProbe.DualNumber_commute_eps_left
run_cmd checkSameStatement `DualNumber.commute_eps_right `StatementProbe.DualNumber_commute_eps_right
run_cmd checkSameStatement `DualNumber.ringHom_ext `StatementProbe.DualNumber_ringHom_ext
run_cmd checkSameStatement `DualNumber.range_lift `StatementProbe.DualNumber_range_lift
run_cmd checkSameStatement `GenContFract.first_num_eq `StatementProbe.GenContFract_first_num_eq
run_cmd checkSameStatement `GenContFract.terminatedAt_iff_s_terminatedAt `StatementProbe.GenContFract_terminatedAt_iff_s_terminatedAt
run_cmd checkSameStatement `GenContFract.partNum_none_iff_s_none `StatementProbe.GenContFract_partNum_none_iff_s_none
run_cmd checkSameStatement `List.isChain_range `StatementProbe.List_isChain_range
run_cmd checkSameStatement `List.ranges_disjoint `StatementProbe.List_ranges_disjoint
run_cmd checkSameStatement `TopologicalSpace.ext_iff `StatementProbe.TopologicalSpace_ext_iff
run_cmd checkSameStatement `IsOpen.union `StatementProbe.IsOpen_union
run_cmd checkSameStatement `isOpen_iff_of_cover `StatementProbe.isOpen_iff_of_cover
run_cmd checkSameStatement `Set.Finite.isOpen_sInter `StatementProbe.Set_Finite_isOpen_sInter
run_cmd checkSameStatement `Nat.divisor_le `StatementProbe.Nat_divisor_le
run_cmd checkSameStatement `Nat.card_divisors_le_self `StatementProbe.Nat_card_divisors_le_self
run_cmd checkSameStatement `Nat.divisors_subset_of_dvd `StatementProbe.Nat_divisors_subset_of_dvd
