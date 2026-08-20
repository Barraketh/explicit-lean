import Mathlib.SetTheory.Cardinal.NatCount
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.ContinuedFractions.Translations

open Lean Elab Command

namespace StatementProbe

axiom Nat_count_le_setENCard {p : ℕ → Prop} [decidablePredP : DecidablePred p] (n : ℕ) :
    Nat.count p n ≤ Set.encard { k | p k }

axiom DualNumber_commute_eps_left {R : Type*} [semiringR : Semiring R]
    (x : DualNumber R) : Commute DualNumber.eps x

axiom DualNumber_range_lift {R : Type*} {B : Type*} {A : Type*}
    [commSemiringR : CommSemiring R] [semiringA : Semiring A] [semiringB : Semiring B]
    [algebraRA : Algebra R A] [algebraRB : Algebra R B]
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (DualNumber.lift fe).range = fe.1.1.range ⊔ Algebra.adjoin R {fe.1.2}

axiom GenContFract_first_num_eq {K : Type*} {g : GenContFract K}
    [divisionRingK : DivisionRing K] {gp : GenContFract.Pair K}
    (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a

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

run_cmd checkSameStatement `Nat.count_le_setENCard `StatementProbe.Nat_count_le_setENCard
run_cmd checkSameStatement `DualNumber.commute_eps_left `StatementProbe.DualNumber_commute_eps_left
run_cmd checkSameStatement `DualNumber.range_lift `StatementProbe.DualNumber_range_lift
run_cmd checkSameStatement `GenContFract.first_num_eq `StatementProbe.GenContFract_first_num_eq
