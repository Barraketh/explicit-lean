import Mathlib.Probability.Kernel.CondDistrib
import ExplicitLean.SimpTrace

/-! Cache-root regressions for captured dependent-congruence event slices. -/

open MeasureTheory Set Filter TopologicalSpace ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ExplicitLean.SimpTrace.T77CongrRootCache

/- Reproduction of the `Mathlib.Probability.Kernel.CondDistrib` worker site
   (command ordinal 26/site 0): the negative-measurability branch simplifies
   `Measure.map X μ` under a dependent congruence. -/
example {α β Ω : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    {μ : Measure α} [IsFiniteMeasure μ] {X : α → β} {Y : α → Ω}
    {κ : Kernel β Ω} [IsFiniteKernel κ]
    (hY : AEMeasurable Y μ)
    (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  by_cases hX : AEMeasurable X μ
  swap
  · simp_trace [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  suffices condDistrib (hY.mk Y) (hX.mk X) μ =ᵐ[μ.map (hX.mk X)] κ by
    rwa [Measure.map_congr hX.ae_eq_mk, condDistrib_congr hY.ae_eq_mk hX.ae_eq_mk]
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hX.measurable_mk hY.measurable_mk ((Eq.trans ?_ hκ).trans ?_)
  · refine Measure.map_congr ?_
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk] with a haX haY using by rw [haX, haY]
  · rw [Measure.map_congr hX.ae_eq_mk]

/- Synthetic same-redex cache-hit and no-memoization controls. -/
example (n : Nat) : (n + 0, n + 0) = (n, n) := by
  simp_trace [Nat.add_zero]

example (n : Nat) : (n + 0, n + 0) = (n, n) := by
  simp_trace (config := { memoize := false }) [Nat.add_zero]

end ExplicitLean.SimpTrace.T77CongrRootCache
