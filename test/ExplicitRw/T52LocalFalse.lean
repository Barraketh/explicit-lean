import ExplicitLean.ExplicitRw
import Mathlib.Logic.Function.Defs

namespace ExplicitRwTest.T52

theorem local_false_bool_replay {α β : Type*} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β] {f : α → β} (I : Function.Injective f)
    {a b : α} : (f a == f b) = (a == b) := by
  by_cases h : a == b
  · exact Bool.eq_iff_iff.mpr ⟨
      fun h' => beq_iff_eq.mpr ((I.eq_iff).mp (beq_iff_eq.mp h')),
      fun h' => beq_iff_eq.mpr ((I.eq_iff).mpr (beq_iff_eq.mp h'))⟩
  · explicit_rw [prop_false h at [1], beq_eq_false_iff_ne at [], ne_eq at []]
    intro h'
    apply h
    exact beq_iff_eq.mpr ((I.eq_iff).mp h')

end ExplicitRwTest.T52
