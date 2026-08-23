import ExplicitLean.SimpExplicit
import Mathlib.Algebra.AddConstMap.Basic

namespace AddConstMap

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/- The context-specialized candidate preserves the historical second match;
   the bare generic declaration is rejected by ordered replay. -/
example (f : G →+c[0, 0] H) (x : G) :
    ((fun g : G →+c[0, 0] H =>
        (⟨fun y => -g (-y), fun _ => by simp⟩ : G →+c[0, 0] H))
      ((fun g : G →+c[0, 0] H =>
        (⟨fun y => -g (-y), fun _ => by simp⟩ : G →+c[0, 0] H)) f)) x = f x := by
  simp_explicit [
    reduce beta,
    reduce beta,
    match 2 => AddConstMap.coe_mk,
    reduce beta,
    neg_neg,
    neg_neg,
    AddConstMap.mk_coe
  ]

end AddConstMap
