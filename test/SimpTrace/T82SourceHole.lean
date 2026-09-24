import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import ExplicitLean.SimpOperations.Recording
import ExplicitLean.ExplicitRw

namespace QuasispectrumRestricts

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]
variable [Algebra R S] {a : A} {f : S → R}
variable [IsScalarTower S A A] [SMulCommClass S A A] [IsScalarTower R S A]

example (h : QuasispectrumRestricts a f) : f '' quasispectrum S a = quasispectrum R a := by
  simp_operations_observe only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']
  exact image h

example (h : QuasispectrumRestricts a f) : f '' quasispectrum S a = quasispectrum R a := by
  explicit_rw_v2 [source_rule lean_term(h.algebraMap_image) variant 0 phase post rev extra 0 at [0, 1, 1] with [], rule _root_.Set.image_image variant 0 phase post fwd extra 0 at [0, 1] with [], congr_rule _root_.Set.image_congr at [0, 1] with [arg 5 intro 2 ; explicit_rw_v2 [source_rule lean_term(h.left_inv _) variant 0 phase post fwd extra 0 at [0, 1] with []] then rfl], rule _root_.Set.image_id' variant 0 phase post fwd extra 0 at [0, 1] with [], rule _root_.eq_self variant 0 phase post fwd extra 0 at [] with []] then true_intro

end QuasispectrumRestricts
