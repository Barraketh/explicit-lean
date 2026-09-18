/- Focused recorder fixture for T35's dependent-forall transport event. -/
import ExplicitLean.SimpTrace

namespace ExplicitLean.SimpTrace.T35

theorem body_transport (A : Prop) (B C : A → Prop)
    (hA : A = True) (hBC : ∀ x : A, B x = C x) :
    (∀ x : A, B x) = (∀ x : A, C x) := by
  simp_trace [hA, hBC] =>trace "test/SimpTrace/meas_out/T35DependentTransport.json"

end ExplicitLean.SimpTrace.T35
