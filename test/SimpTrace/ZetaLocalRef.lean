import ExplicitLean.SimpTrace

namespace ExplicitLean.SimpTrace.ZetaLocalRef

/--
A named zeta-delta step identifies the exact local let by context index.  The
body is retained only as diagnostic `after` text; replay uses the indexed local.
-/
example (a : Nat) (P : Nat → Prop) (hP : ∀ n, P n) : True := by
  let g : Nat → Nat := fun s => s + 0
  have hg : P (g a) := hP _
  simp_trace only [g] at hg =>trace ".lake/private/zeta-local-ref/trace.json"
  guard_hyp hg :ₛ P (a + 0)
  exact True.intro

end ExplicitLean.SimpTrace.ZetaLocalRef
