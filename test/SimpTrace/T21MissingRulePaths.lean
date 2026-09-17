module

import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic

/-!
Focused T21 producer fixtures.  These are intentionally separate from the
74-skeleton green gate: the assertions below are inspected by the bounded
T21 check for event-time derivations and stock-result parity.
-/

namespace ExplicitLean.SimpTrace.T21MissingRulePaths

example (p q : Prop) [Decidable p] [Decidable q] (hpq : p = q) :
    (if p then (1 : Nat) else 2) = if q then 1 else 2 := by
  simp_trace [hpq] =>trace "test/SimpTrace/out/t21_ite_congr.json"

example (p : Prop) [Decidable p] (hp : p) :
    (∃ _ : p, True) ↔ True := by
  simp_trace [hp] =>trace "test/SimpTrace/out/t21_exists_prop_congr.json"

end ExplicitLean.SimpTrace.T21MissingRulePaths
