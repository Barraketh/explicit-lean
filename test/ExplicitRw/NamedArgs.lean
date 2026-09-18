import ExplicitLean.ExplicitRw
import Mathlib.Logic.Basic

/-! The source-backed replay path preserves one named implicit binder. -/

namespace ExplicitRwTest.NamedArgs

theorem heq_comm_named {α : Sort} (a : α) : HEq a a := by
  explicit_rw [heq_comm (a := a) at []]
  rfl

end ExplicitRwTest.NamedArgs
