-- The `with` clause is a closed set too: a simp-family tactic there is refused
-- by the parser, exactly as in `then` and `eq ... by`.
import ExplicitLean.ExplicitRw
import Mathlib.Algebra.Order.Group.Nat
example (n : Nat) (hn : 5 ≤ n) : (n - 5) + 5 = n := by
  explicit_rw [Nat.sub_add_cancel _ at [0, 1] with [simp]]
