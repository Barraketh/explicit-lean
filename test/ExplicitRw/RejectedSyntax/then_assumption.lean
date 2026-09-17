-- Bare `assumption` searches the whole local context, so it can close the goal
-- with a different hypothesis than the trace recorded. The spec writes
-- `assumption:<name>`; render that as `exact <name>`.
import ExplicitLean.ExplicitRw
example (a b : Nat) (h : a = b) (hb : b + 0 = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then assumption
