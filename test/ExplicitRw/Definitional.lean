/-
Fixtures for the definitional steps (`unfold`, `beta`, `eta`, `proj`, `change`)
and for `eq ... by tac`, the replay form of a simproc-computed equation.

Definitional steps replace the subterm by a definitionally equal one and carry
no proof beyond the defeq check, so the rebuilt goal is closed by `Eq.refl`-like
transport rather than by a congruence proof.
-/
import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.Definitional

/-- A plain definition, so `unfold` has something to delta-reduce. -/
def double (n : Nat) : Nat := n + n

/-! ## An `unfold` step -/

theorem unfold_step (a : Nat) : double a = a + a := by
  explicit_rw [unfold double at [0, 1]]
  guard_target =ₛ a + a = a + a
  rfl

theorem unfold_step_conv (a : Nat) : double a = a + a := by
  conv => lhs; unfold double

/-! ## A `beta` step -/

theorem beta_step (a : Nat) : (fun x => x + 0) a = a := by
  explicit_rw [beta at [0, 1]]
  guard_target =ₛ a + 0 = a
  exact Nat.add_zero a

theorem beta_step_conv (a : Nat) : (fun x => x + 0) a = a := by
  show a + 0 = a
  exact Nat.add_zero a

/-! ## `unfold` and `beta` in one trace

`double a` unfolds to `a + a`; a following `beta` would have nothing to do, so
the second step here is the `eta` form on a separate term instead.
-/

theorem unfold_then_rewrite (a : Nat) : double (a + 0) = a + a := by
  explicit_rw [Nat.add_zero a at [0, 1, 1], unfold double at [0, 1]]
  guard_target =ₛ a + a = a + a
  rfl

/-! ## An `eta` step -/

theorem eta_step (f : Nat → Nat) : (fun x => f x) = f := by
  explicit_rw [eta at [0, 1]]
  guard_target =ₛ f = f
  rfl

/-! ## A `change` step: last-resort definitional replacement -/

theorem change_step (a : Nat) : double a = a + a := by
  explicit_rw [change (a + a) at [0, 1]]
  guard_target =ₛ a + a = a + a
  rfl

/-! ## An `eq ... by rfl` arithmetic step

This is how a simproc-computed equation is replayed: the equation is stated
explicitly and proved by an ordinary tactic, never by the simproc.
-/

theorem eq_by_rfl : (2 + 3) + 1 = 6 := by
  explicit_rw [eq (2 + 3 = 5) by rfl at [0, 1, 0, 1]]
  guard_target =ₛ 5 + 1 = 6
  rfl

theorem eq_by_rfl_conv : (2 + 3) + 1 = 6 := by
  conv => lhs; arg 1; rw [show 2 + 3 = 5 from rfl]

/-- The `decide` variant of the same step kind. -/
theorem eq_by_decide : (2 + 3) * 2 = 10 := by
  explicit_rw [eq ((2 : Nat) + 3 = 5) by decide at [0, 1, 0, 1]]
  guard_target =ₛ 5 * 2 = 10
  rfl

end ExplicitRwTest.Definitional
