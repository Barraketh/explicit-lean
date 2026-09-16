/-
Fixtures for `explicit_rw`: top-level rewrites, chaining, and `←`.

Each theorem states the goal after the trace with `guard_target` before
closing, and carries the equivalent `conv` proof as a second theorem, as a
cross-check that the positions were understood. Remember that `conv`'s `arg n`
counts *explicit* arguments while `explicit_rw` positions are raw child
indices, so the two paths look different on purpose.
-/
import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.Basic

/-! ## Top-level rewrite then `rfl` -/

theorem top_level (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]]
  guard_target =ₛ b + 0 = b
  rfl

/-- The ordinary-Lean equivalent: `conv` navigates to the same subterm. -/
theorem top_level_conv (a b : Nat) (h : a = b) : a + 0 = b := by
  conv => lhs; arg 1; rw [h]
  rfl

/-! ## Two chained rewrites

The second position is relative to the term the first step produced.
-/

theorem chained (a b c : Nat) (h1 : a = b) (h2 : b = c) : a + 0 = c := by
  explicit_rw [h1 at [0, 1, 0, 1], h2 at [0, 1, 0, 1]]
  guard_target =ₛ c + 0 = c
  rfl

theorem chained_conv (a b c : Nat) (h1 : a = b) (h2 : b = c) : a + 0 = c := by
  conv => lhs; arg 1; rw [h1]; rw [h2]
  rfl

/-! ## A `←` rewrite -/

theorem reverse (a b : Nat) (h : b = a) : a + 0 = b := by
  explicit_rw [← h at [0, 1, 0, 1]]
  guard_target =ₛ b + 0 = b
  rfl

theorem reverse_conv (a b : Nat) (h : b = a) : a + 0 = b := by
  conv => lhs; arg 1; rw [← h]
  rfl

/-! ## The whole location, `at []` -/

theorem whole_location (p q : Prop) (h : p = q) (hp : p) : q := by
  explicit_rw [h at []] at hp
  guard_hyp hp :ₛ q
  exact hp

theorem whole_location_conv (p q : Prop) (h : p = q) (hp : p) : q := by
  conv at hp => rw [h]
  exact hp

/-! ## The optional closing form

`explicit_rw [...] then tac` is sugar for writing `tac` on the next line. It is
accepted only when the trace rewrites the goal.
-/

theorem closing_form (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then rfl

end ExplicitRwTest.Basic
