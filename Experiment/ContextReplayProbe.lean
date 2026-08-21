import ExplicitLean.SimpExplicit
import Mathlib.Data.Nat.Basic

namespace ContextReplayProbe

example (n : Nat) (h : n + 0 = n) : n + 0 = n := by
  simp_explicit_context [at h => [Nat.add_zero, eq_self], at target => [Nat.add_zero, eq_self]]

example (n : Nat) (hAdd : n + 0 = n) (hMul : n * 1 = n) : n + 0 = n := by
  -- This is the closed, explicitly expanded form of `at *`.
  simp_explicit_context [
    at hAdd => [Nat.add_zero, eq_self],
    at hMul => [Nat.mul_one, eq_self],
    at target => [Nat.add_zero, eq_self]
  ]

example (n : Nat) (hAdd : n + 0 = n) (hMul : n * 1 = n) : n + 0 = n := by
  simp_explicit_context [
    at hMul => [Nat.mul_one, eq_self],
    at hAdd => [Nat.add_zero, eq_self],
    at target => [Nat.add_zero, eq_self]
  ]

example (n : Nat) (h : n + 0 = n) (k : h = h) : n = n := by
  simp_explicit_context [
    at h => [Nat.add_zero],
    at k => [eq_self],
    at target => []
  ]
  have h_new : n = n := h
  have k_new : True := k
  rfl

example (p : Prop) (n : Nat) (hp : p ∧ (n + 0 = n)) : p := by
  have h_explicit_1 : True := True.intro
  rcases hp with ⟨h, _⟩
  rename_i h_explicit_2
  simp_explicit_context [
    at h_explicit_2 => [Nat.add_zero, eq_self],
    at target => []
  ]
  exact h


end ContextReplayProbe
