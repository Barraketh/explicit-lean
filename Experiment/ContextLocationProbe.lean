import ExplicitLean.SimpExplicit
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.DropRight

namespace ContextLocationProbe

example (n : Nat) (hAdd : n + 0 = n) (hMul : n * 1 = n) : n = n := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, Nat.mul_one, eq_self] at hAdd hMul ⊢

example (n : Nat) (hAdd : n + 0 = n) (hMul : n * 1 = n) : n = n := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, Nat.mul_one, eq_self] at hMul hAdd ⊢

example (n : Nat) (h : n + 0 = n) (k : h = h) : n = n := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, eq_self] at h k
  rfl

example (n : Nat) : n = n := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [eq_self] at ⊢

example (n : Nat) (h : n + 0 = n) : n = n := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? [Nat.add_zero, eq_self] at *

example (h : False) : True := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? only [] at h

example (h : True) : True := by
  set_option explicitLean.simpExplicit.report true in
    simp_explicit? only [] at h
  trivial

example {α : Type*} (l : List α) (n : ℕ) :
    l.rtake n = List.reverse (l.reverse.take n) := by
  rw [List.rtake]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · exact List.drop_length
    · have h_explicit_1 : True := True.intro
      set_option explicitLean.simpExplicit.report true in
        simp_explicit? [List.drop_append, IH] at *

end ContextLocationProbe
