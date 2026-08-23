module

import Mathlib

opaque sourcePairAdd : Nat → Nat → Nat

axiom sourceTwoPremises {a b : Nat} (ha : a = 0) (hb : b = 0) :
  sourcePairAdd a b = 0

inductive SourceGroundBox where
  | value

opaque sourceSeeGroundBox : SourceGroundBox → Prop

def sourceGroundValue : SourceGroundBox :=
  let box := SourceGroundBox.value
  box

axiom sourceSeeGroundValue : sourceSeeGroundBox .value

opaque SourceUnchanged : Prop

axiom sourceUnchanged : SourceUnchanged

theorem sourceNestedRule (_ : True) (n : Nat) : n + 0 = n :=
  Nat.add_zero n

example (xs : List Nat) : xs ++ [] = xs := by
  simp only [List.append_nil]

example (n : Nat) : n + 0 = n := by
  simp only [sourceNestedRule (by simp)]

example (a b : Nat) (ha : a = 0) (hb : b = 0) : sourcePairAdd a b = 0 := by
  simp only [sourceTwoPremises, ha, hb]

example (x y : Nat) : x + 0 = x ∧ y + 0 = y := by
  constructor <;> simp only [Nat.add_zero]

example (x : Nat) (h : x + 0 = x) : True := by
  simp only [Nat.add_zero] at h ⊢

set_option simprocs false in
example (p : Prop) : p → p := by
  simp +contextual

example : (20 : Nat) < 30 := by
  simp +decide

example : sourceSeeGroundBox sourceGroundValue := by
  simp (config := { zeta := false }) +ground
  exact sourceSeeGroundValue

example : SourceUnchanged := by
  first
  | simp (config := { failIfUnchanged := true }) only
  | exact sourceUnchanged
