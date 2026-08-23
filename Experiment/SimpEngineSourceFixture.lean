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

example (xs : List Nat) : xs ++ [] = xs := by
  simp only [List.append_nil]

example (a b : Nat) (ha : a = 0) (hb : b = 0) : sourcePairAdd a b = 0 := by
  simp only [sourceTwoPremises, ha, hb]

example (x y : Nat) : x + 0 = x ∧ y + 0 = y := by
  constructor <;> simp only [Nat.add_zero]

example (x : Nat) (h : x + 0 = x) : True := by
  simp only [Nat.add_zero] at h ⊢

example : (20 : Nat) < 30 := by
  simp +decide

example : sourceSeeGroundBox sourceGroundValue := by
  simp (config := { zeta := false }) +ground
  exact sourceSeeGroundValue
