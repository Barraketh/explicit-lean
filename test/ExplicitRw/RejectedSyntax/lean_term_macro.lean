-- Macro expansion inside `lean_term` must happen before its term is elaborated.
import ExplicitLean.ExplicitRw

macro "SmuggleSimp" : term => `(by simp)

example (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then exact lean_term(SmuggleSimp)
