-- A macro whose expansion is `by simp`: the identifier is not admitted by the
-- grammar, so it never reaches macro expansion.
import ExplicitLean.ExplicitRw
macro "SmuggleSimp" : term => `(by simp)
example (a b : Nat) (h : a = b) : a + 0 = b := by
  explicit_rw [h at [0, 1, 0, 1]] then exact SmuggleSimp
