module

import Mathlib

/- This `simp only` performs its listed rewrites but intentionally leaves an
   extensionality goal for `congr!`.  Its explicit replacement must preserve
   that exact open final state instead of closing the enclosing tactic body. -/

variable {ι : Type*} {κ : ι → Type*}

example [∀ i, NonUnitalSemiring (κ i)] (x : ∀ i, κ i) :
    IsQuasiregular x ↔ ∀ i, IsQuasiregular (x i) := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toPi κ), Pi.isUnit_iff]
  congr!
