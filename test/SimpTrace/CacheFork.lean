import ExplicitLean.SimpTrace

namespace ExplicitLean.SimpTrace.CacheFork

-- Two occurrences of the same conditional redex exercise cache hit re-rooting.
example (p : Prop) [Decidable p] (h : p) : (if p then 1 else 2) = 1 := by
  simp_trace [h]

example (p : Prop) [Decidable p] (h : p) :
    (dite p (fun _ => 1) (fun _ => 2)) = 1 := by
  simp_trace [h]

-- The second tuple component is the same expression under a different root;
-- the cache hit must replay the first component's provenance at `[1]`.
example (p : Prop) [Decidable p] (h : p) :
    (if p then 1 else 2, if p then 1 else 2) = (1, 1) := by
  simp_trace [h]

-- The same conditional through the explicit no-memoization path must preserve
-- the result and provenance shape.
example (p : Prop) [Decidable p] (h : p) : (if p then 1 else 2) = 1 := by
  simp_trace (config := { memoize := false }) [h]

-- Contextual/new-lemma scopes exercise the paired fresh-cache lifecycle.
example (p : Prop) [Decidable p] (h : p) : (if p then 1 else 2) = 1 := by
  simp_trace +contextual [h]

-- The recursive default discharger uses the same forked entry point.
example (p : Prop) [Decidable p] (h : p) : (if p then 1 else 2) = 1 := by
  simp_trace (discharger := assumption) [h]

-- Logic.Basic's apply_dite₂ shape: distinct dîtes share a condition, so the
-- second conditional must still carry its own operational provenance.
example (f : Nat → Nat → Nat) (p : Prop) [Decidable p]
    (a b c d : Nat) :
    f (dite p (fun _ => a) (fun _ => b))
      (dite p (fun _ => c) (fun _ => d)) =
      dite p (fun _ => f a c) (fun _ => f b d) := by
  by_cases hp : p <;> simp_trace [hp]

example {α β γ : Sort _} (f : α → β → γ) (p : Prop) [Decidable p]
    (a : p → α) (b : ¬p → α) (c : p → β) (d : ¬p → β) :
    f (dite p a b) (dite p c d) = dite p (fun h => f (a h) (c h))
      (fun h => f (b h) (d h)) := by
  by_cases hp : p <;> simp_trace [hp]

end ExplicitLean.SimpTrace.CacheFork
