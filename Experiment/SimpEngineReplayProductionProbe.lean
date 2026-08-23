import Mathlib.Data.List.DropRight
import ExplicitLean.SimpEngine.Replay

variable {alpha : Type*}

namespace List

example (l : List alpha) (n : Nat) : l.rdrop n = reverse (l.reverse.drop n) := by
  rw [rdrop]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp_engine_replay
  | append_singleton xs x ih =>
    cases n
    · simp_engine_replay [take_length_add_append]
    · simp [take_append, ih] -- `Nat.reduceSubDiff` remains in the simproc workstream.

example (p : alpha → Bool) (l : List alpha) :
    rtakeWhile p l = [] ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  induction l using List.reverseRecOn <;> simp_engine_replay [rtakeWhile]

end List
