import ExplicitLean.SimpExplicit
import Mathlib.Data.List.DropRight

namespace LocalRenameProbe

/- The existing printable local deliberately occupies the context-index-based
   name for the macro-scoped n introduced by cases. The recorder must retain
   the exact index and add a deterministic collision suffix. -/
example {α : Type*} (l : List α) (n : ℕ) :
    l.rtake n = List.reverse (l.reverse.take n) := by
  rw [List.rtake]
  induction l using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton xs x IH =>
    cases n
    · exact List.drop_length
    · have h_explicit_8 : True := True.intro
      set_option explicitLean.simpExplicit.report true in
        simp_explicit? [List.drop_append, IH]

end LocalRenameProbe
