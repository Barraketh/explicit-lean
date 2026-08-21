import ExplicitLean.SimpExplicit
import Mathlib.Data.List.DropRight

namespace LocalRenameProbe

/- The existing printable local deliberately occupies the first generated
   certificate name.  The n introduced by cases is macro-scoped, so the
   recorder must select it in context order and skip to h_explicit_2. -/
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
        simp_explicit? [List.drop_append, IH]

end LocalRenameProbe
