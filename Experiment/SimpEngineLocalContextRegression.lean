import ExplicitLean.SimpEngine.Boundary
class ReviewC : Prop where
  h : True
def ReviewHiddenC : Prop := ReviewC
inductive ReviewBox : Prop where | intro
theorem review_box [ReviewC] : ReviewBox ↔ True := ⟨fun _ => .intro, fun _ => .intro⟩
example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  simp only [ReviewHiddenC, review_box] at h k
  exact k
example (h : ReviewHiddenC) (k : ReviewBox) : ReviewBox := by
  simp_engine_boundary_probe only [ReviewHiddenC, review_box] at h k
  exact k
