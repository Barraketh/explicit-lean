import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.LocalHandles

theorem direct_index (a b : Nat) (h : a = b) : a = b := by
  explicit_rw [local_ref 3 at [0, 1]] then rfl

theorem direct_projection {a b : Prop} (h : a ∧ b) : a := by
  explicit_rw [] then exact local_ref 3 .1

theorem introduced (p : Nat × Nat) : p.1 = p.1 := by
  explicit_rw [] then rfl

theorem introduced_side (p : Prop) : p → p := by
  explicit_rw [] then intro_ref 0 ; exact introduced_ref 0

theorem introduced_nested (p : Prop) : p → p := by
  explicit_rw [] then intro_ref 0 ; explicit_rw [] then exact introduced_ref 0

theorem introduced_rewrite (a b : Nat) : a = b → a = b := by
  explicit_rw [] then intro_ref 0 ; explicit_rw [introduced_ref 0 at [0, 1]] then rfl

theorem inaccessible_index (a b : Nat) : a = b → a = b := by
  intro _
  explicit_rw [] then exact local_ref 3

end ExplicitRwTest.LocalHandles
