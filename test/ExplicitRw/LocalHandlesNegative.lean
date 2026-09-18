import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.LocalHandlesNegative

/-- error: explicit_rw: local_ref 99 is outside the current local context -/
#guard_msgs in
example (a : Nat) : a = a := by
  explicit_rw [local_ref 99 at [0, 1]]

/-- error: explicit_rw: local_ref 0 names an auxiliary declaration, not a local hypothesis -/
#guard_msgs in
example (a : Nat) : a = a := by
  explicit_rw [local_ref 0 at [0, 1]]

/-- error: explicit_rw: local_ref 3: projection `.0` is invalid; projections are numbered from `.1` -/
#guard_msgs in
example {a b : Prop} (h : a ∧ b) : a := by
  explicit_rw [] then exact local_ref 3 .0

/-- error: explicit_rw: local_ref 3: projection .3 is out of bounds for And -/
#guard_msgs in
example {a b : Prop} (h : a ∧ b) : a := by
  explicit_rw [] then exact local_ref 3 .3

/--
error: Type mismatch
  h.right
has type
  b
but is expected to have type
  a
-/
#guard_msgs in
example {a b : Prop} (h : a ∧ b) : a := by
  explicit_rw [] then exact local_ref 3 .2

/-- error: explicit_rw: introduced_ref 7 is unknown in this side proof -/
#guard_msgs in
example (p : Prop) : p → p := by
  explicit_rw [] then exact introduced_ref 7

/-- error: explicit_rw: step 1: the closing `then` proof duplicates introduced handle 0. -/
#guard_msgs in
example (p q : Prop) : p → q → p := by
  explicit_rw [] then intro_ref 0 ; intro_ref 0 ; exact introduced_ref 0

theorem proposition_with_side {p q : Prop} (h : p = q) : p = q := h

theorem proposition_false_with_side {p : Prop} (h : p → False) : ¬p := h

/-- error: explicit_rw: introduced_ref 1 is unknown in this side proof -/
#guard_msgs in
example {p q : Prop} : (p = q) → (p = q) = True := by
  explicit_rw [] then intro_ref 0 ; explicit_rw
    [prop_true proposition_with_side at [0, 1] with [exact introduced_ref 1]] then rfl

/-- error: explicit_rw: introduced_ref 1 is unknown in this side proof -/
#guard_msgs in
example {p : Prop} : (p → False) → p = False := by
  explicit_rw [] then intro_ref 0 ; explicit_rw
    [prop_false proposition_false_with_side at [0, 1] with [exact introduced_ref 1]] then rfl

/-- error: explicit_rw: local_ref requires a canonical decimal index -/
#guard_msgs in
example (a : Nat) : a = a := by
  explicit_rw [local_ref 1_0 at [0, 1]]

/-- error: explicit_rw: local_ref 999999999999999999999999999999 is outside the current local context -/
#guard_msgs in
example (a : Nat) : a = a := by
  explicit_rw [local_ref 999999999999999999999999999999 at [0, 1]]

/-- error: explicit_rw: introduced_ref handle requires a canonical decimal numeral -/
#guard_msgs in
example (p : Prop) : p → p := by
  explicit_rw [] then exact introduced_ref 1_0

/-- error: explicit_rw: intro_ref handle requires a canonical decimal numeral -/
#guard_msgs in
example (p : Prop) : p → p := by
  explicit_rw [] then intro_ref 1_0 ; exact introduced_ref 0

end ExplicitRwTest.LocalHandlesNegative
