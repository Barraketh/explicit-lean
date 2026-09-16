/-
Negative fixtures: every failure mode must produce a clear error naming the step
index and the reason. There is no fallback, no search and no retry at other
positions, so each of these fails rather than quietly succeeding somewhere else.

The expected messages are pinned with `#guard_msgs`, so a change in wording is a
deliberate edit to this file rather than a silent regression.
-/
import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.Negative

/-! ## Wrong position: the path does not exist -/

/--
error: explicit_rw: step 1: position [0, 1, 1] does not exist: the subterm at prefix [0, 1] is a free variable (no children), so it has no child 1.
Subterm:
  a
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : a = b := by
  explicit_rw [h at [0, 1, 1]]

/-! ## Wrong position: the path exists but holds a different subterm -/

/--
error: explicit_rw: step 1: lemma `h` does not match the subterm at position [0, 1].
Expected
  a
but the subterm is
  c
-/
#guard_msgs in
example (a b c : Nat) (h : a = b) : c = c := by
  explicit_rw [h at [0, 1]]

/-! ## Non-matching lemma: right shape, wrong term -/

/--
error: explicit_rw: step 1: lemma `Nat.add_zero b` does not match the subterm at position [0, 1].
Expected
  b + 0
but the subterm is
  a + 0
-/
#guard_msgs in
example (a b : Nat) : a + 0 = a := by
  explicit_rw [Nat.add_zero b at [0, 1]]

/-! ## The step index is reported, not just "a step failed" -/

/--
error: explicit_rw: step 2: lemma `h2` does not match the subterm at position [0, 1].
Expected
  c
but the subterm is
  b
-/
#guard_msgs in
example (a b c d : Nat) (h1 : a = b) (h2 : c = d) : a = b := by
  explicit_rw [h1 at [0, 1], h2 at [0, 1]]

/-! ## The lemma does not prove an equation or an iff -/

/--
error: explicit_rw: step 1: lemma `hp` does not prove an equation or an iff; its type is
  p
-/
#guard_msgs in
example (p : Prop) (hp : p) (a b : Nat) : a = b := by
  explicit_rw [hp at [0, 1]]

/-! ## A leftover metavariable

`leaky`'s right-hand side mentions `m`, which matching the left-hand side does
not determine. `explicit_rw` refuses rather than letting `?m` escape into the
goal, where it would be silently solved later or block the proof.
-/

private theorem leaky (n : Nat) {m : Nat} : n + 0 = n + 0 * m := by
  rw [Nat.zero_mul, Nat.add_zero]

/--
error: explicit_rw: step 1: lemma `leaky a` still has an unassigned argument of type
  Nat
after matching at the given position. Supply it as an explicit argument, or fix the position. `explicit_rw` never searches for it.
-/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  explicit_rw [leaky a at [0, 1]]

/-! ## A definitional step that is not applicable -/

/-- error: explicit_rw: step 1: `beta` at this position: the subterm is not a beta-redex. -/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  explicit_rw [beta at [0, 1]]

/-- error: explicit_rw: step 1: `eta` at this position: the subterm is not an eta-redex. -/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  explicit_rw [eta at [0, 1]]

/-! ## `unfold` naming the wrong constant -/

def double (n : Nat) : Nat := n + n

/--
error: explicit_rw: step 1: `unfold ExplicitRwTest.Negative.double` was applied where the head constant is `@HAdd.hAdd`.
-/
#guard_msgs in
example (a : Nat) : a + a = a + a := by
  explicit_rw [unfold double at [0, 1]]

/-! ## The domain of a *dependent* `∀` is refused

Rewriting `p` in `∀ x : p, q x` would need the body transported along the domain
equality. `explicit_rw` does not build that cast, so it refuses rather than
producing an ill-typed term.
-/

/--
error: explicit_rw: step 1: position [0, 1, 0] rewrites the domain of a dependent `∀`, whose body mentions the bound variable; rebuilding that needs a cast of the body along the domain equality, which `explicit_rw` does not build. Only definitional steps are supported there.
-/
#guard_msgs in
example (p q : Prop) (r : p → Prop) (h : p = q) :
    (∀ x : p, r x) = (∀ x : p, r x) := by
  explicit_rw [h at [0, 1, 0]]

/-! ## `at *` is refused: positions are relative to one location -/

/--
error: explicit_rw: `at *` is not supported: positions are relative to one location. Write one `explicit_rw` per location.
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (hc : a = a) : True := by
  explicit_rw [h at [0, 1]] at *

end ExplicitRwTest.Negative
