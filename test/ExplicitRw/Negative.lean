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

/-! ## Product rule: terms are parsed in a whitelist grammar

Every term a trace hands to `explicit_rw` is parsed in the `explicitRwTerm`
category, which admits identifiers, applications, literals, parentheses and
ascriptions and nothing else. A `by` block, a macro expanding to one, and a term
elaborator that runs the simplifier in `MetaM` are all rejected by the
**parser**, before any elaborator runs. Parse errors cannot be pinned with
`#guard_msgs`, so those cases live in `test/ExplicitRw/RejectedSyntax/`, which
`Experiment/check_explicit_rw.py` compiles and requires to fail.
-/

/-! ## A stale position

Each position is relative to the previous step's result, so a position that was
valid before an earlier step is simply wrong afterwards.
-/

/--
error: explicit_rw: step 2: lemma `h1` does not match the subterm at position [0, 1, 1].
Expected
  a
but the subterm is
  b
-/
#guard_msgs in
example (a b : Nat) (h1 : a = b) (f : Nat → Nat) : f a = f b := by
  explicit_rw [h1 at [0, 1, 1], h1 at [0, 1, 1]]

/-! ## A `change` that is not definitionally equal

The message prints the term with the pretty printer, not the parse tree.
-/

/--
error: explicit_rw: step 1: `change (a +
  1)` at position [0, 1] produced a term that is not definitionally equal to the original.
Before
  a + 0
After
  a + 1
-/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  explicit_rw [change (a + 1) at [0, 1]]

/-! ## A dependent function argument

Rebuilding `f a = f a'` where `f`'s result type mentions its argument needs a
cast. The refusal is phrased in the tactic's own vocabulary.
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0

def DependentP (n : Nat) (_v : Vec Nat n) : Prop := True

/--
error: explicit_rw: step 1: position [0, 1] rewrites an argument of a dependent function, whose result type mentions that argument; rebuilding the term would need a cast, which `explicit_rw` does not build. Only definitional steps are supported there.
Function:
  DependentP
of type:
  (n : Nat) → Vec Nat n → Prop
-/
#guard_msgs in
example (n m : Nat) (h : n = m) (_v : Vec Nat n) : DependentP n _v := by
  explicit_rw [h at [0, 1]]

/-! ## `let` type and value positions stay refused

Only the `let` *body* (child 2) is cast-free; see `Definitional.lean`.
-/

/--
error: explicit_rw: step 1: position [0, 1, 1] rewrites the value of a `let`; only definitional steps are supported there.
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : (let y : Nat := a; y + 1) = b + 1 := by
  explicit_rw [h at [0, 1, 1]]

/-! ## `zeta` applied where there is no `let` -/

/-- error: explicit_rw: step 1: `zeta` at this position: the subterm is not a `let`. -/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  explicit_rw [zeta at [0, 1]]

/-! ## An unrecognised step keyword

`frobnicate` is not a step kind. It parses as a lemma term, and since round 5
elaborates lemma terms without error-recovery the underlying Lean message is
reported directly rather than wrapped, which is more useful.
-/

/-- error: explicit_rw: step 1: Unknown identifier `frobnicate` -/
#guard_msgs(error, drop info, drop warning) in
example (a : Nat) : a + 0 = a := by
  explicit_rw [frobnicate at [0, 1]]

/-! ## `iota` where there is nothing to reduce -/

/--
error: explicit_rw: step 1: `iota` at this position: the subterm is not a matcher or recursor application; its head is `@HAdd.hAdd`.
-/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  explicit_rw [iota at [0, 1]]

/-! ## `intro_ctx` is recognised but not implemented

It has syntax so that a trace containing it fails by name, rather than being
parsed as a lemma called `intro_ctx`.
-/

/--
error: explicit_rw: step 1: `intro_ctx` is a recorded step kind that `explicit_rw` does not implement: contextual rewriting changes what is in scope for later positions, which this tactic's single-location model does not represent. This trace cannot be replayed; hand-write the proof instead.
-/
#guard_msgs in
example (p q : Prop) (hq : q) : p → q := by
  explicit_rw [intro_ctx hp at [1]]

/-! ## Antiquotations are named, in every slot

`$x` parses in every category but means nothing in a trace. Round 6 gave it a
plain message in the term and step slots; round 7 found the recursive
side-proof grammar added in that same round had re-introduced "internal error",
so these pin all three.
-/

/-- error: explicit_rw: antiquotations are not admitted in a trace step. -/
#guard_msgs(error, drop info, drop warning) in
example (a b : Nat) : a = b := by
  explicit_rw [$x at [0, 1]]

/-- error: explicit_rw: step 1: antiquotations are not admitted in a side proof. -/
#guard_msgs(error, drop info, drop warning) in
example (c : Prop) [Decidable c] (x y u : Nat) (hxu : x = u) :
    (if c then x else y) = (if c then u else y) := by
  explicit_rw [ite_congr at [0, 1] with [rfl, $x, intro h ; rfl]] then rfl

/-- error: explicit_rw: antiquotations are not admitted in a trace step. -/
#guard_msgs(error, drop info, drop warning) in
example {α β : Type} (h : α = β) (f : α → α) (a : α) : cast h (f a) = cast h a := by
  explicit_rw [congr 3 [$x at []] at [0, 1]] then rfl

/-! ## `at *` is refused: positions are relative to one location -/

/--
error: explicit_rw: `at *` is not supported: positions are relative to one location. Write one `explicit_rw` per location.
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (hc : a = a) : True := by
  explicit_rw [h at [0, 1]] at *

end ExplicitRwTest.Negative
