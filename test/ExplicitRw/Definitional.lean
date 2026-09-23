/-
Fixtures for the definitional steps (`unfold`, `beta`, `eta`, `proj`, `change`)
and for `eq ... by tac`, the replay form of a simproc-computed equation.

Definitional steps replace the subterm by a definitionally equal one and carry
no proof beyond the defeq check, so the rebuilt goal is closed by `Eq.refl`-like
transport rather than by a congruence proof.
-/
import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.Definitional

/-- A plain definition, so `unfold` has something to delta-reduce. -/
def double (n : Nat) : Nat := n + n

/-! ## An `unfold` step -/

theorem unfold_step (a : Nat) : double a = a + a := by
  explicit_rw [unfold double at [0, 1]]
  guard_target =ₛ a + a = a + a
  rfl

theorem unfold_step_conv (a : Nat) : double a = a + a := by
  conv => lhs; unfold double

/-! ## A `beta` step -/

theorem beta_step (a : Nat) : (fun x => x + 0) a = a := by
  explicit_rw [beta at [0, 1]]
  guard_target =ₛ a + 0 = a
  exact Nat.add_zero a

theorem beta_step_conv (a : Nat) : (fun x => x + 0) a = a := by
  show a + 0 = a
  exact Nat.add_zero a

/-! ## `unfold` and `beta` in one trace

`double a` unfolds to `a + a`; a following `beta` would have nothing to do, so
the second step here is the `eta` form on a separate term instead.
-/

theorem unfold_then_rewrite (a : Nat) : double (a + 0) = a + a := by
  explicit_rw [Nat.add_zero a at [0, 1, 1], unfold double at [0, 1]]
  guard_target =ₛ a + a = a + a
  rfl

/-! ## An `eta` step -/

theorem eta_step (f : Nat → Nat) : (fun x => f x) = f := by
  explicit_rw [eta at [0, 1]]
  guard_target =ₛ f = f
  rfl

/-! ## A `change` step: last-resort definitional replacement -/

theorem change_step (a : Nat) : double a = a + a := by
  explicit_rw [change (a + a) at [0, 1]]
  guard_target =ₛ a + a = a + a
  rfl

/-! ## An `eq ... by rfl` arithmetic step

This is how a simproc-computed equation is replayed: the equation is stated
explicitly and proved by an ordinary tactic, never by the simproc.
-/

theorem eq_by_rfl : (2 + 3) + 1 = 6 := by
  explicit_rw [eq (2 + 3 = 5) by rfl at [0, 1, 0, 1]]
  guard_target =ₛ 5 + 1 = 6
  rfl

theorem eq_by_rfl_conv : (2 + 3) + 1 = 6 := by
  conv => lhs; arg 1; rw [show 2 + 3 = 5 from rfl]

/-- The `decide` variant of the same step kind. -/
theorem eq_by_decide : (2 + 3) * 2 = 10 := by
  explicit_rw [eq ((2 : Nat) + 3 = 5) by decide at [0, 1, 0, 1]]
  guard_target =ₛ 5 * 2 = 10
  rfl

/-! ## `proj` steps: both shapes a projection can take

`(P.mk 3 4).fst` elaborates to an application of the projection *function*
`P.fst`, which needs a delta step before it reduces; a single-field structure
gives a raw `Expr.proj`. Both are covered, since only the first exercises the
delta path.
-/

structure Pair where
  fst : Nat
  snd : Nat

theorem proj_function_shape : (Pair.mk 3 4).fst = 3 := by
  explicit_rw [proj at [0, 1]]
  guard_target =ₛ 3 = 3
  rfl

/-- A projection also reduces when its structure argument is exposed by WHNF. -/
def makePair (a b : Nat) : Pair := ⟨a, b⟩

theorem proj_function_whnf_major : (makePair 3 4).fst = 3 := by
  explicit_rw [proj at [0, 1]]
  guard_target =ₛ 3 = 3
  rfl

/- `proj` still refuses a stuck structure argument rather than unfolding it. -/
/-- error: explicit_rw: step 1: `proj` at this position: the projection's argument is not a constructor application, so there is nothing to reduce. -/
#guard_msgs in
example (p : Pair) : p.fst = p.fst := by
  explicit_rw [proj at [0, 1]]

theorem proj_function_shape_conv : (Pair.mk 3 4).fst = 3 := by
  conv => lhs; whnf

structure Box where
  val : Nat

theorem proj_raw_shape : (Box.mk 7).val = 7 := by
  explicit_rw [proj at [0, 1]]
  guard_target =ₛ 7 = 7
  rfl

/-! ## An `mdata` position

Ordinary goals carry no `mdata`, so the node is reached here by wrapping the
target explicitly. Navigation consumes child `0` and rebuilds the wrapper.
-/

open Lean Elab Tactic in
/-- Wrap the goal in an `mdata` node, definitionally. -/
elab "wrap_mdata" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let wrapped := Expr.mdata (KVMap.empty.insert `explicitRwTest (DataValue.ofBool true)) t
  replaceMainGoal [← g.replaceTargetDefEq wrapped]

theorem mdata_position (a b : Nat) (h : a = b) : a + 0 = b := by
  wrap_mdata
  -- child 0 of the `mdata` node, then the usual path into the left-hand side.
  explicit_rw [h at [0, 0, 1, 0, 1]]
  guard_target =ₛ b + 0 = b
  rfl

/-! ## A `let` body position (spec child 2)

A `let` body needs no cast: `let x := v; b` is definitionally `b[v/x]`, so the
proof transports unchanged. The `let` type and value positions remain refused;
see `test/ExplicitRw/Negative.lean`.
-/

theorem let_body (a b : Nat) (h : a = b) : (let y : Nat := 7; a + y) = b + 7 := by
  explicit_rw [h at [0, 1, 2, 0, 1]]
  -- The `let` must survive: only a `zeta` step may destroy it.
  guard_target =ₛ (let y : Nat := 7; b + y) = b + 7
  rfl

theorem let_body_conv (a b : Nat) (h : a = b) : (let y : Nat := 7; a + y) = b + 7 := by
  conv => lhs; rw [h]

/-- Two steps through the same `let` body: step 2's position is only valid if
step 1 left the `let` in place. -/
theorem let_body_two_steps (a b c d : Nat) (h1 : a = b) (h2 : c = d) :
    (let y : Nat := 7; a + (y + c)) = b + (7 + d) := by
  explicit_rw [h1 at [0, 1, 2, 0, 1], h2 at [0, 1, 2, 1, 1]]
  guard_target =ₛ (let y : Nat := 7; b + (y + d)) = b + (7 + d)
  rfl

/-- The bound value is itself a free variable: rewriting inside the body must not
capture the standalone `a` in `(c + a)`, which the source never wrote as `y`. -/
theorem let_body_no_capture (a b c : Nat) (h : c = b) :
    (let y : Nat := a; y + (c + a)) = a + (b + a) := by
  explicit_rw [h at [0, 1, 2, 1, 0, 1]]
  guard_target =ₛ (let y : Nat := a; y + (b + a)) = a + (b + a)
  rfl

set_option linter.unusedVariables false in
/-- A `let` whose body never mentions the bound variable still survives a body
rewrite: `mkLetFVars (usedLetOnly := false)` keeps the binder, so only an
explicit `zeta` step removes it. -/
theorem let_body_unused_binder (a : Nat) (h : a = 7) :
    (let y : Nat := 7; a + 1) = 8 := by
  explicit_rw [h at [0, 1, 2, 0, 1]]
  guard_target =ₛ (let y : Nat := 7; 7 + 1) = 8
  rfl

/-! ## The `zeta` step: the only step that destroys a `let` -/

theorem zeta_step (a : Nat) : (let y : Nat := 7; a + y) = a + 7 := by
  explicit_rw [zeta at [0, 1]]
  guard_target =ₛ a + 7 = a + 7
  rfl

theorem zeta_step_conv (a : Nat) : (let y : Nat := 7; a + y) = a + 7 := by
  conv => lhs; zeta

/-- A named trace `zeta` is zeta-delta on the local definition `g`; the
recorded lambda body is replayed with an ordinary `change`, then its application
is beta-reduced as a separate trace step. This matches
`test/SimpTrace/zeta_delta_at_hyp`. -/
example (a : Nat) (P : Nat → Prop) (hP : ∀ n, P n) : True := by
  let g : Nat → Nat := fun s => s + 0
  have hg : P (g a) := hP _
  explicit_rw [change (fun s => s + 0) at [1, 0], beta at [1]] at hg
  guard_hyp hg :ₛ P (a + 0)
  exact True.intro

/-- A position taken *after* a `zeta` step, against the zeta-reduced term. -/
theorem zeta_then_rewrite (a b : Nat) (h : a = b) :
    (let y : Nat := 7; a + y) = b + 7 := by
  explicit_rw [zeta at [0, 1], h at [0, 1, 0, 1]]
  guard_target =ₛ b + 7 = b + 7
  rfl

/-! ## The `iota` step: **exactly one** matcher or recursor reduction

The spec says "reduced one step". Round 5 found this was using `whnfCore`, which
iterates to weak-head normal form and so swallows the redexes that later recorded
`iota` steps address — a trace of N steps would fail at step 2. It now uses
`reduceRecMatcher?`, the single-step primitive.
-/

/-- One `iota` contracts the recursor and leaves a beta-redex behind, rather than
continuing to a normal form: the following `beta` steps are what finish the job,
and they would have nothing to do if `iota` had normalised. -/
theorem iota_recursor : Nat.rec (motive := fun _ => Nat) 7 (fun _ _ => 9) 0 = 7 := by
  explicit_rw [iota at [0, 1], beta at [0, 1]]
  guard_target =ₛ 7 = 7
  rfl

/-- A `match` compiles to a matcher application, which `iota` reduces once. -/
def classify : Nat → Nat
  | 0 => 100
  | _ + 1 => 200

theorem iota_matcher : classify 0 = 100 := by
  explicit_rw [unfold classify at [0, 1], iota at [0, 1]]
  guard_target =ₛ 100 = 100
  rfl

/-- Nested matchers: each needs its **own** `iota`. If one step reduced to weak-head
normal form, the second step would fail at a position the recorder considered
valid, so this fixture pins the step count. -/
def outerStep : Nat → Nat
  | 0 => 10
  | _ + 1 => 20

def innerStep : Nat → Nat
  | 0 => 1
  | _ + 1 => 2

theorem iota_two_steps : outerStep (innerStep 0) = 20 := by
  explicit_rw [unfold innerStep at [0, 1, 1], iota at [0, 1, 1],
               unfold outerStep at [0, 1], iota at [0, 1]]
  guard_target =ₛ 20 = 20
  rfl

/-! ## The `congr` step: cast transport

`congr i [steps] at pos` rebuilds the application at `pos` through its
auto-generated congruence theorem, proving argument `i`'s equation from the
nested steps. Unlike `congrArg` it transports the arguments that *depend* on
`i`, which is what makes a `cast` position replayable at all: the type-equality
proof rides along.

These three replay T1's recorded traces verbatim. The first is the shape of
`Mathlib/Logic/Function/Basic.lean:390`.
-/

/-- T1's `congr_cast` trace: `congr` at `[0, 1]` on argument 3, nested `hfa`. -/
theorem congr_cast {α β : Type} (h : α = β) (f : α → α) (a : α) (hfa : f a = a) :
    cast h (f a) = cast h a := by
  explicit_rw [congr 3 [hfa at []] at [0, 1]] then rfl

/-- T1's `congr_nested_cast` trace: a `congr` inside a `congr`, transporting two
levels of type equality. -/
theorem congr_nested_cast {α β γ : Type} (h₁ : α = β) (h₂ : β = γ) (f : α → α)
    (a : α) (hfa : f a = a) :
    cast h₂ (cast h₁ (f a)) = cast h₂ (cast h₁ a) := by
  explicit_rw [congr 3 [congr 3 [hfa at []] at []] at [0, 1]] then rfl

/-- The `Function/Basic:390` shape, which used to panic the recorder. -/
theorem congr_function_basic {α β : Type} (h : α = β) (g : α → α) (x : α)
    (hgx : g x = x) : cast h (g x) = cast h x := by
  explicit_rw [congr 3 [hgx at []] at [0, 1]]
  guard_target =ₛ cast h x = cast h x
  rfl

end ExplicitRwTest.Definitional
