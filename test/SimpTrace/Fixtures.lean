/-
`simp_trace` fixtures.

Each `simp_trace` call writes its trace JSON to `test/SimpTrace/out/<name>.json`.
`Experiment/check_simp_trace.py` compares each against the expected step
skeleton in `test/SimpTrace/expected/<name>.json`.

Compile with `lake env lean test/SimpTrace/Fixtures.lean` from the repository
root, so the relative `out :=` paths resolve.
-/
import ExplicitLean.SimpTrace
import Mathlib.Logic.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Group.Basic

namespace ExplicitLean.SimpTrace.Fixtures

/-- A top-level rewrite that closes the goal by `rfl`/`True`. -/
example (a : Nat) : a + 0 = a := by
  simp_trace with_trace "test/SimpTrace/out/top_level_rfl.json"

/-- Two chained rewrites. -/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace [h] with_trace "test/SimpTrace/out/chained.json"

/-- A `←` (reverse) rewrite. -/
example (a b : Nat) (h : b = a) : a + 0 = b := by
  simp_trace [← h] with_trace "test/SimpTrace/out/reverse.json"

/-- A rewrite under a `∀` binder. -/
example (f : Nat → Nat) : ∀ x : Nat, f x + 0 = f x := by
  simp_trace with_trace "test/SimpTrace/out/under_forall.json"

/-- A rewrite under a `fun x =>` binder. -/
example (f : Nat → Nat) : (fun x => f x + 0) = fun x => f x := by
  simp_trace with_trace "test/SimpTrace/out/under_lambda.json"

/-- A rewrite inside a hypothesis. -/
example (a b : Nat) (h : a + 0 = b) : a = b := by
  simp_trace at h with_trace "test/SimpTrace/out/at_hyp.json"
  exact h

/-- `simp [h]` with a local equation. -/
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  simp_trace [h] with_trace "test/SimpTrace/out/local_eq.json"

/-- A conditional lemma whose side condition simp discharged: `Nat.sub_add_cancel`
needs `n ≤ m`, which the discharger proves from the hypothesis `h`. -/
example (m n : Nat) (h : n ≤ m) : m - n + n = m := by
  simp_trace [Nat.sub_add_cancel, h] with_trace "test/SimpTrace/out/conditional.json"

/-- A simproc with a condition it reduces itself (`reduceIte`). -/
example (n : Nat) (h : n = 3) : (if n = 3 then 1 else 2) = 1 := by
  simp_trace [h] with_trace "test/SimpTrace/out/ite.json"

/-- A simproc arithmetic step. -/
example : (2 : Nat) + 3 = 5 := by
  simp_trace with_trace "test/SimpTrace/out/simproc.json"

/-- A definitional step: a reducible definition unfolding. -/
@[reducible] def myId (n : Nat) : Nat := n

example (n : Nat) : myId n = n := by
  simp_trace [myId] with_trace "test/SimpTrace/out/unfold.json"

/-- A definitional step: beta reduction. -/
example (f : Nat → Nat) (n : Nat) : (fun x => f x) n = f n := by
  simp_trace with_trace "test/SimpTrace/out/beta.json"

/-- `+contextual`. -/
example (p q : Prop) : p → (p ∧ q → q) := by
  simp_trace +contextual with_trace "test/SimpTrace/out/contextual.json"

/-- Every parenthesized argument form `simp` accepts must parse, or `simp_trace`
is not substitutable for `simp`. -/
example : (2:Nat) + 2 = 4 := by
  simp_trace (config := { decide := true }) with_trace "test/SimpTrace/out/cfg_paren.json"

example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace (discharger := assumption) [h] with_trace "test/SimpTrace/out/discharger.json"

example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace (disch := assumption) [h] with_trace "test/SimpTrace/out/disch.json"

/-- `+decide` records the decision as an `eq` step, never an unattributed abort. -/
example : (2:Nat) + 2 = 4 := by
  simp_trace +decide with_trace "test/SimpTrace/out/decide.json"

/-- A `-flag` form. -/
example (a : Nat) : a + 0 = a := by
  simp_trace -contextual with_trace "test/SimpTrace/out/minus_flag.json"

/-- `[*]` and `at h ⊢`. -/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace [*] with_trace "test/SimpTrace/out/star_lemmas.json"

example (a b : Nat) (h : a + 0 = b) : a + 0 = b := by
  simp_trace at h ⊢ with_trace "test/SimpTrace/out/at_hyp_goal.json"
  exact h

example (a b : Nat) (h : a + 0 = b) : b + 0 = a := by
  simp_trace at * with_trace "test/SimpTrace/out/at_star.json"
  omega

/-- A shadowed nested binder: the inner `x` shadows the outer one. -/
example (f : Nat → Nat → Nat) :
    (fun x => (fun x => f x (x + 0)) (x + 0)) = (fun x => f x x) := by
  simp_trace with_trace "test/SimpTrace/out/shadowed.json"

/-- A `let`, which simp discharges by zeta reduction. -/
example (a : Nat) : (let y := a + 0; y + 0) = a := by
  simp_trace with_trace "test/SimpTrace/out/zeta.json"

/-- An inaccessible hypothesis: recorded with a `local` object carrying its
user name and context index, never a bare `ctx:` label. -/
example (a b : Nat) : a = b → a + 0 = b := by
  intro _
  simp_trace [*] with_trace "test/SimpTrace/out/inaccessible.json"

/-- A hypothesis that simplifies to `False`, closing by absurdity. -/
example (a : Nat) (h : a ≠ a) : False := by
  simp_trace at h with_trace "test/SimpTrace/out/absurd.json"

/-- A call that closes the goal via `True`. -/
example : True := by
  simp_trace with_trace "test/SimpTrace/out/closes_true.json"

end ExplicitLean.SimpTrace.Fixtures
