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
  simp_trace (out := "test/SimpTrace/out/top_level_rfl.json")

/-- Two chained rewrites. -/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp_trace (out := "test/SimpTrace/out/chained.json") [h]

/-- A `←` (reverse) rewrite. -/
example (a b : Nat) (h : b = a) : a + 0 = b := by
  simp_trace (out := "test/SimpTrace/out/reverse.json") [← h]

/-- A rewrite under a `∀` binder. -/
example (f : Nat → Nat) : ∀ x : Nat, f x + 0 = f x := by
  simp_trace (out := "test/SimpTrace/out/under_forall.json")

/-- A rewrite under a `fun x =>` binder. -/
example (f : Nat → Nat) : (fun x => f x + 0) = fun x => f x := by
  simp_trace (out := "test/SimpTrace/out/under_lambda.json")

/-- A rewrite inside a hypothesis. -/
example (a b : Nat) (h : a + 0 = b) : a = b := by
  simp_trace (out := "test/SimpTrace/out/at_hyp.json") at h
  exact h

/-- `simp [h]` with a local equation. -/
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  simp_trace (out := "test/SimpTrace/out/local_eq.json") [h]

/-- A conditional lemma whose side condition simp discharged: `Nat.sub_add_cancel`
needs `n ≤ m`, which the discharger proves from the hypothesis `h`. -/
example (m n : Nat) (h : n ≤ m) : m - n + n = m := by
  simp_trace (out := "test/SimpTrace/out/conditional.json") [Nat.sub_add_cancel, h]

/-- A simproc with a condition it reduces itself (`reduceIte`). -/
example (n : Nat) (h : n = 3) : (if n = 3 then 1 else 2) = 1 := by
  simp_trace (out := "test/SimpTrace/out/ite.json") [h]

/-- A simproc arithmetic step. -/
example : (2 : Nat) + 3 = 5 := by
  simp_trace (out := "test/SimpTrace/out/simproc.json")

/-- A definitional step: a reducible definition unfolding. -/
@[reducible] def myId (n : Nat) : Nat := n

example (n : Nat) : myId n = n := by
  simp_trace (out := "test/SimpTrace/out/unfold.json") [myId]

/-- A definitional step: beta reduction. -/
example (f : Nat → Nat) (n : Nat) : (fun x => f x) n = f n := by
  simp_trace (out := "test/SimpTrace/out/beta.json")

/-- `+contextual`. -/
example (p q : Prop) : p → (p ∧ q → q) := by
  simp_trace (out := "test/SimpTrace/out/contextual.json") +contextual

/-- A call that closes the goal via `True`. -/
example : True := by
  simp_trace (out := "test/SimpTrace/out/closes_true.json")

end ExplicitLean.SimpTrace.Fixtures
