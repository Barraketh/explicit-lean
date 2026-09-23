import Mathlib.Order.CompleteLattice.Basic
import ExplicitLean.SimpTrace
import ExplicitLean.ExplicitRw

/-! Focused regression for LHS-only validation of class-valued explicit binders. -/

open Lean Lean.Meta

namespace ExplicitLean.SimpTrace.T77ClassExplicitArguments

/- The source call mirrors the Birkhoff `this.allEq` shape: the rewrite fixes
   one argument from its LHS, while the remaining explicit argument has a
   class type and can be supplied by ordinary instance synthesis. -/
example {α : Type*} [LE α] [OrderBot α] (this : Subsingleton (OrderBot α))
    (f : OrderBot α → Nat) (a : OrderBot α) :
    f a = f (inferInstance : OrderBot α) := by
  simp_trace only [this.allEq]

/- `iInf_pos` has an explicit proof argument after matching its LHS. Since its
   index is a class proposition, ordinary instance synthesis supplies that
   proof just as it does during `explicit_rw`. -/
example {α : Type*} [Nonempty α] : (⨅ h : Nonempty α, True) = True := by
  simp_trace only [iInf_pos]

private theorem extraNatBinder (n ignored : Nat) : n + 0 = n := Nat.add_zero n

/- The recorder's own LHS-only validator must reject a missing non-class
   explicit argument. Simp itself rejects this malformed theorem application
   before firing, so exercise the validator directly on the recorded shape. -/
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let a := mkNatLit 2
    let before := mkAppN (mkConst ``Nat.add) #[a, mkNatLit 0]
    let reason ← checkRwStep (.decl ``extraNatBinder true false) #[a] false none
      before a {} #[] "" none
    unless reason.any (String.startsWith · "unassigned_explicit_argument:") do
      throwError "expected a missing non-class explicit argument, got {reason}"

/- Keep the boundary narrow: a leftover ordinary explicit argument is still
   not inferred from unrelated local context or target matching. -/
/--
error: explicit_rw: step 1: lemma `extraNatBinder a` still has an unassigned argument of type
  ℕ
after matching at the given position. Supply it as an explicit argument, or fix the position. `explicit_rw` never searches for it.
-/
#guard_msgs in
example (a : Nat) : a + 0 = a := by
  explicit_rw [extraNatBinder a at [0, 1]]

end ExplicitLean.SimpTrace.T77ClassExplicitArguments
