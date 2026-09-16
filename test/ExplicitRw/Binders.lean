/-
Fixtures for `explicit_rw` under binders.

Crossing a `lam`/`forallE` body (child `1`) introduces that bound variable as a
local, so the lemma term and its explicit arguments may mention it. The
congruence proof is rebuilt with `funext` for a lambda and `forall_congr` for a
`∀`, which is why these proofs legitimately depend on `Quot.sound` (`funext`),
exactly as the `conv`/`ext` equivalents below do.
-/
import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.Binders

/-! ## Rewrite under `∀ x,` -/

theorem under_forall (f g : Nat → Nat) (h : ∀ x, f x = g x) :
    ∀ x : Nat, f x + 0 = g x := by
  explicit_rw [h x at [1, 0, 1, 0, 1]]
  guard_target =ₛ ∀ x : Nat, g x + 0 = g x
  intro x
  rfl

theorem under_forall_conv (f g : Nat → Nat) (h : ∀ x, f x = g x) :
    ∀ x : Nat, f x + 0 = g x := by
  conv => ext x; lhs; arg 1; rw [h x]
  intro x
  rfl

/-! ## Rewrite under `fun x =>` (funext congruence) -/

theorem under_lambda (f g : Nat → Nat) (h : ∀ x, f x = g x) :
    (fun x => f x + 0) = (fun x => g x + 0) := by
  explicit_rw [h x at [0, 1, 1, 0, 1]]
  guard_target =ₛ (fun x => g x + 0) = (fun x => g x + 0)
  rfl

theorem under_lambda_conv (f g : Nat → Nat) (h : ∀ x, f x = g x) :
    (fun x => f x + 0) = (fun x => g x + 0) := by
  conv => lhs; ext x; arg 1; rw [h x]

/-! ## A position crossing two binders

`[1, 1, 0, 1]` crosses the `∀ x` body, then the `∀ y` body, then descends into
the left-hand side of the inner equation.
-/

theorem two_binders (f g : Nat → Nat → Nat) (h : ∀ x y, f x y = g x y) :
    ∀ x y : Nat, f x y + 0 = g x y := by
  explicit_rw [h x y at [1, 1, 0, 1, 0, 1]]
  guard_target =ₛ ∀ x y : Nat, g x y + 0 = g x y
  intro x y
  rfl

theorem two_binders_conv (f g : Nat → Nat → Nat) (h : ∀ x y, f x y = g x y) :
    ∀ x y : Nat, f x y + 0 = g x y := by
  conv => ext x y; lhs; arg 1; rw [h x y]
  intro x y
  rfl

/-! ## Under a lambda, with the bound variable in the lemma's explicit argument -/

theorem lambda_explicit_arg (f : Nat → Nat) :
    (fun x => f x + 0) = (fun x => f x) := by
  explicit_rw [Nat.add_zero (f x) at [0, 1, 1]]
  guard_target =ₛ (fun x => f x) = (fun x => f x)
  rfl

theorem lambda_explicit_arg_conv (f : Nat → Nat) :
    (fun x => f x + 0) = (fun x => f x) := by
  conv => lhs; ext x; rw [Nat.add_zero (f x)]

end ExplicitRwTest.Binders
