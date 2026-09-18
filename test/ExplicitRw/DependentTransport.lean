/- Focused reduced forms for the dependent-forall transport primitive. -/
import ExplicitLean.ExplicitRw
import Mathlib.Logic.Basic

namespace ExplicitRwTest.DependentTransport

theorem domain_false (A : Prop) (B : A → Prop) (h : A = False) :
    (A → ∀ x : A, B x) = True := by
  explicit_rw [transport forall 1 [h at []] body [] at [0, 1, 1]]
  explicit_rw [forall_false at [0, 1, 1], implies_true at [0, 1]]
  rfl

theorem domain_true (A B : Prop) (h : A = True) :
    (A → ∀ _ : A, B) = (True → B) := by
  explicit_rw [h at [0, 1, 0], transport forall 2 [h at []] body [] at [0, 1, 1], forall_true_left at [0, 1, 1]]
  rfl

theorem body_handle (A : Prop) (B C : A → Prop) (hb : ∀ x : A, B x = C x) :
    (A → ∀ x : A, B x) = (A → ∀ x : A, C x) := by
  explicit_rw [transport forall 3 [eq (A = A) by rfl at []] body [hb introduced_ref 3 at []] at [0, 1, 1]]
  rfl

/- The four Logic.Basic branches all reduce to the same operation: a
   proposition-valued forall whose domain is changed before a branch lemma
   consumes it.  Keep two extra reduced forms here so both branch polarities
   and a body with an application are covered. -/
theorem branch_false (P : Prop) (Q : P → Prop) (h : P = False) :
    (∀ x : P, Q x) = True := by
  explicit_rw [transport forall 4 [h at []] body [] at [0, 1], forall_false at [0, 1]]
  rfl

theorem branch_true (P : Prop) (Q : Prop) (h : P = True) :
    (∀ _ : P, Q) = Q := by
  explicit_rw [transport forall 5 [h at []] body [] at [0, 1], forall_true_left at [0, 1]]
  rfl

theorem membership_body (P : Prop) (α β : Type) [Membership α β]
    (a : α) (s : P → β) (_t : ¬P → β) (h : P = False) :
    (∀ x : P, a ∈ s x) = True := by
  explicit_rw [transport forall 6 [h at []] body [] at [0, 1], forall_false at [0, 1]]
  rfl

end ExplicitRwTest.DependentTransport
