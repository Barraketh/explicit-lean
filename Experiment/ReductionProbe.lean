import ExplicitLean.SimpExplicit

/-! Closed, ambient-free reduction replay fixtures.  These commands are not
    recorder output: they exercise the replay IR directly. -/

def reductionDelta (n : Nat) : Nat := n + 1

inductive ReductionInductive where
  | mk (left : Nat) (right : Nat)

example (n : Nat) : reductionDelta n = n + 1 := by
  simp_explicit [reduce delta reductionDelta]

example (n : Nat) : (fun x : Nat => x + 1) n = n + 1 := by
  simp_explicit [reduce beta]

example (n : Nat) : (let x := n + 1; x) = n + 1 := by
  simp_explicit [reduce zeta]

example (n : Nat) :
    @ReductionInductive.rec (fun _ => Nat) (fun left _ => left)
      (ReductionInductive.mk n 0) = n := by
  simp_explicit [reduce iota]

example (n : Nat) : (ReductionInductive.mk n 0).1 = n := by
  simp_explicit [reduce projection ReductionInductive 0]

example (f : Nat → Nat) : (fun x => f x) = f := by
  simp_explicit [reduce eta]

example (f : Nat → Nat) : (fun x => f x) = f := by
  simp_explicit [↑ reduce eta]

/- The pinned simplifier does not expose eta as a recorder transition.  The
   report assertion for that fact lives in check_reductions.py; this example
   only verifies that the replay command itself remains available. -/
set_option explicitLean.simpExplicit.report true in
example (f : Nat → Nat) : (fun x => f x) = f := by
  simp_explicit?

set_option explicitLean.simpExplicit.report true in
example (n : Nat) : reductionDelta n = n + 1 := by
  simp_explicit? only [reductionDelta]

set_option explicitLean.simpExplicit.report true in
example (n : Nat) : (fun x : Nat => x + 1) n = n + 1 := by
  simp_explicit?

set_option explicitLean.simpExplicit.report true in
example (n : Nat) : (let x := n + 1; x) = n + 1 := by
  simp_explicit?

set_option explicitLean.simpExplicit.report true in
example (n : Nat) :
    @ReductionInductive.rec (fun _ => Nat) (fun left _ => left)
      (ReductionInductive.mk n 0) = n := by
  simp_explicit?

set_option explicitLean.simpExplicit.report true in
example (n : Nat) : (ReductionInductive.mk n 0).1 = n := by
  simp_explicit?

/- Iota replay must retain the beta capability needed by matcher reduction
   after an earlier pre-phase rewrite exposes the constructor discriminant. -/
set_option explicitLean.simpExplicit.report true in
example {α : Type} (p : α → Bool) (x : α) (n : Nat) (h : p x = true) :
    (match p x with | true => n | false => 0) = n := by
  simp_explicit? [h]

/- Wrong operation identity, kind, selector, order, missing command, and
   duplicate command must all fail rather than being silently skipped. -/
example (n : Nat) : reductionDelta n = n + 1 := by
  fail_if_success simp_explicit [reduce delta notReductionDelta]
  exact rfl

example (n : Nat) : reductionDelta n = n + 1 := by
  fail_if_success simp_explicit [reduce beta]
  exact rfl

example (n : Nat) : reductionDelta n = n + 1 := by
  fail_if_success simp_explicit [match 99 => reduce delta reductionDelta]
  exact rfl

example (n : Nat) : reductionDelta n = n + 1 := by
  fail_if_success simp_explicit [Nat.add_comm, reduce delta reductionDelta]
  exact rfl

example (n : Nat) : reductionDelta n = n + 1 := by
  fail_if_success simp_explicit [Nat.add_zero]
  exact rfl

example (n : Nat) : reductionDelta n = n + 1 := by
  fail_if_success simp_explicit [reduce delta reductionDelta, reduce delta reductionDelta]
  exact rfl

/- Empty replay may not let `Simp.mainCore` perform hidden reductions.  The
   neutral beta/zeta paths preserve syntax; pinned iota/projection traversal is
   rejected before its built-in reducer can run. -/
example (n : Nat) : (fun x : Nat => x + 1) n = 1 + n := by
  simp_explicit leave_open []
  guard_target =ₛ (fun x : Nat => x + 1) n = 1 + n
  exact Nat.add_comm n 1

example (n : Nat) : (let x := n + 1; x) = 1 + n := by
  simp_explicit leave_open []
  guard_target =ₛ (let x := n + 1; x) = 1 + n
  exact Nat.add_comm n 1

example (n : Nat) :
    @ReductionInductive.rec (fun _ => Nat) (fun left _ => left + 1)
      (ReductionInductive.mk n 0) = 1 + n := by
  fail_if_success simp_explicit leave_open []
  exact Nat.add_comm n 1

example (n : Nat) : (ReductionInductive.mk (n + 1) 0).1 = 1 + n := by
  fail_if_success simp_explicit leave_open []
  exact Nat.add_comm n 1

example (n : Nat) : reductionDelta n = n + 1 := by
  fail_if_success simp_explicit [reduce nonsense]
  exact rfl

example (n : Nat) : (ReductionInductive.mk n 0).1 = n := by
  fail_if_success simp_explicit [reduce projection ReductionInductive 99]
  exact rfl
