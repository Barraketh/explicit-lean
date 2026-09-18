import ExplicitLean.SimpTrace

namespace ExplicitLean.SimpTrace.T20IteSimproc

/- A changed application tail is refused before any semantic record is made. -/
def changedTailBefore : Lean.Expr :=
  Lean.mkAppN (.const ``ite [])
    #[.const ``True [], .const ``True [], .const ``True [],
      .const ``True [], .const ``False [], .const ``Nat.zero []]

def changedTailAfter : Lean.Expr :=
  Lean.mkAppN (.const ``Nat.succ [])
    #[.const ``Nat.zero [], .const ``True []]

#guard (peelBoundedIteApplication changedTailBefore changedTailAfter).isNone

theorem source_condition (p : Prop) (h : p) : p = True :=
  propext ⟨fun _ => True.intro, fun _ => h⟩

example (p : Prop) [Decidable p] (h : p) : (if p then 1 else 2) = 1 := by
  simp_trace [h] =>trace "test/SimpTrace/out/t20_ite_true.json"

example (p : Prop) [Decidable p] (h : ¬p) : (if p then 1 else 2) = 2 := by
  simp_trace [h] =>trace "test/SimpTrace/out/t20_ite_false.json"

example (n : Nat) (h : n = 3) : (if n = 3 then 1 else 2) = 1 := by
  simp_trace [h] =>trace "test/SimpTrace/out/t20_ite_nested_condition.json"

example (p : Prop) [Decidable p] (h : p) :
    (if p then (if p then 1 else 2) else 3) = 1 := by
  simp_trace [h] =>trace "test/SimpTrace/out/t20_ite_nested_occurrence.json"

example (p : Prop) [Decidable p] (h : p) : (if p then 1 else 2) = 1 := by
  simp_trace [source_condition p h] =>trace "test/SimpTrace/out/t20_ite_source.json"

example (p : Prop) [Decidable p] (h : p) :
    (dite p (fun _ => 1) (fun _ => 2)) = 1 := by
  simp_trace [h] =>trace "test/SimpTrace/out/t20_dite_true.json"

example (p : Prop) [Decidable p] (h : ¬p) :
    (dite p (fun _ => 1) (fun _ => 2)) = 2 := by
  simp_trace [h] =>trace "test/SimpTrace/out/t20_dite_false.json"

example (p : Prop) [Decidable p] (f g : Nat → Nat) (a : Nat) (h : p) :
    (if p then f else g) a = f a := by
  simp_trace [h] =>trace "test/SimpTrace/out/t20_ite_applied.json"

example (p : Prop) [Decidable p] (f : p → Nat → Nat) (g : ¬p → Nat → Nat)
    (a : Nat) (h : p) :
    (dite p f g) a = f h a := by
  simp_trace [h] =>trace "test/SimpTrace/out/t20_dite_applied.json"

/- Regression for Function.Basic site 17: forked traversal records the
congruence that changes `a = a` to `True` before the later `reduceIte` call.
The second call has no diverted condition events and must use its actual
simproc proof, while retaining the earlier congruence transition. -/
example (α β γ : Type) [DecidableEq α] (f : α → β) (g : β → γ)
    (a : α) (c c' : γ)
    (h : (g ∘ f) a = if a = a then c else c') : True := by
  simp_trace only [Function.comp_apply, reduceIte] at h =>trace "test/SimpTrace/out/t20_ite_reflexive_site17.json"
  trivial

/- Related reflexive-condition shapes ensure no duplicate or missing bounded
events when an `ite`/`dite` is applied or nested. -/
example (α : Type) [DecidableEq α] (a : α) (f g : Nat → Nat) (x : Nat) :
    (if a = a then f else g) x = f x := by
  simp_trace only [reduceIte]

example (α : Type) [DecidableEq α] (a : α) :
    (if a = a then (if a = a then 1 else 2) else 3) = 1 := by
  simp_trace only [reduceIte]

example (α : Type) [DecidableEq α] (a : α) :
    (dite (a = a) (fun _ => (if a = a then 1 else 2)) (fun _ => 3)) = 1 := by
  simp_trace only [reduceIte, reduceDIte]

end ExplicitLean.SimpTrace.T20IteSimproc
