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

end ExplicitLean.SimpTrace.T20IteSimproc
