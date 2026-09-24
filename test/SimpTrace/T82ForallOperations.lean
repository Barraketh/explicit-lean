import ExplicitLean.SimpOperations.Recording
import ExplicitLean.ExplicitRw

example (P Q : Prop) (h : P = Q) : ∀ p : P, p = p := by
  simp_operations_observe only [h]
  intro p
  rfl

example (P Q : Prop) (h : P = Q) : ∀ p : P, p = p := by
  explicit_rw_v2 [forall_congr at []
    domain [source_rule lean_term(h) variant 0 phase post fwd extra 0 at [] with []]
    body [auto_congr at [] with [arg 0 [cached [source_rule lean_term(h) variant 0
      phase post fwd extra 0 at [] with []] at []]], rule _root_.eq_self variant 0
      phase post fwd extra 0 at [] with []]]
  intro
  exact True.intro

example (P Q : Prop) (h : P = Q) : P → Q := by
  simp_operations_observe only [h]
  intro hp
  exact h.mp hp

example (P Q : Prop) (h : P = Q) : P → Q := by
  explicit_rw_v2 [forall_congr at []
    domain [source_rule lean_term(h) variant 0 phase post fwd extra 0 at [] with []]
    body []]
  intro hq
  exact hq

example (P : Prop) : P → P := by
  simp_operations_observe +contextual only
  exact id

example (P : Prop) : P → P := by
  explicit_rw_v2 [forall_congr at [] domain []
    body [bound 0 variant 0 phase post fwd extra 0 at [] with []]]
  intro
  exact True.intro

example (α : Type) (x y : α) : x = y → x = y := by
  explicit_rw_v2 [forall_congr at [] domain []
    body [bound 0 variant 0 phase post fwd extra 0 at [] with []]]
  intro
  exact True.intro
