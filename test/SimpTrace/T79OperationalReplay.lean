import ExplicitLean.ExplicitRw

namespace ExplicitLean.SimpTrace.T79OperationalReplay

/- A declaration operand, variant/phase/direction metadata, exact raw child path,
   and empty ordered premise list are all visible in the generated source. -/
example (n : Nat) : n + 0 = n := by
  explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 at [0, 1] with []]
  rfl

/- The same theorem is applied backwards at the right-hand redex. -/
example (n : Nat) : n = n + 0 := by
  explicit_rw_v2 [rule Nat.add_zero variant 0 phase dpost rev extra 0 at [1] with []]
  rfl

/- Only the named path is changed; the second matching occurrence remains until
   the second explicit operation names its own path. -/
example (n : Nat) : n + 0 = n + 0 := by
  explicit_rw_v2 [rule Nat.add_zero variant 1 phase dpre fwd extra 0 at [0, 1] with []]
  change n = n + 0
  explicit_rw_v2 [rule Nat.add_zero variant 7 phase post fwd extra 0 at [1] with []]
  rfl

/- A local theorem is an exact local-context operand. -/
example (n : Nat) (h : n + 0 = n) : n + 0 = n := by
  explicit_rw_v2 [local h variant 0 phase pre fwd extra 0 at [0, 1] with []]
  rfl

/- A nontrivial source operand is replayed from its original parser syntax.
The operational record contains no elaborated theorem or proof term. -/
example (n : Nat) (h : n + 0 = n) : n + 0 = n := by
  explicit_rw_v2 [source_rule lean_term(h) variant 0 phase pre fwd extra 0 at [0, 1] with []]
  rfl

example (n : Nat) : n = n + 0 := by
  explicit_rw_v2 [source_rule lean_term(Nat.add_zero n) variant 0 phase pre rev extra 0 at [1] with []]
  rfl

/- A polymorphic source application is elaborated while Lean matches the exact
recorded redex, so the redex fixes the otherwise-stuck cast carrier. -/
example (p : Prop) [Decidable p] (x y : Nat) :
    ((↑(if p then x else y) : Int)) = if p then (↑x : Int) else ↑y := by
  explicit_rw_v2 [source_rule lean_term(apply_ite Nat.cast) variant 0 phase post fwd extra 0
    at [0, 1] with []]
  rfl

/- `local_ref` selects a declaration by its local-context identity rather than
   by searching for a theorem of a compatible type. In this Lean local context,
   `h` is declaration 2. -/
example (n : Nat) (h : n = n) : n = n := by
  explicit_rw_v2 [local local_ref 2 variant 0 phase dpre fwd extra 0 at [0, 1] with []]
  rfl

private theorem conditionalRule (n : Nat) (h : n = 0) : n + 0 = 0 :=
  Eq.trans (Nat.add_zero n) h

/- Premises are discharged in the explicitly listed order. -/
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  explicit_rw_v2 [rule conditionalRule variant 0 phase pre fwd extra 0 at [0, 1] with [assumption h]]
  rfl

example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  explicit_rw_v2 [rule conditionalRule variant 0 phase pre fwd extra 0 at [0, 1] with [assumption local_ref 2]]
  rfl

/- A premise may itself be discharged by the exact recursive operation stream
that simp used, rather than by a guessed theorem search. -/
example (n : Nat) : (if n + 0 = n then 1 else 2) = 1 := by
  explicit_rw_v2 [rule if_pos variant 0 phase pre fwd extra 0 at [0, 1] with [
    explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 at [0, 1] with []]
      then rfl]]
  rfl

private def replayNestedPremiseProp (n : Nat) : Prop := n + 0 = n

private theorem replayNestedPremiseRule (n : Nat) (h : n + 0 = n) :
    replayNestedPremiseProp n := h

/- This is the exact recursive shape emitted by the recorder probe, including
the simplifier's explicit metavariable-instantiation operation and terminal. -/
example (n : Nat) : replayNestedPremiseProp n := by
  explicit_rw_v2 [rule replayNestedPremiseRule variant 0 phase post fwd extra 0 at [] with [
    explicit_rw_v2 [instantiate at [0, 1, 0, 1],
      rule Nat.add_zero variant 0 phase post fwd extra 0 at [0, 1] with [],
      rule eq_self variant 0 phase post fwd extra 0 at [] with []] then true_intro]] then true_intro

/- A cache hit is explicit and carries the exact source operations that first
produced the cached result. They are replayed relative to the new occurrence. -/
example (n : Nat) : (n + 0) + 0 = n := by
  explicit_rw_v2 [cached [rule Nat.add_zero variant 0 phase post fwd extra 0 at [] with []]
    at [0, 1, 0, 1], rule Nat.add_zero variant 0 phase post fwd extra 0 at [0, 1] with []]
  rfl

private theorem operationalNotCongr (p q : Prop) (h : p ↔ q) : (¬p) ↔ (¬q) := not_congr h

/- A named congruence theorem states its exact proposition argument index. The
side program fixes the theorem's right-hand proposition without search. -/
example (n : Nat) : (¬(n + 0 = n)) = False := by
  explicit_rw_v2 [congr_rule operationalNotCongr at [0, 1] with [arg 2
    explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 at [0, 1, 0, 1] with [],
      rule eq_self variant 0 phase post fwd extra 0 at [0, 1] with []] then rfl],
    rule not_true_eq_false variant 0 phase post fwd extra 0 at [0, 1] with []]
  rfl

/- Definitional operations share the same path semantics. -/
example (n : Nat) : n = n := by
  explicit_rw_v2 [instantiate at []]
  rfl

example (n : Nat) : (fun x : Nat => x) n = n := by
  explicit_rw_v2 [beta at [0, 1]]
  rfl

private def deltaTarget (n : Nat) : Nat := n + 0

example (n : Nat) : deltaTarget n = n + 0 := by
  explicit_rw_v2 [unfold deltaTarget at [0, 1]]
  rfl

/- These three operations delegate to the existing exact single-step
   `explicitRwStep` implementations. -/
example : Nat.rec 1 (fun _ _ => 2) 0 = 1 := by
  explicit_rw_v2 [iota at [0, 1]]
  rfl

example : (Nat.succ 0, Nat.succ 1).1 = Nat.succ 0 := by
  explicit_rw_v2 [proj at [0, 1]]
  rfl

example (n : Nat) : (let x := n; x) = n := by
  explicit_rw_v2 [zeta at [0, 1]]
  rfl

private def operationalEquationTarget : Nat → Nat
  | 0 => 0
  | n + 1 => n

example : operationalEquationTarget 0 = 0 := by
  explicit_rw_v2 [equation operationalEquationTarget index 0 variant 0 phase pre fwd extra 0 at [0, 1] with []]
  rfl

private def operationalIdentity : Nat → Nat := fun n => n
private theorem operationalIdentity_eq_id : operationalIdentity = id := by rfl

/- `extra 1` extends the exact base path by one function child, rewriting only
   the selected application's head and rebuilding it with congruence. -/
example (n : Nat) : operationalIdentity n = n := by
  explicit_rw_v2 [rule operationalIdentity_eq_id variant 9 phase dpre fwd extra 1 at [0, 1] with []]
  rfl

/- The actual two-step simp shape: after the direct term rewrite, `eq_self` is
   recognized by its exact instantiated proposition type and maps that node to
   `True`; the terminal is a closed opcode, not a term payload. -/
example (n : Nat) : n + 0 = n := by
  explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 at [0, 1] with [],
    rule eq_self variant 0 phase post fwd extra 0 at [] with []] then true_intro

/- A named local negative proposition rule performs the corresponding exact
   `P → False` operation. -/
example (p : Prop) (h : ¬ p) : p = False := by
  explicit_rw_v2 [local h variant 0 phase pre fwd extra 0 at [0, 1] with []]
  rfl

/- Optional v2 locations address exactly one named hypothesis. -/
example (n : Nat) (h : n + 0 = n) : n = n := by
  explicit_rw_v2 [rule Nat.add_zero variant 0 phase pre fwd extra 0 at [0, 1] with []] at h
  exact h

example (h : (0 : Nat) = 1) : False := by
  explicit_rw_v2 [rule Nat.zero_ne_one variant 0 phase post fwd extra 0 at [] with []]
    at h then false_elim

example (n : Nat) (h : n + 0 = n) : n = n := by
  explicit_rw_v2 [rule Nat.add_zero variant 0 phase pre fwd extra 0 at [0, 1] with []]
    at local_ref 2
  exact h

/- The selected node does not match, although matching redexes exist elsewhere.
   The operation fails at the recorded path instead of searching the goal. -/
/-- error: explicit_rw_v2: step 1: lemma `Nat.add_zero` does not match the subterm at position [0, 0] -/
#guard_msgs(error, drop info, drop warning, substring := true) in
example (n m : Nat) : n + 0 = m + 0 := by
  explicit_rw_v2 [rule Nat.add_zero variant 0 phase pre fwd extra 0 at [0, 0] with []]

/- A global declaration operand does not fall back to a local theorem search. -/
/-- error: explicit_rw_v2: step 1: Unknown constant `missingRule` -/
#guard_msgs(error, drop info, drop warning, substring := true) in
example (n : Nat) (h : n + 0 = n) : n + 0 = n := by
  explicit_rw_v2 [rule missingRule variant 0 phase pre fwd extra 0 at [0, 1] with []]

/- The same rule with an omitted proof premise is not discharged by finding the
   matching local hypothesis. -/
/-- error: explicit_rw_v2: step 1: lemma `conditionalRule` still has an unassigned argument of type -/
#guard_msgs(error, drop info, drop warning, substring := true) in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  explicit_rw_v2 [rule conditionalRule variant 0 phase pre fwd extra 0 at [0, 1] with []]

/- A simproc operation is parsed so the interpreter can reject it directly; it
   is never invoked or reconstructed. -/
/-- error: explicit_rw_v2: simproc `fixtureProc` is not a rewrite-rule operation. -/
#guard_msgs(error, drop info, drop warning, substring := true) in
example : True := by
  explicit_rw_v2 [simproc fixtureProc at []]

end ExplicitLean.SimpTrace.T79OperationalReplay
