/-
Every term `explicit_rw` elaborates must fail *loudly*.

Round 6 found a false theorem admitted through the one elaboration site that
lacked a `sorry` guard: Lean reports many failures as *recoverable* errors,
logging a message and returning a `sorryAx`-typed expression rather than
throwing. The surrounding `by` block was then abandoned with no diagnostic, and
`lake env lean` exited 0 on `theorem false_thm : (1 : Nat) = 2`.

Guarding one call site at a time is how that hole survived two rounds, so all
four sites now go through `elabStrict`. These fixtures pin that each of them
rejects, including the `eq` slot that shipped the false theorem.
-/
import ExplicitLean.ExplicitRw

namespace ExplicitRwTest.Strict

/-! ## The critical case: the `eq` slot must not admit a false theorem -/

/-- error: explicit_rw: step 1: Unknown identifier `unknownIdent` -/
#guard_msgs(error, drop info, drop warning) in
example : (1 : Nat) = 2 := by
  explicit_rw [eq (unknownIdent = (2:Nat)) by rfl at [0, 1]]

/-! ## The other elaboration sites -/

/-- error: explicit_rw: step 1: Unknown identifier `nosuchlemma` -/
#guard_msgs(error, drop info, drop warning) in
example (a b : Nat) : a = b := by
  explicit_rw [nosuchlemma at [0, 1]]

/-- error: explicit_rw: step 1: Unknown identifier `nosucharg` -/
#guard_msgs(error, drop info, drop warning) in
example (a b : Nat) : a + 0 = b := by
  explicit_rw [Nat.add_zero nosucharg at [0, 1]]

/-- error: explicit_rw: step 1: Unknown identifier `nosuchterm` -/
#guard_msgs(error, drop info, drop warning) in
example (a : Nat) : a + 0 = a := by
  explicit_rw [change (nosuchterm) at [0, 1]]

/-- error: explicit_rw: step 1: Unknown identifier `nosuchproof` -/
#guard_msgs(error, drop info, drop warning) in
example (n : Nat) (hn : 5 ≤ n) : (n - 5) + 5 = n := by
  explicit_rw [Nat.sub_add_cancel _ at [0, 1] with [exact nosuchproof]]

/-- error: Unknown identifier `nosuchcloser` -/
#guard_msgs(error, drop info, drop warning) in
example (a b : Nat) : a = b := by
  explicit_rw [] then exact nosuchcloser

/-! ## A hole left in a term is rejected, not silently instantiated

`elabStrict` refuses a result that still carries an expression or universe
metavariable at a site that must be closed, so an `eq` equation cannot ship a
`?m` into the proof.
-/

/-- error: explicit_rw: step 1: the `eq` equation of this step still contains an unassigned metavariable after elaboration:
  ?m.8 = 2 -/
#guard_msgs(error, drop info, drop warning) in
example : (1 : Nat) = 2 := by
  explicit_rw [eq (_ = (2:Nat)) by rfl at [0, 1]]

/-! ## Sorts are discriminated, not collapsed to `Sort _`

Round 5 fixed the sort productions but committed only *accepting* fixtures, all
of which pass equally well with the `Sort _` bug, since `Sort _` unifies with
anything. This is the discriminating case: `change Type` at a `Prop` position
must be **refused**, while `change (Sort 0)` at the same position is accepted
because `Sort 0` really is `Prop`.
-/

/--
error: explicit_rw: step 1: Type mismatch
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1`
-/
#guard_msgs(error, drop info, drop warning) in
example : (fun (_α : Prop) => True) True := by
  explicit_rw [change (Type) at [0, 0]]
  exact trivial

/-- `Sort 0` *is* `Prop`, so the same position accepts it. -/
theorem sort0_accepted_at_prop : (fun (_α : Prop) => True) True := by
  explicit_rw [change (Sort 0) at [0, 0]] then exact True.intro

/-- `Type` is accepted where the position really is a `Type`. -/
theorem type_accepted_at_type : (fun (_α : Type) => True) Nat := by
  explicit_rw [change (Type) at [0, 0]] then exact True.intro

/-- `Type*`, `Sort*` and `Type u` remain distinguishable spellings. -/
theorem sort_star_and_universe : (fun (_α : Type) => True) Nat := by
  explicit_rw [change (Type*) at [0, 0], change (Sort*) at [0, 0],
               change (Type 0) at [0, 0]] then exact True.intro

/-- `Prop` at a `Prop` position. -/
theorem prop_at_prop : (fun (_α : Prop) => True) True := by
  explicit_rw [change (Prop) at [0, 0]] then exact True.intro

end ExplicitRwTest.Strict
