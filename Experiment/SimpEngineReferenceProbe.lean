import ExplicitLean.SimpEngine.Reference

def requestedDelta (n : Nat) : Nat := n + 0

opaque Holds : Prop → Prop

axiom holdsTrue : Holds True

@[congr] theorem Holds.congr {p q : Prop} (h : p = q) : Holds p = Holds q :=
  congrArg Holds h

theorem guardedRule {p q : Prop} (h : p → q) : p → q := h

example (xs : List Nat) : (fun ys => ys ++ []) xs = xs := by
  simp_engine_reference

example (x : Nat) : (x + 0, x + 0) = (x, x) := by
  simp_engine_reference

example (n : Nat) : (match some n with | some k => k + 0 | none => 0) = n := by
  simp_engine_reference

example (p : Nat × Nat) : (p.1, p.2) = p := by
  simp_engine_reference

example (p : Nat × Nat) : Prod.fst p = p.1 := by
  simp_engine_reference

example (x : Nat) : requestedDelta x = x := by
  simp_engine_reference [requestedDelta]

example (x : Nat) : (let unused := 1; x + 0) = x := by
  simp_engine_reference

example (x : Nat) : (fun y : Nat => y + 0) x = x := by
  simp_engine_reference

example : (fun y : Nat => y + 0) = fun y => y := by
  simp_engine_reference

example (P : Nat → Prop) : (∀ n, P n ∧ True) ↔ ∀ n, P n := by
  simp_engine_reference

example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  simp_engine_reference [h]

example (p q : Prop) (h : p → q) : p → q := by
  simp_engine_reference (config := { contextual := true }) [h]

example (p q : Prop) (h : p) (hpq : p → q) : q := by
  simp_engine_reference (disch := assumption) [hpq]

example : Holds (True ∧ True) := by
  simp_engine_reference
  exact holdsTrue

example : (20 : Nat) < 30 := by
  simp_engine_reference +decide

example (x : Int) : x + x + 0 = 2 * x := by
  simp_engine_reference +arith

example : List.length ([1, 2, 3].map (· + 1)) = 3 := by
  simp_engine_reference +ground

example (x : Nat) : (have y := x + 0; y) = x := by
  simp_engine_reference (config := { zeta := false })
  simp

example (p : Prop) (h : p) : (have hp : p := h; True) := by
  simp_engine_reference (config := { zeta := false, zetaUnused := true })

example (x : Nat) : (let y := x + 0; y) = x := by
  dsimp_engine_reference

example (x : Nat) : (let y := x + 0; y) = x := by
  simp_engine_reference_assigned_mvar
  simp

example (x : Nat) : id (id x) = x := by
  simp_engine_reference (config := { index := false, implicitDefEqProofs := false }) only [id_eq]
