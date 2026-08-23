import ExplicitLean.SimpEngine.Recording

open Lean Meta Elab Tactic

def requestedDelta (n : Nat) : Nat := n + 0

opaque Holds : Prop → Prop

axiom holdsTrue : Holds True

@[congr] theorem Holds.congr {p q : Prop} (h : p = q) : Holds p = Holds q :=
  congrArg Holds h

theorem guardedRule {p q : Prop} (h : p → q) : p → q := h

theorem falseGuardedAdd {n : Nat} (_ : False) : n + 0 = n := Nat.add_zero n

elab "check_premise_trace_delta" : tactic => withMainContext do
  let simpStx ← `(tactic|
    simp (config := { failIfUnchanged := false }) [falseGuardedAdd])
  let recording ← ExplicitLean.SimpEngine.Recording.recordCertificate simpStx.raw
  let count := recording.certificate.subjects.foldl (init := 0) fun total subject =>
    total + subject.simprocs.size
  unless count == 18 do
    throwError "premise recording duplicated or dropped simproc observations: expected 18, got {count}"
  logInfo m!"SIMP_ENGINE_PREMISE_TRACE simprocs={count}"

opaque SeeProp : Prop → Prop
opaque SeeNat : Nat → Prop
opaque SeeInt : Int → Prop
opaque SeeFin {n : Nat} : Fin n → Prop
opaque Depends {p : Prop} : p → Prop
opaque SeeUInt8 : UInt8 → Prop

example (xs : List Nat) : (fun ys => ys ++ []) xs = xs := by
  simp_engine_recording

example (x : Nat) : (x + 0, x + 0) = (x, x) := by
  simp_engine_recording

example (n : Nat) : (match some n with | some k => k + 0 | none => 0) = n := by
  simp_engine_recording

example (p : Nat × Nat) : (p.1, p.2) = p := by
  simp_engine_recording

example (p : Nat × Nat) : Prod.fst p = p.1 := by
  simp_engine_recording

example (x : Nat) : requestedDelta x = x := by
  simp_engine_recording [requestedDelta]

example (x : Nat) : (let unused := 1; x + 0) = x := by
  simp_engine_recording

example : (fun y : Nat => y + 0) = fun y => y := by
  simp_engine_recording

example (P : Nat → Prop) : (∀ n, P n ∧ True) ↔ ∀ n, P n := by
  simp_engine_recording

example (p q : Prop) (h : p → q) : p → q := by
  simp_engine_recording (config := { contextual := true }) [h]

example (p q : Prop) (h : p) (hpq : p → q) : q := by
  simp_engine_recording (disch := assumption) [hpq]

example (n : Nat) : n + 0 = n := by
  check_premise_trace_delta
  simp_engine_recording (config := { failIfUnchanged := false })
    (disch := assumption) only [falseGuardedAdd]
  exact Nat.add_zero n

example : Holds (True ∧ True) := by
  simp_engine_recording
  exact holdsTrue

example : (20 : Nat) < 30 := by
  simp_engine_recording +decide

example (x : Int) : x + x + 0 = 2 * x := by
  simp_engine_recording +arith

example : List.length ([1, 2, 3].map (· + 1)) = 3 := by
  simp_engine_recording +ground

example (x : Nat) : (have y := x + 0; y) = x := by
  simp_engine_recording (config := { zeta := false })
  simp

example (p : Prop) (h : p) : (have hp : p := h; True) := by
  simp_engine_recording (config := { zeta := false, zetaUnused := true })

example (p q : Prop) (h : SeeProp (p → q)) : SeeProp (p → q) := by
  simp_engine_observe
  exact h

example (h : SeeProp (∀ x : True ∧ True, Depends x)) :
    SeeProp (∀ x : True ∧ True, Depends x) := by
  simp_engine_observe
  exact h

example (p : Nat × Nat) (h : SeeNat p.1) : SeeNat p.1 := by
  simp_engine_observe
  exact h

example {n : Nat} (a : Fin n) (h : SeeFin (Fin.mk a.val a.isLt)) :
    SeeFin (Fin.mk a.val a.isLt) := by
  simp_engine_observe
  exact h

example (x : Int) (h : SeeInt (x + x)) : SeeInt (x + x) := by
  simp_engine_observe (config := { arith := true })
  exact h

example (x : Nat) (h : x + 0 = x) : True := by
  simp_engine_recording at h ⊢

example (h : False) : True := by
  simp_engine_recording at h

example (h : SeeUInt8 ((1 : UInt8) + 2)) : SeeUInt8 ((1 : UInt8) + 2) := by
  dsimp_engine_observe
  exact h
