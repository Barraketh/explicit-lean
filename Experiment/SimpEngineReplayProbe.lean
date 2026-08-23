import ExplicitLean.SimpEngine.Replay

open Lean Meta Elab Tactic

def replayDelta (n : Nat) : Nat := n + 0

opaque ReplayHolds : Prop → Prop
axiom replayHoldsTrue : ReplayHolds True

opaque ReplaySeeProp : Prop → Prop
opaque ReplaySeeFin {n : Nat} : Fin n → Prop
opaque ReplayDepends {p : Prop} : p → Prop
axiom replaySeePropTrue : ReplaySeeProp (∀ x : True, ReplayDepends x)
axiom replaySeeArrow (p q : Prop) : ReplaySeeProp (p → q)

elab "check_engine_terminals_replay" : tactic => withMainContext do
  let ctx ← Simp.mkContext (simpTheorems := {}) (congrTheorems := {})
  let methods := Simp.Engine.mkDefaultMethodsCore {}
  let proofExpression := mkConst ``True.intro
  let (_, _, proofRecording) ←
    Simp.Engine.mainCoreRecording proofExpression ctx (methods := methods)
  unless proofRecording.coveredBranches.contains "struct.proofSkip" do
    throwError "proof fixture missed its structural terminal"
  let config ← Simp.Engine.replayConfigOfContext ctx
  let _ ← Simp.Engine.mainCoreReplay proofExpression ctx config proofRecording.program
  let mvarExpression ← mkFreshExprMVar (mkConst ``Nat)
  let (_, _, mvarRecording) ←
    Simp.Engine.mainCoreRecording mvarExpression ctx (methods := methods)
  unless mvarRecording.coveredBranches.contains "struct.unassignedMVarStop" do
    throwError "unassigned mvar fixture missed its structural terminal"
  let _ ← Simp.Engine.mainCoreReplay mvarExpression ctx config mvarRecording.program
  let branches := proofRecording.coveredBranches ++ mvarRecording.coveredBranches
  logInfo m!"SIMP_ENGINE_REPLAY branches={String.intercalate "," branches.toList}"

opaque replayPairAdd : Nat → Nat → Nat
axiom replayTwoPremises {a b : Nat} (ha : a = 0) (hb : b = 0) :
  replayPairAdd a b = 0

@[congr] theorem ReplayHolds.congr {p q : Prop} (h : p = q) :
    ReplayHolds p = ReplayHolds q := congrArg ReplayHolds h

example (xs : List Nat) : xs ++ [] = xs := by
  simp_engine_replay only [List.append_nil]

example (x : Nat) : (fun y => y) x = x := by
  simp_engine_replay only

example (x : Nat) : replayDelta x = x := by
  simp_engine_replay only [replayDelta, Nat.add_zero]

example (x : Nat) : (x + 0, x + 0) = (x, x) := by
  simp_engine_replay only [Nat.add_zero]

example (n : Nat) : (match some n with | some k => k + 0 | none => 0) = n := by
  simp_engine_replay

example (p : Nat × Nat) : (p.1, p.2) = p := by
  simp_engine_replay

example (p : Nat × Nat) : Prod.fst p = p.1 := by
  simp_engine_replay

example (p q : Prop) (h : p → q) : p → q := by
  simp_engine_replay (config := { contextual := true }) only [h]
  intro
  trivial

example : True := by
  check_engine_terminals_replay
  trivial

example : (fun y : Nat => y + 0) = fun y => y := by
  simp_engine_replay

example (P : Nat → Prop) : (∀ n, P n ∧ True) ↔ ∀ n, P n := by
  simp_engine_replay

example (p q : Prop) : ReplaySeeProp (p ∧ True → q) := by
  simp_engine_replay only [and_true]
  exact replaySeeArrow p q

example (p q : Prop) (h : p) (hpq : p → q) : q := by
  simp_engine_replay only [hpq, h]

example (a b : Nat) (ha : a = 0) (hb : b = 0) : replayPairAdd a b = 0 := by
  simp_engine_replay only [replayTwoPremises, ha, hb]

example : ReplayHolds (True ∧ True) := by
  simp_engine_replay
  exact replayHoldsTrue

example (h : ReplaySeeProp (∀ x : True ∧ True, ReplayDepends x)) :
    ReplaySeeProp (∀ x : True ∧ True, ReplayDepends x) := by
  simp_engine_replay
  exact replaySeePropTrue

example {n : Nat} (a : Fin n) (h : ReplaySeeFin (Fin.mk a.val a.isLt)) :
    ReplaySeeFin (Fin.mk a.val a.isLt) := by
  simp_engine_replay
  exact h

example (x : Nat) : (have y := x + 0; y) = x := by
  simp_engine_replay (config := { zeta := false }) only [Nat.add_zero]
  rfl

example (p : Prop) (h : p) : (have hp : p := h; True) := by
  simp_engine_replay (config := { zeta := false, zetaUnused := true })

example (x : Nat) (h : x + 0 = x) : True := by
  simp_engine_replay at h ⊢

example (h : False) : True := by
  simp_engine_replay at h

example : (20 : Nat) < 30 := by
  simp_engine_replay +decide

example (x : Int) : x + x + 0 = 2 * x := by
  simp_engine_replay +arith
