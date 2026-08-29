import ExplicitLean.SimpEngine.Boundary
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Lean Elab Command

theorem boundaryStockTransport
    (P : Nat → Prop) (n : Nat) (h : P n) : P (n + 0) := by
  simp only [Nat.add_zero]
  exact h

theorem boundaryReplacementTransport
    (P : Nat → Prop) (n : Nat) (h : P n) : P (n + 0) := by
  simp_engine_boundary_probe only [Nat.add_zero]
  exact h

theorem boundaryStockClosed (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]

theorem boundaryReplacementClosed (n : Nat) : n + 0 = n := by
  simp_engine_boundary_probe only [Nat.add_zero]

theorem boundaryStockHypothesis
    (P : Nat → Prop) (n : Nat) (h : P (n + 0)) : P n := by
  simp only [Nat.add_zero] at h
  exact h

theorem boundaryReplacementHypothesis
    (P : Nat → Prop) (n : Nat) (h : P (n + 0)) : P n := by
  simp_engine_boundary_probe only [Nat.add_zero] at h
  exact h

theorem boundaryStockFalseHypothesis (h : (0 : Nat) = 1) : True := by
  simp only [Nat.zero_ne_one] at h

theorem boundaryReplacementFalseHypothesis (h : (0 : Nat) = 1) : True := by
  simp_engine_boundary_probe only [Nat.zero_ne_one] at h

run_cmd do
  let pairs : Array (Name × Name) := #[
    (`boundaryStockTransport, `boundaryReplacementTransport),
    (`boundaryStockClosed, `boundaryReplacementClosed),
    (`boundaryStockHypothesis, `boundaryReplacementHypothesis),
    (`boundaryStockFalseHypothesis, `boundaryReplacementFalseHypothesis)
  ]
  let environment ← getEnv
  for (stockName, replacementName) in pairs do
    let some stockInfo := environment.find? stockName
      | throwError "missing stock declaration: {stockName}"
    let some replacementInfo := environment.find? replacementName
      | throwError "missing replacement declaration: {replacementName}"
    unless stockInfo.type == replacementInfo.type do
      throwError "declaration type mismatch: {stockName} / {replacementName}"
    let stockAxioms ← Lean.collectAxioms stockName
    let replacementAxioms ← Lean.collectAxioms replacementName
    unless replacementAxioms.all stockAxioms.contains do
      throwError "replacement axiom set is not a subset: {stockName} / {replacementName}"
    if replacementAxioms.contains ``sorryAx then
      throwError "replacement depends on sorryAx: {replacementName}"
  logInfo "SIMP_ENGINE_BOUNDARY_TRUST equivalent_types=true axiom_subset=true sorry_free=true"
