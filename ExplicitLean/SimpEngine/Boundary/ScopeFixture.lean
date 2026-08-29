module

import Mathlib

namespace SimpEngineScopeFixture

theorem scopeTheorem (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]

def scopeProofDef (n : Nat) : n + 0 = n := by
  simp only [Nat.add_zero]

def scopeComputational (n : Nat) : Nat := by
  simp (config := { failIfUnchanged := false }) only
  exact n

def scopePropData : Prop := by
  simp (config := { failIfUnchanged := false }) only
  exact True

structure ScopeRecord where
  value : Nat
  proof : value = value

def scopeStructure (n : Nat) : ScopeRecord :=
  { value := n
    proof := by simp }

macro "scope_reusable" : tactic =>
  `(tactic| simp only [Nat.add_zero])

theorem scopeMacroUse (n : Nat) : n + 0 = n := by
  scope_reusable

-- Anonymous examples are renamed only in temporary scope-classification
-- copies, so the report can resolve their final declaration type.
example : (0 : Nat) = 0 := by
  simp

example : Nat := by
  simp (config := { failIfUnchanged := false }) only
  exact 0

-- The proof field belongs to a computational irreducible definition and is
-- excluded by the static command ancestry rule.
irreducible_def scopeIrreducible : ScopeRecord :=
  { value := 0
    proof := by simp }

-- This tactic is part of a declaration signature, not a proof body.
variable (scopeVariableSignature : Nat := by simp)

-- A generated theorem is elaborated by a nested command quotation. The
-- temporary scope probe must carry the source occurrence ID through it.
set_option hygiene false in
run_cmd
  Lean.Elab.Command.elabCommand (← `(
    theorem scopeGeneratedFromRunCmd : (0 : Nat) = 0 := by
      simp
  ))

set_option hygiene false in
run_cmd
  Lean.Elab.Command.elabCommand (← `(
    def scopeGeneratedDataFromRunCmd : Nat := by
      simp (config := { failIfUnchanged := false }) only
      exact 0
  ))

-- This check intentionally retains a tactic quotation as syntax data instead
-- of executing it as part of a proof body.
#check `(tactic| simp only [Nat.add_zero])

end SimpEngineScopeFixture
