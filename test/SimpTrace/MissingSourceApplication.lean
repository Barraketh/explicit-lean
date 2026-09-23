import ExplicitLean.SimpTrace
import Mathlib.Data.Set.Basic
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Rep.Res

namespace ExplicitLean.SimpTrace.MissingSourceApplication

open Lean Lean.Meta ExplicitLean.SimpTrace

def WrappedFunction : Type := Nat → Nat
def WrappedArgument (n : Nat) : Nat := n
def ImplicitWrappedFunction : Type 1 := {α : Type} → α → Nat
opaque OpaqueFunctionType : Type := Nat → Nat

/- Direct adversarial coverage of the source-hole predicate. The function type
and nested argument are behind ordinary `def`s, while the implicit parameter
is an unassigned metavariable that must remain allowed. -/
run_cmd do
  Lean.Elab.Command.liftTermElabM do
    let simpCtx ← Simp.Context.mkDefault
    let (_, _) ← Simp.SimpM.run simpCtx {} {} do
      withLocalDeclD `f (mkConst ``WrappedFunction) fun f => do
        let hole ← mkFreshExprMVar (mkConst ``Nat)
        unless ← hasExplicitSourceHole (mkApp f hole) do
          throwError "explicit source metavariable behind a semireducible function type was accepted"
        if ← hole.mvarId!.isAssigned then
          throwError "source-hole validation assigned the explicit argument metavariable"
      withLocalDeclD `f (mkConst ``WrappedFunction) fun f => do
        let hole ← mkFreshExprMVar (mkConst ``Nat)
        let hidden := mkApp (mkConst ``WrappedArgument) hole
        unless ← hasExplicitSourceHole (mkApp f hidden) do
          throwError "explicit source metavariable nested under a definition was accepted"
        if ← hole.mvarId!.isAssigned then
          throwError "source-hole validation assigned the nested argument metavariable"
      withLocalDeclD `f (mkConst ``ImplicitWrappedFunction) fun f => do
        let implicitType ← mkFreshExprMVar (mkSort (.succ .zero))
        withLocalDeclD `x implicitType fun x => do
          let source := mkAppN f #[implicitType, x]
          if ← hasExplicitSourceHole source then
            throwError "an unassigned implicit parameter incorrectly counted as an explicit source hole"
          if ← implicitType.mvarId!.isAssigned then
            throwError "source-hole validation assigned the implicit parameter metavariable"
      let unknownType ← mkFreshExprMVar (mkSort (.succ .zero))
      withLocalDeclD `f unknownType fun f => do
        let hole ← mkFreshExprMVar (mkConst ``Nat)
        unless ← hasExplicitSourceHole (mkApp f hole) do
          throwError "an application with an unresolved function type did not fail closed"
        if ← unknownType.mvarId!.isAssigned then
          throwError "source-hole validation assigned an unresolved function type"
        if ← hole.mvarId!.isAssigned then
          throwError "source-hole validation assigned an argument under an unresolved function type"
      withLocalDeclD `f (mkConst ``OpaqueFunctionType) fun f => do
        let hole ← mkFreshExprMVar (mkConst ``Nat)
        unless ← hasExplicitSourceHole (mkApp f hole) do
          throwError "an opaque, uninspectable function type did not fail closed"

example {α : Type} (f : Nat → α) (g : Nat) (x : α)
    (hv : ∀ n, n = g → f n = x) : f g = x := by
  simp_trace only [hv g rfl] =>trace "T77_MISSING_APPLIED_LOCAL"

example {α : Type} (f : Nat → α) (g : Nat) (x : α) (hv : ∀ n, f n = x) : f g = x := by
  simp_trace only [hv g] =>trace "T77_MISSING_FORALL_LOCAL"

example {P : Nat → Nat → Prop}
    (h : Membership.mem (setOf fun n : Nat => ∀ g : Nat, P n g) 0) : P 0 3 := by
  simp_trace only [h 3] =>trace "T77_MISSING_MEMBERSHIP_LOCAL"

example (h : ∀ s : Nat, ∃ y : Nat, y = s) (s : Nat) : (h s).choose = s := by
  simp_trace only [(h s).choose_spec] =>trace "T77_MISSING_CHOOSE_SPEC"

example {p : Nat → Prop} (x : {n : Nat // p n}) : p x.val := by
  simp_trace only [x.property] =>trace "T77_MISSING_SUBTYPE_PROPERTY"

example (f : Nat → Nat) (n : Nat) (h : f n = n) : f n = n := by
  simp_trace only [show f n = n from h] =>trace "T77_MISSING_SHOW_FROM"

example (p q : Prop) (h : p ∧ q) : p ∧ q := by
  simp_trace only [h] =>trace "T77_MISSING_MULTIPLE_THEOREMS"
  exact ⟨trivial, trivial⟩

end ExplicitLean.SimpTrace.MissingSourceApplication

/- Exact source-application shape from
`Mathlib.RepresentationTheory.Invariants.add_mem'`. -/
namespace ExplicitLean.SimpTrace.MissingSourceApplication.RepresentationInvariants

universe w u v

open MonoidAlgebra Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

def invariants : Submodule k V where
  carrier := setOf fun v => ∀ g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by
    simp_trace only [hv g, hw g, map_add] =>trace "T77_REPRESENTATION_INVARIANTS"
  smul_mem' r v hv g := by simp only [hv g, map_smul]

end ExplicitLean.SimpTrace.MissingSourceApplication.RepresentationInvariants
