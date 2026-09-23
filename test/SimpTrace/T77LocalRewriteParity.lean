import ExplicitLean.SimpTrace
import ExplicitLean.ExplicitRw

open Lean Lean.Meta

namespace ExplicitLean.SimpTrace.T77LocalRewriteParity

/-- A bare local quantified theorem uses the same selected-redex matching in
the recorder validator and the ordinary positional rewriter. -/
example {α : Type} {i j : α → α} (h : Function.LeftInverse i j) (x : α) :
    i (j x) = x := by
  explicit_rw [h at [0, 1]] then rfl

/-- An explicit proof binder is replayed only when its ordered side evidence
has the exact proposition type required by the source theorem. -/
example (f g : Nat → Nat)
    (h : ∀ x : Nat, x = x → f x = g x) (x : Nat) : f x = g x := by
  explicit_rw [h at [0, 1] with [rfl]] then rfl

run_cmd do
  Lean.Elab.Command.liftTermElabM do
    withLocalDeclD `α (mkSort (Level.succ Level.zero)) fun α => do
      let fnTy ← mkArrow α α
      withLocalDeclD `i fnTy fun i => do
        withLocalDeclD `j fnTy fun j => do
          withLocalDeclD `x α fun x => do
            let jx := mkApp (mkFVar j.fvarId!) x
            let lhs := mkApp (mkFVar i.fvarId!) jx
            let hType ← mkAppM ``Function.LeftInverse #[i, j]
            withLocalDeclD `h hType fun h => do
              let proof := mkApp h x
              let lctx ← getLCtx
              let insts ← getLocalInstances
              let reason ← checkRwStep (.fvar h.fvarId!) #[] false none
                lhs x { lctx := lctx, insts := insts } #[] "" (some proof)
                (localEvidence := true)
              unless reason.isNone do
                throwError "bare Function.LeftInverse evidence was rejected: {reason}"

run_cmd do
  Lean.Elab.Command.liftTermElabM do
    withLocalDeclD `x (mkConst ``Nat) fun x => do
      let xEqX ← mkEq x x
      withLocalDeclD `y (mkConst ``Nat) fun y => do
        let hType ← mkForallFVars #[x, y] xEqX
        withLocalDeclD `h hType fun h => do
          let proof := mkAppN h #[x, mkNatLit 0]
          let lctx ← getLCtx
          let ctx : EvCtx := { lctx := lctx, insts := (← getLocalInstances) }
          let noSide ← checkRwStep (.fvar h.fvarId!) #[] false (some true)
            xEqX (mkConst ``True) ctx #[] "" (some proof) (localEvidence := true)
          unless noSide.any (String.startsWith · "unassigned_explicit_argument:") do
            throwError "an unrelated explicit binder was accepted without side evidence: {noSide}"
          let irrelevantSide : SideRec :=
            .mk (mkConst ``True) #[] (some "true_intro") ctx #[]
              (mkConst ``True) (some (mkConst ``True))
          let withWrongSide ← checkRwStep (.fvar h.fvarId!) #[] false (some true)
            xEqX (mkConst ``True) ctx #[irrelevantSide] "" (some proof)
            (localEvidence := true)
          unless withWrongSide.any
              (String.startsWith · "unassigned_explicit_argument:") do
            throwError "an unrelated Nat binder was treated as side evidence: {withWrongSide}"

run_cmd do
  Lean.Elab.Command.liftTermElabM do
    withLocalDeclD `α (mkSort (Level.succ Level.zero)) fun α => do
      let fnTy ← mkArrow α α
      withLocalDeclD `i fnTy fun i => do
        withLocalDeclD `j fnTy fun j => do
          withLocalDeclD `x α fun x => do
            let xx ← mkEq x x
            withLocalDeclD `hx xx fun hx => do
              let lhs := mkApp (mkFVar i.fvarId!) x
              let rhs := mkApp (mkFVar j.fvarId!) x
              let hType ← mkForallFVars #[x, hx] (← mkEq lhs rhs)
              withLocalDeclD `h hType fun h => do
                let proof := mkAppN h #[x, hx]
                let lctx ← getLCtx
                let ctx : EvCtx := { lctx := lctx, insts := (← getLocalInstances) }
                let side : SideRec := .mk xx #[] (some "rfl") ctx #[] xx (some xx)
                let reason ← checkRwStep (.fvar h.fvarId!) #[] false none
                  lhs rhs ctx #[side] "" (some proof) (localEvidence := true)
                unless reason.isNone do
                  throwError "matching typed side evidence was rejected: {reason}"
                let wrongSide : SideRec :=
                  .mk (mkConst ``True) #[] (some "true_intro") ctx #[]
                    (mkConst ``True) (some (mkConst ``True))
                let mismatch ← checkRwStep (.fvar h.fvarId!) #[] false none
                  lhs rhs ctx #[wrongSide] "" (some proof) (localEvidence := true)
                unless mismatch.any
                    (String.startsWith · "unassigned_explicit_argument:") do
                  throwError "a mismatched side goal was accepted: {mismatch}"

run_cmd do
  Lean.Elab.Command.liftTermElabM do
    withLocalDeclD `α (mkSort (Level.succ Level.zero)) fun α => do
      let fnTy ← mkArrow α α
      withLocalDeclD `i fnTy fun i => do
        withLocalDeclD `j fnTy fun j => do
          withLocalDeclD `x α fun x => do
            let hType ← mkAppM ``Function.LeftInverse #[i, j]
            withLocalDeclD `h hType fun h => do
              let proof := mkApp h x
              let outer ← mkFreshExprMVar α
              let before ← instantiateMVars outer
              let lctx ← getLCtx
              let ctx : EvCtx := { lctx := lctx, insts := (← getLocalInstances) }
              let reason ← checkRwStep (.fvar h.fvarId!) #[] false none
                outer x ctx #[] "" (some proof) (localEvidence := true)
              unless reason.isNone do
                throwError "the caller-metavariable replay check was rejected: {reason}"
              let after ← instantiateMVars outer
              unless after == before do
                throwError "recorder rewrite matching leaked an assignment into caller state"

end ExplicitLean.SimpTrace.T77LocalRewriteParity
