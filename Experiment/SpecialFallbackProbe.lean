import ExplicitLean.SimpExplicit

open Lean Meta Elab Tactic
open ExplicitLean

namespace SpecialFallbackProbe

/- This is deliberately a lower-level producer test. `Origin.other` is not
   source-reachable through `simp_explicit?`, so the public encoder must reject
   it instead of manufacturing a generated proof or special fallback. -/
private def checkEncoding : TacticM Unit := do
  let input := mkApp2 (mkConst ``Nat.add) (mkNatLit 0) (mkNatLit 1)
  let result : Simp.Result := { expr := mkNatLit 1 }
  let rejected ← try
    let _ ← ExplicitLean.SimpExplicit.encodeProofResult input result
      #[.other `syntheticSpecial] .post
    pure false
  catch _ =>
    pure true
  unless rejected do
    throwError "synthetic Origin.other unexpectedly received a generated fallback"

example : True := by
  run_tac do
    checkEncoding
  trivial

end SpecialFallbackProbe
