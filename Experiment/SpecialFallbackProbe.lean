import ExplicitLean.SimpExplicit

open Lean Meta Elab Tactic
open ExplicitLean

namespace SpecialFallbackProbe

/- This is deliberately a lower-level producer test.  `Origin.other` is not
   claimed to be source-reachable through `simp_explicit?` yet; the public
   encoder is exercised directly with a kernel-checked, definitionally equal
   simp result and its closed replay validation. -/
private def checkEncoding : TacticM Unit := do
  let input := mkApp2 (mkConst ``Nat.add) (mkNatLit 0) (mkNatLit 1)
  let result : Simp.Result := { expr := mkNatLit 1 }
  let encoded ← ExplicitLean.SimpExplicit.encodeProofResult input result
    #[.other `syntheticSpecial] .post
  unless encoded.encodingKind == "generated_proof" do
    throwError "special fallback did not use generated proof encoding"
  unless encoded.encodingReason == some "special_rule" do
    throwError "special fallback did not report special_rule"
  unless encoded.metrics.generatedSpecialEvents == 1 do
    throwError "special fallback did not count one special event"
  unless encoded.source.contains "have" && !encoded.source.isEmpty do
    throwError "special fallback emitted an empty binding source"

example : True := by
  run_tac do
    checkEncoding
  trivial

end SpecialFallbackProbe
