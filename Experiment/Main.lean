import Mathlib.SetTheory.Cardinal.NatCount
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Data.List.Range
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.Divisors
import ExplicitLean.ProofExport

open Lean Elab Command Meta

open ExplicitLean

/-- Export one completed theorem proof body using the shared expression
renderer. The source namespace is supplied to the pretty-printer so root
declarations are qualified when the target namespace contains a shadowing
declaration. -/
private def exportTheorem (name : Name) (binderNames : Array Name)
    (sourceNamespace : Name := name.getPrefix) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? name
    | throwError "unknown declaration '{name}'"
  let some value := info.value? (allowOpaque := true)
    | throwError "declaration '{name}' has no accessible value"
  let rendered ← liftTermElabM do
    withTheReader Core.Context (fun context => { context with currNamespace := sourceNamespace }) do
      ProofExport.render value (config := {
        sourceNamespace
        binderNames
      })
  let dir : System.FilePath := ".lake" / "proof-term-probe"
  IO.FS.createDirAll dir
  let stem := name.toString.replace "." "_"
  IO.FS.writeFile (dir / s!"{stem}.shared-body.lean") (rendered.valueText ++ "\n")
  let unsharedBytes := match rendered.metrics.unsharedBytes with
    | some bytes => toString bytes
    | none => "omitted"
  let statsText :=
    s!"private constants inlined: {rendered.metrics.privateConstantsInlined}\n" ++
    s!"shared bindings: {rendered.metrics.bindingCount}\n" ++
    s!"proof haves: {rendered.metrics.haveCount}\n" ++
    s!"value lets: {rendered.metrics.bindingCount - rendered.metrics.haveCount}\n" ++
    s!"pruned candidates: {rendered.metrics.prunedCount}\n" ++
    s!"unshared body bytes: {unsharedBytes}\n" ++
    s!"unshared body nodes: {rendered.metrics.unsharedNodes}\n" ++
    s!"shared body bytes: {rendered.valueText.utf8ByteSize}\n"
  IO.FS.writeFile (dir / s!"{stem}.stats") statsText

run_cmd exportTheorem `Nat.count_le_setENCard #[`p, `decidablePredP, `n]
run_cmd exportTheorem `Nat.count_le_cardinal #[`p, `decidablePredP, `n]
run_cmd exportTheorem `Nat.count_le_setNCard #[`p, `decidablePredP, `n, `h]
run_cmd exportTheorem `DualNumber.commute_eps_left #[`R, `semiringR, `x]
run_cmd exportTheorem `DualNumber.commute_eps_right #[`R, `semiringR, `x]
run_cmd exportTheorem `DualNumber.ringHom_ext #[`R, `commSemiringR, `R', `commSemiringR', `f, `g, `h₀, `hε]
run_cmd exportTheorem `DualNumber.range_lift #[`R, `B, `A, `commSemiringR, `semiringA, `semiringB, `algebraRA, `algebraRB, `fe]
run_cmd exportTheorem `GenContFract.first_num_eq #[`K, `g, `divisionRingK, `gp, `zeroth_s_eq]
run_cmd exportTheorem `GenContFract.terminatedAt_iff_s_terminatedAt #[`α, `g, `n]
run_cmd exportTheorem `GenContFract.partNum_none_iff_s_none #[`α, `g, `n]
run_cmd exportTheorem `List.isChain_range #[`r, `n]
run_cmd exportTheorem `List.ranges_disjoint #[`l]
run_cmd exportTheorem `TopologicalSpace.ext_iff #[`X, `t, `t'] Name.anonymous
run_cmd exportTheorem `IsOpen.union #[`X, `s₁, `s₂, `topologicalSpaceX, `h₁, `h₂] Name.anonymous
run_cmd exportTheorem `isOpen_iff_of_cover #[`X, `α, `s, `topologicalSpaceX, `f, `ho, `hU] Name.anonymous
run_cmd exportTheorem `Set.Finite.isOpen_sInter #[`X, `topologicalSpaceX, `s, `hs, `h] Name.anonymous
run_cmd exportTheorem `Nat.divisor_le #[`n, `m]
run_cmd exportTheorem `Nat.card_divisors_le_self #[`n]
run_cmd exportTheorem `Nat.divisors_subset_of_dvd #[`n, `m, `hzero, `h]

def main : IO Unit := pure ()
