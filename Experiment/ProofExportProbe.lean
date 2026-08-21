import Lean.Elab.Command
import ExplicitLean.ProofExport

open Lean Elab Command Meta
open ExplicitLean

namespace ProofExportProbe

namespace Shadowed

/- This declaration intentionally shadows the root `Nat` name while the
   renderer is asked to print a proof whose type is root `Nat`. -/
def Nat := Bool

end Shadowed

private def parseTerm (env : Environment) (text : String) : CommandElabM Syntax := do
  match Parser.runParserCategory env `term text with
  | .ok parsed => pure parsed
  | .error message => throwError "proof-export probe could not parse generated source: {message}"

private def checkRenderer : CommandElabM Unit := do
  let (proof, proofType) ← liftTermElabM do
    let nat := mkConst ``Nat
    let proof ← withLetDecl `shared nat (mkNatLit 0) (nondep := false) fun shared => do
      let body ← mkEqRefl shared
      mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) #[shared] body
    pure (proof, ← inferType proof)
  let suppliedType := proofType
  let rendered ← liftTermElabM do
    ProofExport.render proof (type? := some suppliedType) (config := {
      sourceNamespace := `ProofExportProbe.Shadowed
    })
  let typeStx ← parseTerm (← getEnv) rendered.typeText
  let valueStx ← parseTerm (← getEnv) rendered.valueText
  liftTermElabM do
    withTheReader Core.Context (fun context =>
      { context with currNamespace := `ProofExportProbe.Shadowed }) do
      let type ← Term.elabType typeStx
      let value ← Term.elabTerm valueStx (some type)
      Term.synthesizeSyntheticMVarsNoPostponing
      unless ← isDefEq type (← inferType value) do
        throwError "proof-export probe generated a term with the wrong type"
  let rejectedWrongType ← liftTermElabM do
    try
      let _ ← ProofExport.render proof (type? := some (mkConst ``Bool)) (config := {
        sourceNamespace := `ProofExportProbe.Shadowed
      })
      pure false
    catch _ =>
      pure true
  unless rejectedWrongType do
    throwError "proof-export probe accepted a supplied type that is not definitionally equal"
  unless rendered.valueText.contains "let" do
    throwError "proof-export probe did not preserve the shared let regression"
  unless rendered.metrics.sharedBytes == rendered.valueText.utf8ByteSize do
    throwError "proof-export probe reported an incorrect shared byte count"
  logInfo m!"proof-export probe passed ({rendered.typeText.utf8ByteSize} type bytes, {rendered.valueText.utf8ByteSize} value bytes)"

run_cmd checkRenderer

end ProofExportProbe
