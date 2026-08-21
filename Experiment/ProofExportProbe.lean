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
  unless rendered.metrics.unsharedBytes.isSome do
    throwError "small proof-export fixture omitted its exact unshared byte metric"
  unless rendered.metrics.sharedBytes == rendered.valueText.utf8ByteSize do
    throwError "proof-export probe reported an incorrect shared byte count"
  logInfo m!"proof-export probe passed ({rendered.typeText.utf8ByteSize} type bytes, {rendered.valueText.utf8ByteSize} value bytes)"

run_cmd checkRenderer

private def checkLargeDag : CommandElabM Unit := do
  let (value, valueType) ← liftTermElabM do
    let mut term := mkNatLit 0
    for _ in Array.range 18 do
      let add := mkConst ``Nat.add
      term := mkApp (mkApp add term) term
    pure (term, mkConst ``Nat)
  let rendered ← liftTermElabM do
    ProofExport.render value (type? := some valueType)
  unless rendered.metrics.unsharedNodes > 100000 do
    throwError "large proof-export DAG did not exceed the bounded metric threshold"
  unless rendered.metrics.unsharedBytes.isNone do
    throwError "large proof-export DAG unexpectedly measured unshared source bytes"
  unless rendered.valueText.contains "let" do
    throwError "large proof-export DAG did not retain semantic sharing"
  unless rendered.valueText.utf8ByteSize < 10000 do
    throwError "large proof-export DAG shared source is not compact"
  let valueStx ← parseTerm (← getEnv) rendered.valueText
  liftTermElabM do
    withTheReader Core.Context (fun context => context) do
      let elaborated ← Term.elabTerm valueStx (some valueType)
      Term.synthesizeSyntheticMVarsNoPostponing
      unless ← isDefEq valueType (← inferType elaborated) do
        throwError "large proof-export DAG did not materialize at its declared type"
      unless ← isDefEq value elaborated do
        throwError "large proof-export DAG materialization changed the rendered value"
  logInfo m!"large proof-export DAG passed ({rendered.metrics.unsharedNodes} expanded nodes, {rendered.valueText.utf8ByteSize} shared bytes)"

run_cmd checkLargeDag

end ProofExportProbe
