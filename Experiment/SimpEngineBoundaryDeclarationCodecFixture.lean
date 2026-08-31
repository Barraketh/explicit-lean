import ExplicitLean.SimpEngine.Boundary.DeclarationCodec
import Lean.Meta.CongrTheorems

open Lean Meta ExplicitLean.SimpEngine.Boundary

private def payload (name : Name) (all : List Name) (type value : Expr) : MetaM String := do
  let typeSource ← encodeBoundaryExpr type
  let valueSource ← encodeBoundaryExpr value
  let allJson : Json := .arr (all.toArray.map encodeBoundaryName)
  return (Json.arr #[.str "boundary_theorem_dag_v1", encodeBoundaryName name,
    allJson,
    .arr #[], .str typeSource, .str valueSource]).compress

private def expectFailure (action : MetaM Unit) : MetaM Unit := do
  let failed ← try
    let _ ← action
    pure false
  catch _ => pure true
  unless failed do throwError "expected declaration codec failure"

run_meta do
  let generated := `DeclarationCodecProbe.generated
  let trueType := mkConst ``True
  let trueValue := mkConst ``True.intro
  let source ← payload generated [generated] trueType trueValue

  logInfo "first declaration"
  executeBoundaryTheorem generated source

  let emptyAllName := `DeclarationCodecProbe.empty_all
  let emptyAllSource ← payload emptyAllName [] trueType trueValue
  logInfo "empty-all declaration"
  executeBoundaryTheorem emptyAllName emptyAllSource
  logInfo "empty-all matching declaration"
  executeBoundaryTheorem emptyAllName emptyAllSource

  let nat := mkConst ``Nat
  let equality := mkApp3 (mkConst ``Eq [.succ .zero]) nat (mkBVar 1) (mkBVar 1)
  let nestedType := mkForall `y .default nat equality
  let forallType := mkForall `x .default nat nestedType
  let reflProof := mkApp2 (mkConst ``Eq.refl [.succ .zero]) nat (mkBVar 1)
  let nestedValue := mkLambda `y .default nat reflProof
  let lambdaValue := mkLambda `x .default nat nestedValue
  let _ ← encodeBoundaryTheorem {
    name := `DeclarationCodecProbe.bound
    levelParams := []
    type := forallType
    value := lambdaValue
    all := [`DeclarationCodecProbe.bound]
  }
  unless (← getEnv).containsOnBranch generated do
    throwError "declaration codec did not add theorem"
  executeBoundaryTheorem generated source

  expectFailure (executeBoundaryTheorem `DeclarationCodecProbe.foreign source)
  expectFailure (executeBoundaryTheorem ``True source)

  let falseSource ← payload generated [generated] (mkConst ``False) trueValue
  expectFailure (executeBoundaryTheorem generated falseSource)

  let unknown := Name.str `DeclarationCodecProbe "reserved_missing"
  let unknownSource ← payload generated [generated] (mkConst unknown) trueValue
  expectFailure (executeBoundaryTheorem generated unknownSource)

  let malformed := (Json.arr #[.str "boundary_theorem_dag_v1", .arr #[.str "bad"],
    .arr #[encodeBoundaryName generated],
    .arr #[], .str "[]", .str "[]"]).compress
  expectFailure (executeBoundaryTheorem generated malformed)

  let reserved := `Nat.add.congr_simp
  unless isReservedName (← getEnv) reserved do
    throwError "negative control is not a reserved name"
  unless !(← getEnv).containsOnBranch reserved do
    throwError "negative control was already realized"
  let reservedSource ← payload generated [generated] (mkConst reserved) trueValue
  expectFailure (executeBoundaryTheorem generated reservedSource)
  unless !(← getEnv).containsOnBranch reserved do
    throwError "decoding invoked a reserved-name generator"

  let conflicting := ``True
  let conflictSource ← payload conflicting [] trueType trueValue
  expectFailure (executeBoundaryTheorem conflicting conflictSource)
