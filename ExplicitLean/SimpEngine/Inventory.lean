module

public import Lean.Data.Json
public import Lean.Elab.Tactic.Simp

public meta section

open Lean

namespace ExplicitLean.SimpEngine.Inventory

/-- The source identity needed to instrument one supported simplifier call. -/
structure Entry where
  file : String
  kind : String
  startByte : Nat
  endByte : Nat
  line : Nat
  column : Nat
  syntaxKind : String
  source : String
  deriving ToJson

private def tacticKind? (stx : Syntax) : Option String :=
  if stx.isOfKind ``Lean.Parser.Tactic.simp then
    some (if stx[3].isNone then "simp" else "simp_only")
  else
    none

private partial def collectAux (file : String) (fileMap : FileMap) (stx : Syntax)
    (entries : Array Entry := #[]) : Array Entry := Id.run do
  let mut entries := entries
  if let some range := stx.getRange? then
    if let some kind := tacticKind? stx then
      let position := fileMap.toPosition range.start
      entries := entries.push {
        file
        kind
        startByte := range.start.byteIdx
        endByte := range.stop.byteIdx
        line := position.line
        column := position.column
        syntaxKind := stx.getKind.toString
        source := String.Pos.Raw.extract fileMap.source range.start range.stop
      }
  for arg in stx.getArgs do
    entries := collectAux file fileMap arg entries
  return entries

/-- Find `simp` and `simp only` syntax without matching comments or strings. -/
def collect (file : String) (fileMap : FileMap) (stx : Syntax) : Array Entry :=
  collectAux file fileMap stx

end ExplicitLean.SimpEngine.Inventory
