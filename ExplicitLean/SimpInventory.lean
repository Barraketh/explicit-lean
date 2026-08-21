module

public import Lean.Data.Json
public meta import Lean.Elab.Command
public import Lean.Elab.Tactic.Simp
public import Lean.Elab.Tactic.Simpa
public import Lean.Linter.Basic

public meta section

open Lean Elab Command

namespace ExplicitLean.SimpInventory

register_option explicitLean.simpInventory : Bool := {
  defValue := false
  descr := "emit syntax-aware JSON records for simp-family tactics"
}

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

def tacticKind? (stx : Syntax) (source : String) : Option String :=
  if stx.isOfKind ``Lean.Parser.Tactic.simp then
    some (if stx[3].isNone then "simp" else "simp_only")
  else if stx.isOfKind ``Lean.Parser.Tactic.simpa ||
      stx.isOfKind ``Lean.Parser.Tactic.simpaUsingBang then
    some "simpa"
  else if stx.isOfKind ``Lean.Parser.Tactic.simpAll then
    some "simp_all"
  else if source.startsWith "simp_rw" && stx.getKind.toString.contains "tacticSimp_rw" then
    some "simp_rw"
  else
    none

partial def collect (file : String) (fileMap : FileMap) (stx : Syntax)
    (entries : Array Entry := #[]) : Array Entry := Id.run do
  let mut entries := entries
  if let some range := stx.getRange? then
    let source := String.Pos.Raw.extract fileMap.source range.start range.stop
    if let some kind := tacticKind? stx source then
      let position := fileMap.toPosition range.start
      entries := entries.push {
        file
        kind
        startByte := range.start.byteIdx
        endByte := range.stop.byteIdx
        line := position.line
        column := position.column
        syntaxKind := stx.getKind.toString
        source
      }
  for arg in stx.getArgs do
    entries := collect file fileMap arg entries
  return entries

private def inventoryLinter : Linter where run := fun stx => do
  unless explicitLean.simpInventory.get (← getOptions) do
    return
  let file ← getFileName
  let fileMap ← getFileMap
  for entry in collect file fileMap stx do
    IO.println (toJson entry).compress

initialize addLinter inventoryLinter

end ExplicitLean.SimpInventory
