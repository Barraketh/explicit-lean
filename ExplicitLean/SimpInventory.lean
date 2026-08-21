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
  bodyScopeStartByte : Option Nat
  bodyScopeEndByte : Option Nat
  bodyScopeSource : Option String
  ownerKind : Option String
  ownerRole : Option String
  ownerStartByte : Option Nat
  ownerEndByte : Option Nat
  ownerSource : Option String
  ownerChildStartByte : Option Nat
  ownerChildEndByte : Option Nat
  ownerChildSource : Option String
  ownerLeftStartByte : Option Nat
  ownerLeftEndByte : Option Nat
  ownerLeftSource : Option String
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

private def bodyScope? (stx : Syntax) (current : Option Syntax) : Option Syntax :=
  if current.isSome then
    current
  else if stx.isOfKind ``Lean.Parser.Term.byTactic then
    some stx
  else
    none

private def bodyScopeRange (fileMap : FileMap) (body? : Option Syntax) :
    Option (Nat × Nat × String) := do
  let body ← body?
  let sequence := if body.getNumArgs > 1 then body[1] else body
  let range ← sequence.getRange?
  pure (
    range.start.byteIdx,
    range.stop.byteIdx,
    String.Pos.Raw.extract fileMap.source range.start range.stop)

private structure OwnerFrame where
  owner : Syntax
  kind : String
  role : String
  child : Syntax
  left? : Option Syntax := none

private structure OwnerInfo where
  kind : String
  role : String
  startByte : Nat
  endByte : Nat
  source : String
  childStartByte : Nat
  childEndByte : Nat
  childSource : String
  leftStartByte : Option Nat
  leftEndByte : Option Nat
  leftSource : Option String

private def ownerKind? (stx : Syntax) : Option String :=
  if stx.isOfKind ``Lean.Parser.Tactic.«tactic_<;>_» then
    some "and_then"
  else if stx.isOfKind ``Lean.Parser.Tactic.allGoals then
    some "all_goals"
  else if stx.isOfKind ``Lean.Parser.Tactic.tacticRepeat_ then
    some "repeat"
  else if stx.isOfKind ``Lean.Parser.Tactic.repeat' then
    some "repeat_prime"
  else if stx.isOfKind ``Lean.Parser.Tactic.first then
    some "first"
  else
    none

private def ownerFramesForChild (stx : Syntax) (index : Nat) : Array OwnerFrame :=
  match ownerKind? stx with
  | none => #[]
  | some "and_then" =>
      if stx.getNumArgs >= 3 && index == 0 then
        #[{ owner := stx, kind := "and_then", role := "and_then_left", child := stx[0],
            left? := some stx[0] }]
      else if stx.getNumArgs >= 3 && index == 2 then
        #[{ owner := stx, kind := "and_then", role := "and_then_right", child := stx[2],
            left? := some stx[0] }]
      else
        #[]
  | some "all_goals" =>
      if stx.getNumArgs >= 2 && index == 1 then
        #[{ owner := stx, kind := "all_goals", role := "all_goals_child", child := stx[1] }]
      else
        #[]
  | some "repeat" =>
      if stx.getNumArgs >= 2 && index == 1 then
        #[{ owner := stx, kind := "repeat", role := "repeat_child", child := stx[1] }]
      else
        #[]
  | some "repeat_prime" =>
      if stx.getNumArgs >= 2 && index == 1 then
        #[{ owner := stx, kind := "repeat_prime", role := "repeat_child", child := stx[1] }]
      else
        #[]
  | some "first" =>
      if stx.getNumArgs >= 2 && index == 1 then
        #[{ owner := stx, kind := "first", role := "first_branch", child := stx[1] }]
      else
        #[]
  | some _ => #[]

private def selectedOwner? (owners : Array OwnerFrame) : Option OwnerFrame := do
  -- An andThen owner distributes its right tactic over all produced goals;
  -- prefer it over a nested repeat/all_goals owner.  Within a chain, the
  -- innermost andThen owns the occurrence.  For other combinators the
  -- innermost recognized owner is the exact source parent.
  let andThenOwners := owners.filter (·.kind == "and_then")
  if let some owner := andThenOwners.back? then
    if owner.role == "and_then_right" then
      return owner
  owners.back?

private def specializeFirstBranch (owners : Array OwnerFrame) (child : Syntax) :
    Array OwnerFrame :=
  owners.map fun owner =>
    if owner.kind == "first" && owner.child.getKind.toString == "null" then
      { owner with child := child }
    else
      owner

private def ownerInfo (fileMap : FileMap) (owners : Array OwnerFrame) :
    Option OwnerInfo := do
  let frame ← selectedOwner? owners
  let ownerRange ← frame.owner.getRange?
  let childRange ← frame.child.getRange?
  let ownerSource := String.Pos.Raw.extract fileMap.source ownerRange.start ownerRange.stop
  let childSource := String.Pos.Raw.extract fileMap.source childRange.start childRange.stop
  let (leftStartByte, leftEndByte, leftSource) ← match frame.left? with
    | none => pure (none, none, none)
    | some left =>
        let range ← left.getRange?
        pure (some range.start.byteIdx, some range.stop.byteIdx,
          some (String.Pos.Raw.extract fileMap.source range.start range.stop))
  pure {
    kind := frame.kind
    role := frame.role
    startByte := ownerRange.start.byteIdx
    endByte := ownerRange.stop.byteIdx
    source := ownerSource
    childStartByte := childRange.start.byteIdx
    childEndByte := childRange.stop.byteIdx
    childSource
    leftStartByte
    leftEndByte
    leftSource
  }

private partial def collectAux (file : String) (fileMap : FileMap) (stx : Syntax)
    (body? : Option Syntax := none)
    (owners : Array OwnerFrame := #[])
    (entries : Array Entry := #[]) : Array Entry := Id.run do
  let mut entries := entries
  let body? := bodyScope? stx body?
  if let some range := stx.getRange? then
    let source := String.Pos.Raw.extract fileMap.source range.start range.stop
    if let some kind := tacticKind? stx source then
      let position := fileMap.toPosition range.start
      let (bodyScopeStartByte, bodyScopeEndByte, bodyScopeSource) :=
        match bodyScopeRange fileMap body? with
        | some (start, stop, source) => (some start, some stop, some source)
        | none => (none, none, none)
      let owner := ownerInfo fileMap owners
      entries := entries.push {
        file
        kind
        startByte := range.start.byteIdx
        endByte := range.stop.byteIdx
        line := position.line
        column := position.column
        syntaxKind := stx.getKind.toString
        source
        bodyScopeStartByte
        bodyScopeEndByte
        bodyScopeSource
        ownerKind := owner.map (·.kind)
        ownerRole := owner.map (·.role)
        ownerStartByte := owner.map (·.startByte)
        ownerEndByte := owner.map (·.endByte)
        ownerSource := owner.map (·.source)
        ownerChildStartByte := owner.map (·.childStartByte)
        ownerChildEndByte := owner.map (·.childEndByte)
        ownerChildSource := owner.map (·.childSource)
        ownerLeftStartByte := owner.bind (·.leftStartByte)
        ownerLeftEndByte := owner.bind (·.leftEndByte)
        ownerLeftSource := owner.bind (·.leftSource)
      }
  for (arg, index) in stx.getArgs.toList.zipIdx do
    let childOwners := specializeFirstBranch
      (owners ++ ownerFramesForChild stx index) arg
    entries := collectAux file fileMap arg body?
      (owners := childOwners) entries
  return entries

def collect (file : String) (fileMap : FileMap) (stx : Syntax) : Array Entry :=
  collectAux file fileMap stx

private def inventoryLinter : Linter where run := fun stx => do
  unless explicitLean.simpInventory.get (← getOptions) do
    return
  let file ← getFileName
  let fileMap ← getFileMap
  for entry in collect file fileMap stx do
    IO.println (toJson entry).compress

initialize addLinter inventoryLinter

end ExplicitLean.SimpInventory
