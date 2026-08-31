/- Emit exact Lean header imports for the translation index.

This is deliberately a header-only tool. It never imports the modules named by
the source files and it exits nonzero when Lean reports a header parse error.
The Python indexer turns each path<TAB>import... line into its
module@sourceHash dependency-map format. -/

import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Parser.Module

open Lean Parser

private def uniqueNames (imports : Array Lean.Import) : Array String :=
  imports.foldl (init := #[]) fun names imported =>
    let name := imported.module.toString
    if names.contains name then names else names.push name

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: LeanImportIndex.lean <Lean source file>..."
    return 2
  let mut failures := 0
  for path in args do
    try
      let source ← IO.FS.readFile path
      let input := Parser.mkInputContext source path
      let (header, _parserState, messages) ← Parser.parseHeader input
      if messages.hasErrors then
        IO.eprintln s!"header parse failed: {path}"
        failures := failures + 1
      else
        let names := uniqueNames (Lean.Elab.HeaderSyntax.imports header false)
        IO.println s!"{path}\t{String.intercalate "," names.toList}"
    catch error =>
      IO.eprintln s!"header parse failed: {path}: {error}"
      failures := failures + 1
  return if failures == 0 then 0 else 1
