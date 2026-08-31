import ExplicitLean.SimpEngine.CommandAudit

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [moduleName, file] := args
    | IO.eprintln "usage: simpEngineCommandAudit <module> <source.lean>" *> pure 2
  try
    initSearchPath (← findSysroot)
    let nonce ← ExplicitLean.SimpEngine.CommandAudit.runNonce
    let source ← IO.FS.readFile file
    -- Same package options as the existing inventory/declaration oracle.
    -- capture itself passes these to runFrontend without modifying them.
    let options := Elab.async.set (Elab.autoImplicit.set {} false) true
      |>.set `maxSynthPendingDepth (3 : Nat)
      |>.set `weak.linter.unusedVariables false
      |>.set `weak.linter.unusedSimpArgs false
      |>.set `weak.linter.unreachableTactic false
      |>.set `maxHeartbeats (0 : Nat)
    let captured ← ExplicitLean.SimpEngine.CommandAudit.capture source options file moduleName.toName
    ExplicitLean.SimpEngine.CommandAudit.emit captured "standalone" nonce
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
