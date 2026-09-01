import ExplicitLean.SimpEngine.CommandAudit
import ExplicitLean.SimpEngine.FrontendOptions

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let some (moduleName, file, output?) := (match args with
    | [moduleName, file] => some (moduleName, file, none)
    | [moduleName, file, "--olean", output] =>
      some (moduleName, file, some (System.FilePath.mk output))
    | _ => none)
    | IO.eprintln "usage: simpEngineCommandAudit <module> <source.lean> [--olean quarantine.olean]" *> pure 2
  try
    initSearchPath (← findSysroot)
    let nonce ← ExplicitLean.SimpEngine.CommandAudit.runNonce
    let source ← IO.FS.readFile file
    -- `capture` passes the shared package-plus-verification options to
    -- `runFrontend` without modifying them.
    let options := ExplicitLean.SimpEngine.verificationFrontendOptions
    let captured ← ExplicitLean.SimpEngine.CommandAudit.capture source options file moduleName.toName
      (oleanFileName? := output?)
    ExplicitLean.SimpEngine.CommandAudit.emit captured "standalone" nonce
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
