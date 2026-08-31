module
prelude

public meta import Lean.Meta.Basic

public meta section
open Lean Meta
namespace ExplicitLean.SimpEngine.Boundary

/-- Pinned synthPendingImp checks this depth before invoking synthInstance?.
    Increasing MCtx depth alone does not prevent its unchecked synthesis path.
    Install this inside each fresh MetaM runner, using that runner's options.
    The scoped reader changes no options and is automatically restored. -/
def withoutBoundaryPendingSynthesis [Monad m] [MonadControlT MetaM m]
    (action : m α) : m α := mapMetaM (fun action => do
  let bound := maxSynthPendingDepth.get (← getOptions)
  withReader (fun ctx => {ctx with synthPendingDepth := max ctx.synthPendingDepth (bound + 1)}) action) action

/-- realizeConst starts its producer with a fresh Meta reader and the owner's
    options. Reinstall the capability restriction *inside* that callback,
    including every nested captured producer. No codec semantics change. -/
def realizeBoundaryConst (owner name : Name) (action : MetaM Unit) : MetaM Unit :=
  Meta.realizeConst owner name (withoutBoundaryPendingSynthesis action)

end ExplicitLean.SimpEngine.Boundary
