module
prelude

public meta import Lean.Data.Json
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.ElabTerm

public meta section

open Lean Meta Elab Tactic

namespace Lean.Parser.Tactic

/-!
The scope probe intentionally duplicates only the stock `simp` argument
grammar.  It is kept independent of the boundary recorder/replay engine so
that source instrumentation observes ordinary stock `simp` execution.
-/
syntax scopeProbeSimpArgs := optConfig (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?

syntax (name := simpEngineBoundaryScopeProbe)
  "simp_engine_boundary_scope_probe " str scopeProbeSimpArgs : tactic

end Lean.Parser.Tactic

namespace Lean.Parser.Command

syntax (name := simpEngineBoundaryScopeReport)
  "simp_engine_boundary_scope_report" : command

end Lean.Parser.Command

namespace ExplicitLean.SimpEngine.BoundaryScopeProbe

private structure ScopeObservation where
  occurrenceId : String
  caller : Option Name
  deriving BEq

private initialize scopeObservationsRef : IO.Ref (Array ScopeObservation) ←
  IO.mkRef #[]

private def recordObservation (occurrence : String) : TacticM Unit := do
  let caller? ← Term.getDeclName?
  scopeObservationsRef.modify fun observations => observations.push {
    occurrenceId := occurrence
    caller := caller?
  }

elab_rules : tactic
  | `(tactic| simp_engine_boundary_scope_probe $occurrence:str
      $args:scopeProbeSimpArgs) => withMainContext do
      recordObservation occurrence.getString
      let inner := mkNode ``Lean.Parser.Tactic.simp #[
        mkAtom "simp", args.raw[0], args.raw[1], args.raw[2], args.raw[3], args.raw[4]]
      evalTactic inner

private structure ScopeReport where
  occurrenceId : String
  module : String
  caller : Option String
  executionCount : Nat
  isProofDeclaration : Option Bool
  evidenceStatus : String
  deriving ToJson

private def resolveObservation (module : String) (observation : ScopeObservation)
    (observations : Array ScopeObservation) : Lean.Elab.Command.CommandElabM ScopeReport := do
  let count := observations.countP (· == observation)
  let env ← getEnv
  let isProof? ← match observation.caller with
    | none => pure none
    | some caller => do
      let some declaration := env.find? caller
        | pure none
      try
        some <$> PPContext.runMetaM {
          env := env
          opts := ← getOptions
          currNamespace := Name.anonymous
          openDecls := []
        } (Meta.isProp declaration.type)
      catch _ =>
        pure none
  let evidenceStatus := if observation.caller.isNone then
      "missing_caller"
    else if isProof?.isNone then
      "missing_declaration_or_type"
    else
      "complete"
  return {
    occurrenceId := observation.occurrenceId
    module
    caller := observation.caller.map Name.toString
    executionCount := count
    isProofDeclaration := isProof?
    evidenceStatus
  }

private def reportObservations : Lean.Elab.Command.CommandElabM Unit := do
  let observations ← scopeObservationsRef.get
  -- This command is appended to exactly one temporary source module.  Clear
  -- the process-local log before resolving it so a second report cannot leak
  -- observations from the first one.
  scopeObservationsRef.set #[]
  let module := (← getEnv).mainModule.toString
  let mut keys : Array (String × Option Name) := #[]
  for observation in observations do
    let key := (observation.occurrenceId, observation.caller)
    unless keys.contains key do
      keys := keys.push key
  keys := keys.qsort fun left right =>
    left.1 < right.1 || (left.1 == right.1 &&
      (left.2.map Name.toString |>.getD "") <
        (right.2.map Name.toString |>.getD ""))
  for (occurrence, caller) in keys do
    let some observation := observations.find? fun item =>
      item.occurrenceId == occurrence && item.caller == caller
      | throwError "scope probe lost observation"
    let report ← resolveObservation module observation observations
    IO.println s!"SIMP_ENGINE_SCOPE_EXECUTION {(toJson report).compress}"

elab_rules : command
  | `(command| simp_engine_boundary_scope_report) => reportObservations

end ExplicitLean.SimpEngine.BoundaryScopeProbe
