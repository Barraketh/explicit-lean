module
prelude

public import Init.Prelude
public meta import ExplicitLean.SimpEngine.Boundary.SequenceCodec
meta import all ExplicitLean.SimpEngine.Boundary.SequenceCodec
public meta import Lean.Elab.Tactic.Basic
meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all ExplicitLean.SimpEngine.Boundary.MatcherCodec

public meta section
open Lean Meta Elab
namespace ExplicitLean.SimpEngine.Boundary

/-- Source syntax is data: parsing below never elaborates or evaluates it. -/
partial def boundaryReservationSyntaxJson : Syntax → Json
  | .missing => .arr #[.str "missing"]
  | .atom _ value => .arr #[.str "atom", .str value]
  | .ident _ raw name _ => .arr #[.str "ident", .str raw.toString, encodeBoundaryName name]
  | .node _ kind args => .arr #[.str "node", encodeBoundaryName kind,
      .arr (args.map boundaryReservationSyntaxJson)]

private partial def sourceTokens : Syntax → Array String
  | .atom _ value => #[value]
  | .ident _ raw _ _ => #[raw.toString]
  | .node _ _ args => args.foldl (fun acc arg => acc ++ sourceTokens arg) #[]
  | .missing => #[]

private partial def sourceCounts (stx : Syntax) : Nat × Nat × Bool := Id.run do
  let mut byCount := if stx.getKind == `Lean.Parser.Term.byTactic then 1 else 0
  let mut aesopCount := if stx.getKind == `Aesop.Frontend.Parser.aesopTactic then 1 else 0
  let mut valid := !stx.isQuot && (stx.getKind != `Lean.Parser.Term.byTactic || sourceTokens stx == #["by", "aesop"]) &&
    stx.getKind != `Aesop.Frontend.Parser.aesopTactic? &&
    (stx.getKind != `Aesop.Frontend.Parser.aesopTactic ||
      (stx.getArgs.size == 2 && stx[0].isAtom && stx[0].getAtomVal == "aesop" &&
        stx[1].getKind == nullKind && stx[1].getArgs.isEmpty))
  for arg in stx.getArgs do
    let (b, a, ok) := sourceCounts arg
    byCount := byCount + b
    aesopCount := aesopCount + a
    valid := valid && ok
  return (byCount, aesopCount, valid)

/-- Exactly one plain nested `by aesop` in an original simp call. -/
def boundaryReservationSource (env : Environment) (source : String) : MetaM Json := do
  let parsed ← ofExcept <| Parser.runParserCategory env `tactic source
  unless parsed.getKind == `Lean.Parser.Tactic.simp do
    throwError "boundary_reservation_source_not_simp"
  unless sourceCounts parsed == (1, 1, true) do
    throwError "boundary_reservation_source_not_single_plain_aesop"
  return boundaryReservationSyntaxJson parsed

private def generatorJson (g : DeclNameGenerator) : Json :=
  .arr #[encodeBoundaryName g.namePrefix, toJson g.idx, toJson g.parentIdxs]

/-- Full checked auxiliary proofs, caller caches and both declaration branches
    are authenticated, never installed or cleared. -/
def boundaryReservationState (env : Environment) : MetaM Json := do
  let (auxiliary, auxState) ← (localAuxCacheViewJson env).run { checked := ← IO.wait env.checked }
  let checked := env.constants.foldStage2 (fun names name _ => names.push name) #[]
  return .arr #[nameArrayJson (checked.qsort Name.quickLt),
    nameArrayJson (branchNames env), nameArrayJson (branchNames env true),
    boundaryMatchStateJson (Match.matchEqnsExt.getState env),
    equationStateJson (eqnsExt.getState env), boundarySparseCacheJson env,
    auxiliary, .arr (auxState.auxProofs.map (·.2))]

/-- Reserve one child namespace, optionally preceded by one authenticated
    absent-key registration of an already active imported equation theorem. -/
def encodeBoundaryDeclarationBranch (before after : Environment)
    (pre post : DeclNameGenerator) (source : String) : MetaM String := do
  let (child, parent) := pre.mkChild
  unless !pre.namePrefix.isAnonymous && generatorJson parent == generatorJson post do
    throwError "boundary_reservation_not_one_child"
  let initial ← boundaryReservationState before
  let final ← boundaryReservationState after
  let beforeMap := (eqnsExt.getState before).mapInv
  let afterMap := (eqnsExt.getState after).mapInv
  unless beforeMap.toArray.all (fun (name, owner) => afterMap.find? name == some owner) do
    throwError "boundary_reservation_changed_equation_mapping"
  let added := afterMap.toArray.filter fun (name, _) => (beforeMap.find? name).isNone
  unless added.size <= 1 do throwError "boundary_reservation_multiple_registrations"
  let registration ← if let some (name, owner) := added[0]? then do
      let signature ← activeRegistrationSignature before owner name
      unless (← activeRegistrationSignature after owner name) == signature do
        throwError "boundary_reservation_registration_changed"
      pure <| Json.arr #[encodeBoundaryName name, .str signature.compress]
    else pure Json.null
  let projected ← withEnv before do
    if let .arr #[name, .str signature] := registration then
      executeActiveRegistration (← ofExcept <| decodeBoundaryName name) signature
    getEnv
  unless (← boundaryReservationState projected) == final do
    throwError "boundary_reservation_environment_changed"
  let sourceAst ← boundaryReservationSource before source
  return (Json.arr #[.str "boundary_declaration_branch_v1", encodeBoundaryName pre.namePrefix,
    generatorJson pre, generatorJson child, generatorJson parent, .str source, sourceAst,
    initial, final, registration]).compress

def executeBoundaryDeclarationBranch (anchor : Name) (source : String) : MetaM Unit := do
  let .arr values ← ofExcept (Json.parse source)
    | throwError "boundary_reservation_payload_shape"
  unless values.size == 10 && values[0]! == .str "boundary_declaration_branch_v1" do
    throwError "boundary_reservation_payload_shape"
  let pre ← getDeclNGen
  unless !anchor.isAnonymous && anchor == pre.namePrefix &&
      values[1]! == encodeBoundaryName anchor && values[2]! == generatorJson pre do
    throwError "boundary_reservation_pre_generator"
  let (child, parent) := pre.mkChild
  unless values[3]! == generatorJson child && values[4]! == generatorJson parent do
    throwError "boundary_reservation_derived_generator"
  let original ← ofExcept values[5]!.getStr?
  unless (← boundaryReservationSource (← getEnv) original) == values[6]! do
    throwError "boundary_reservation_source_ast"
  unless (← boundaryReservationState (← getEnv)) == values[7]! do
    throwError "boundary_reservation_pre_state"
  -- Derive a candidate environment using the shared authenticated operation.
  -- No recorded environment state is installed; all other state must match.
  let projected ← withEnv (← getEnv) do
    match values[9]! with
    | .null => pure ()
    | .arr #[name, .str signature] =>
      executeActiveRegistration (← ofExcept <| decodeBoundaryName name) signature
    | _ => throwError "boundary_reservation_registration_shape"
    getEnv
  unless (← boundaryReservationState projected) == values[8]! do
    throwError "boundary_reservation_final_state"
  setEnv projected
  -- The only name allocation is Lean's computed parent from the actual pre-state.
  -- Recorded post-state numbers are checked above, never assigned.
  setDeclNGen parent

end ExplicitLean.SimpEngine.Boundary
