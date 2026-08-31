module
prelude

public meta import Lean.Meta.Match.MatchEqsExt

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/-- Compare every matcher field, preserving all ordered arrays. Map keys are
    unique; an absent overlap entry differs from an explicitly empty entry. -/
def boundaryMatcherInfoEq (lhs rhs : MatcherInfo) : Bool :=
  lhs.numParams == rhs.numParams && lhs.numDiscrs == rhs.numDiscrs &&
  lhs.altInfos == rhs.altInfos && lhs.uElimPos? == rhs.uElimPos? &&
  lhs.discrInfos.map (·.hName?) == rhs.discrInfos.map (·.hName?) &&
  (lhs.overlaps.map.toArray.map (fun (key, values) => (key, values.toArray))).qsort
      (fun a b => a.1 < b.1) ==
    (rhs.overlaps.map.toArray.map (fun (key, values) => (key, values.toArray))).qsort
      (fun a b => a.1 < b.1)

def boundaryMatchEqnsEq (lhs rhs : Match.MatchEqns) : Bool :=
  lhs.eqnNames == rhs.eqnNames && lhs.splitterName == rhs.splitterName &&
    boundaryMatcherInfoEq lhs.splitterMatchInfo rhs.splitterMatchInfo

/-- `eqns` is independent state: registering a new value for an existing
    matcher overwrites its map value but accumulates equation names. -/
def boundaryMatchEqnsStateEq (lhs rhs : Match.MatchEqnsExtState) : Bool := Id.run do
  let lhsMap := lhs.map.toArray
  let rhsMap := rhs.map.toArray
  if lhsMap.size != rhsMap.size then return false
  for (name, lhsEqns) in lhsMap do
    let some rhsEqns := rhs.map.find? name | return false
    unless boundaryMatchEqnsEq lhsEqns rhsEqns do
      return false
  return lhs.eqns.toList.toArray.qsort Name.quickLt == rhs.eqns.toList.toArray.qsort Name.quickLt

end ExplicitLean.SimpEngine.Boundary
