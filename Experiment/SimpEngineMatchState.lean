import Lean
import ExplicitLean.SimpEngine.Boundary.MatchState

open Lean Meta ExplicitLean.SimpEngine.Boundary

run_cmd do
  let overlaps : Match.Overlaps :=
    { map := ({} : Std.HashMap Nat (Std.TreeSet Nat)).insert 0 (({} : Std.TreeSet Nat).insert 1) }
  let info : MatcherInfo := {
    numParams := 2, numDiscrs := 2,
    altInfos := #[{ numFields := 1, numOverlaps := 0, hasUnitThunk := false },
                  { numFields := 2, numOverlaps := 1, hasUnitThunk := true }],
    uElimPos? := some 0,
    discrInfos := #[{ hName? := some `first }, { hName? := some `second }],
    overlaps }
  unless boundaryMatcherInfoEq info info do throwError "identical matcher metadata rejected"
  for (label, changed) in #[
      ("parameters", { info with numParams := 3 }),
      ("discriminants", { info with numDiscrs := 3 }),
      ("universe", { info with uElimPos? := none }),
      ("alternative fields", { info with altInfos := info.altInfos.set! 0 { info.altInfos[0]! with numFields := 0 } }),
      ("alternative overlaps", { info with altInfos := info.altInfos.set! 0 { info.altInfos[0]! with numOverlaps := 1 } }),
      ("unit thunk", { info with altInfos := info.altInfos.set! 0 { info.altInfos[0]! with hasUnitThunk := true } }),
      ("alternative order", { info with altInfos := info.altInfos.reverse }),
      ("discriminant order", { info with discrInfos := info.discrInfos.reverse }),
      ("overlap edge", { info with overlaps := overlaps.insert 2 0 }),
      ("explicit empty overlap", { info with overlaps := { map := overlaps.map.insert 2 {} } })] do
    if boundaryMatcherInfoEq info changed then throwError "metadata mutation accepted: {label}"
  let eqn : Match.MatchEqns := {
    eqnNames := #[`eq1, `eq2], splitterName := `splitter, splitterMatchInfo := info }
  let state : Match.MatchEqnsExtState := {
    map := ({} : PHashMap Name Match.MatchEqns).insert `matcher eqn,
    eqns := (({} : PHashSet Name).insert `eq1).insert `eq2 }
  unless boundaryMatchEqnsStateEq state state do throwError "identical matcher state rejected"
  for (label, changed) in #[
      ("map key", { state with map := ({} : PHashMap Name Match.MatchEqns).insert `other eqn }),
      ("equation order", { state with map := state.map.insert `matcher { eqn with eqnNames := eqn.eqnNames.reverse } }),
      ("splitter", { state with map := state.map.insert `matcher { eqn with splitterName := `other } }),
      ("equation set", { state with eqns := state.eqns.insert `extra }),
      ("missing equation", { state with eqns := state.eqns.erase `eq1 }),
      ("matcher metadata", { state with map := state.map.insert `matcher { eqn with splitterMatchInfo := { info with numParams := 7 } } })] do
    if boundaryMatchEqnsStateEq state changed then throwError "state mutation accepted: {label}"
  let reordered := { state with eqns := (({} : PHashSet Name).insert `eq2).insert `eq1 }
  unless boundaryMatchEqnsStateEq state reordered do throwError "set insertion order affected comparison"
  logInfo "matcher state: 16 mutations rejected; unchanged and reordered sets accepted"
