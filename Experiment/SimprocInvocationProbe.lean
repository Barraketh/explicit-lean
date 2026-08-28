import ExplicitLean.SimpEngine

open Lean Meta Elab Tactic

namespace SimprocInvocationProbe

inductive Disposition where
  | done
  | visit
  | continueSome
  | continueNone
  deriving Inhabited

opaque probeF : Nat → Nat → Nat
opaque probeG : Nat → Nat → Nat
axiom probeFG : probeF = probeG

def probeInput (args : Array Expr) : Expr :=
  mkAppN (mkConst ``probeF) args

def probeOutput : Expr := mkConst ``probeG

def probeResult : Simp.Result := {
  expr := probeOutput
  proof? := some (mkConst ``probeFG)
  cache := false
}

def countingSimpProc (peeled : Expr) (disposition : Disposition) : Simp.Simproc :=
  fun input => do
    unless Expr.equal input peeled do
      throwError "simproc received the wrong peeled input"
    modify fun state : Simp.State => { state with numSteps := state.numSteps + 1 }
    match disposition with
    | .done => return .done probeResult
    | .visit => return .visit probeResult
    | .continueSome => return .continue (some probeResult)
    | .continueNone => return .continue

def countingDSimpProc (peeled : Expr) (disposition : Disposition) : Simp.DSimproc :=
  fun input => do
    unless Expr.equal input peeled do
      throwError "dsimproc received the wrong peeled input"
    modify fun state : Simp.State => { state with numSteps := state.numSteps + 1 }
    match disposition with
    | .done => return .done probeOutput
    | .visit => return .visit probeOutput
    | .continueSome => return .continue (some probeOutput)
    | .continueNone => return .continue

def forbiddenSimpProc : Simp.Simproc := fun _ =>
  throwError "ordinary Simproc was executed by tryD"

def mkEntry (proc : Sum Simp.Simproc Simp.DSimproc) : Simp.SimprocEntry :=
  { declName := `SimprocInvocationProbe.entry, proc }

def exprFingerprint (expression : Expr) : String := toString expression

def reprFingerprint {α} [Repr α] (value : α) : String := reprStr value

def sortStrings (values : List String) : List String :=
  values.toArray.qsort (· < ·) |>.toList

def listFingerprint (values : List String) : String :=
  String.intercalate "," (sortStrings values)

def optionExprFingerprint : Option Expr → String
  | none => "none"
  | some expression => "some:" ++ exprFingerprint expression

def resultFingerprint (result : Simp.Result) : String :=
  s!"{exprFingerprint result.expr}|{optionExprFingerprint result.proof?}|{result.cache}"

def cacheFingerprint (cache : Simp.Cache) : String :=
  let entries := cache.toList.map fun (key, value) =>
    s!"{exprFingerprint key}=>{resultFingerprint value}"
  s!"stage₁={cache.stage₁};{listFingerprint entries}"

def congrTheoremFingerprint (theorem? : Option CongrTheorem) : String :=
  match theorem? with
  | none => "none"
  | some congrTheorem =>
    s!"{exprFingerprint congrTheorem.type}|{exprFingerprint congrTheorem.proof}|{reprFingerprint congrTheorem.argKinds}"

def congrCacheFingerprint (cache : ExprMap (Option CongrTheorem)) : String :=
  let entries := cache.toList.map fun (key, value) =>
    s!"{exprFingerprint key}=>{congrTheoremFingerprint value}"
  listFingerprint entries

def dsimpCacheFingerprint (cache : ExprStructMap Expr) : String :=
  let entries := cache.toList.map fun (key, value) =>
    s!"{exprFingerprint key.val}=>{exprFingerprint value}"
  listFingerprint entries

def originFingerprint (origin : Origin) : String := reprFingerprint origin

def usedTheoremsFingerprint (used : Simp.UsedSimps) : String :=
  let entries := used.map.toList.map fun (origin, count) =>
    s!"{originFingerprint origin}=>{count}"
  s!"size={used.size};{listFingerprint entries}"

def simpTheoremFingerprint (simpThm : SimpTheorem) : String :=
  s!"keys={reprFingerprint simpThm.keys}|levels={reprFingerprint simpThm.levelParams}|" ++
    s!"proof={exprFingerprint simpThm.proof}|priority={simpThm.priority}|post={simpThm.post}|" ++
    s!"perm={simpThm.perm}|origin={originFingerprint simpThm.origin}|rfl={simpThm.rfl}|" ++
    s!"backwardRfl={simpThm.backwardRfl}"

def diagnosticsFingerprint (diagnostics : Simp.Diagnostics) : String :=
  let used := diagnostics.usedThmCounter.toList.map fun (origin, count) =>
    s!"{originFingerprint origin}=>{count}"
  let tried := diagnostics.triedThmCounter.toList.map fun (origin, count) =>
    s!"{originFingerprint origin}=>{count}"
  let congr := diagnostics.congrThmCounter.toList.map fun (name, count) =>
    s!"{toString name}=>{count}"
  let badKeys := diagnostics.thmsWithBadKeys.toList.map simpTheoremFingerprint
  s!"used={listFingerprint used};tried={listFingerprint tried};" ++
    s!"congr={listFingerprint congr};badKeys={listFingerprint badKeys}"

structure StateSummary where
  numSteps : Nat
  cache : String
  congrCache : String
  dsimpCache : String
  usedTheorems : String
  diagnostics : String
  deriving BEq, Repr

def summarizeState (state : Simp.State) : StateSummary := {
  numSteps := state.numSteps
  cache := cacheFingerprint state.cache
  congrCache := congrCacheFingerprint state.congrCache
  dsimpCache := dsimpCacheFingerprint state.dsimpCache
  usedTheorems := usedTheoremsFingerprint state.usedTheorems
  diagnostics := diagnosticsFingerprint state.diag
}

def runFromSavedMeta (ctx : Simp.Context) (state : Simp.State) (action : SimpM α) : MetaM
    (α × Simp.State) := do
  let saved ← Meta.saveState
  let result ← try
    Lean.Meta.Simp.SimpM.run ctx state {} action
  finally
    saved.restore
  return result

def assertExpr (label : String) (expected actual : Expr) : MetaM Unit := do
  unless Expr.equal expected actual do
    throwError "{label}: expression mismatch"

def assertProof (label : String) (expected actual : Option Expr) : MetaM Unit := do
  match expected, actual with
  | none, none => pure ()
  | some expected, some actual => assertExpr label expected actual
  | _, _ => throwError "{label}: proof presence mismatch"

def assertResult (label : String) (expected actual : Simp.Result) : MetaM Unit := do
  assertExpr (label ++ ".expr") expected.expr actual.expr
  assertProof (label ++ ".proof") expected.proof? actual.proof?
  unless expected.cache == actual.cache do
    throwError "{label}.cache: mismatch"

def assertStep (label : String) (expected actual : Simp.Step) : MetaM Unit := do
  match expected, actual with
  | .done expected, .done actual => assertResult (label ++ ".done") expected actual
  | .visit expected, .visit actual => assertResult (label ++ ".visit") expected actual
  | .continue none, .continue none => pure ()
  | .continue (some expected), .continue (some actual) =>
    assertResult (label ++ ".continue") expected actual
  | _, _ => throwError "{label}: step constructor mismatch"

def assertDStep (label : String) (expected actual : Simp.DStep) : MetaM Unit := do
  match expected, actual with
  | .done expected, .done actual => assertExpr (label ++ ".done") expected actual
  | .visit expected, .visit actual => assertExpr (label ++ ".visit") expected actual
  | .continue none, .continue none => pure ()
  | .continue (some expected), .continue (some actual) =>
    assertExpr (label ++ ".continue") expected actual
  | _, _ => throwError "{label}: DStep constructor mismatch"

def assertStateDelta (label : String) (initial expected actual : Simp.State)
    (expectedNumSteps : Nat) : MetaM Unit := do
  let expected := summarizeState expected
  let actual := summarizeState actual
  unless expected == actual do
    throwError "{label}: Simp state delta mismatch: {repr expected} != {repr actual}"
  unless expected.numSteps == initial.numSteps + expectedNumSteps do
    throwError "{label}: upstream Simp state had the wrong numSteps delta"
  unless actual.numSteps == initial.numSteps + expectedNumSteps do
    throwError "{label}: wrapper Simp state had the wrong numSteps delta"

def assertRawSimpStep (label : String) (disposition : Disposition)
    (actual : Simp.Step) (convertedDSimproc : Bool) : MetaM Unit := do
  let expected : Simp.Step := if convertedDSimproc then
    match disposition with
    | .done => .done { expr := probeOutput }
    | .visit => .visit { expr := probeOutput }
    | .continueSome => .continue (some { expr := probeOutput })
    | .continueNone => .continue
  else
    match disposition with
    | .done => .done probeResult
    | .visit => .visit probeResult
    | .continueSome => .continue (some probeResult)
    | .continueNone => .continue
  assertStep (label ++ ".raw") expected actual

def assertLiftedSimpResult (label : String) (input : Expr) (args : Array Expr)
    (convertedDSimproc : Bool) (step : Simp.Step) : MetaM Unit := do
  let output := mkAppN probeOutput args
  let expectedProofType ← Meta.mkEq input output
  match step with
  | .done result | .visit result
  | .continue (some result) =>
    assertExpr (label ++ ".lifted.expr") output result.expr
    if convertedDSimproc then
      unless result.proof?.isNone do
        throwError "{label}.lifted.proof: converted DStep unexpectedly has a proof"
    else
      unless result.cache do
        throwError "{label}.lifted.cache: raw cache=false was not reset to default true"
      let some proof := result.proof?
        | throwError "{label}.lifted.proof: proof was dropped"
      unless (← isDefEq (← inferType proof) expectedProofType) do
        throwError "{label}.lifted.proof: wrong lifted proof type"
  | .continue none => pure ()

def checkSimpInvocation (ctx : Simp.Context) (entry : Simp.SimprocEntry)
    (numExtraArgs : Nat) (input peeled : Expr) (args : Array Expr)
    (disposition : Disposition) (convertedDSimproc : Bool) : MetaM Unit := do
  let initial : Simp.State := {}
  let (upstream, upstreamState) ← runFromSavedMeta ctx initial
    (Simp.SimprocEntry.try entry numExtraArgs input)
  let (actual, actualState) ← runFromSavedMeta ctx initial
    (Lean.Meta.Simp.Engine.trySimprocEntry entry numExtraArgs input)
  assertStep "try.final" upstream actual.finalStep
  assertStateDelta "try.state" initial upstreamState actualState 1
  unless upstreamState.numSteps == 1 && actualState.numSteps == 1 do
    throwError "try procedure was not invoked exactly once"
  assertExpr "try.peeledInput" peeled actual.peeledInput
  unless actual.extraArguments.size == args.size do
    throwError "try.extraArguments: size mismatch"
  for h : index in *...args.size do
    assertExpr "try.extraArguments" args[index] actual.extraArguments[index]!
  assertRawSimpStep "try" disposition actual.procedureStep
    convertedDSimproc
  assertLiftedSimpResult "try" input args convertedDSimproc actual.finalStep

def checkDSimpInvocation (ctx : Simp.Context) (entry : Simp.SimprocEntry)
    (numExtraArgs : Nat) (input peeled : Expr) (args : Array Expr)
    (disposition : Disposition) : MetaM Unit := do
  let initial : Simp.State := {}
  let (upstream, upstreamState) ← runFromSavedMeta ctx initial
    (Simp.SimprocEntry.tryD entry numExtraArgs input)
  let (actual, actualState) ← runFromSavedMeta ctx initial
    (Lean.Meta.Simp.Engine.tryDSimprocEntry entry numExtraArgs input)
  assertDStep "tryD.final" upstream actual.finalStep
  let expectedProcedure : Simp.DStep := match disposition with
    | .done => .done probeOutput
    | .visit => .visit probeOutput
    | .continueSome => .continue (some probeOutput)
    | .continueNone => .continue
  assertDStep "tryD.procedure" expectedProcedure actual.procedureStep
  assertStateDelta "tryD.state" initial upstreamState actualState 1
  unless upstreamState.numSteps == 1 && actualState.numSteps == 1 && actual.executed do
    throwError "tryD DSimproc was not invoked exactly once"
  assertExpr "tryD.peeledInput" peeled actual.peeledInput
  unless actual.extraArguments.size == args.size do
    throwError "tryD.extraArguments: size mismatch"
  for h : index in *...args.size do
    assertExpr "tryD.extraArguments" args[index] actual.extraArguments[index]!
  match actual.finalStep with
  | .done output | .visit output | .continue (some output) =>
    assertExpr "tryD.lifted.expr" (mkAppN probeOutput args) output
  | .continue none => pure ()

def checkOrdinaryTryD (ctx : Simp.Context) (entry : Simp.SimprocEntry)
    (numExtraArgs : Nat) (input peeled : Expr) (args : Array Expr) : MetaM Unit := do
  let initial : Simp.State := {}
  let (upstream, upstreamState) ← runFromSavedMeta ctx initial
    (Simp.SimprocEntry.tryD entry numExtraArgs input)
  let (actual, actualState) ← runFromSavedMeta ctx initial
    (Lean.Meta.Simp.Engine.tryDSimprocEntry entry numExtraArgs input)
  assertDStep "tryD.ordinary.final" upstream actual.finalStep
  assertDStep "tryD.ordinary.raw" .continue actual.procedureStep
  assertStateDelta "tryD.ordinary.state" initial upstreamState actualState 0
  unless upstreamState.numSteps == 0 && actualState.numSteps == 0 && !actual.executed do
    throwError "tryD ordinary Simproc was executed"
  assertExpr "tryD.ordinary.peeledInput" peeled actual.peeledInput
  unless actual.extraArguments.size == args.size do
    throwError "tryD.ordinary.extraArguments: size mismatch"
  for h : index in *...args.size do
    assertExpr "tryD.ordinary.extraArguments" args[index] actual.extraArguments[index]!

def checkArrayExhaustionCache : MetaM Unit := do
  let input := mkConst ``probeF
  let accumulator : Simp.Engine.SimprocArrayAccumulator := { expression := input }
  let accumulator ← accumulator.push { expr := probeOutput, cache := false }
  unless !accumulator.cache do
    throwError "simproc array accumulator did not retain the synthetic cache=false input"
  match accumulator.finish with
  | .continue (some result) =>
    assertExpr "simprocArray.finish.expr" probeOutput result.expr
    unless result.cache do
      throwError "simproc array exhaustion did not restore the default cache=true result"
  | _ => throwError "simproc array exhaustion returned the wrong Step"

elab "check_simproc_invocation" : tactic => withMainContext do
  let ctx ← Simp.mkContext
  let arg₁ := mkRawNatLit 7
  let arg₂ := mkRawNatLit 11
  let zeroArgs : Array Expr := #[]
  let extraArgs : Array Expr := #[arg₁, arg₂]
  let zeroInput := probeInput zeroArgs
  let extraInput := probeInput extraArgs
  let zeroPeeled := mkConst ``probeF
  let extraPeeled := mkConst ``probeF
  for disposition in #[.done, .visit, .continueSome, .continueNone] do
    let entry := mkEntry (.inl (countingSimpProc extraPeeled disposition))
    checkSimpInvocation ctx entry 2 extraInput extraPeeled extraArgs disposition false
  let zeroEntry := mkEntry (.inl (countingSimpProc zeroPeeled .done))
  checkSimpInvocation ctx zeroEntry 0 zeroInput zeroPeeled zeroArgs .done false
  for disposition in #[.done, .visit, .continueSome, .continueNone] do
    let entry := mkEntry (.inr (countingDSimpProc extraPeeled disposition))
    checkSimpInvocation ctx entry 2 extraInput extraPeeled extraArgs disposition true
    checkDSimpInvocation ctx entry 2 extraInput extraPeeled extraArgs disposition
  let zeroDEntry := mkEntry (.inr (countingDSimpProc zeroPeeled .done))
  checkSimpInvocation ctx zeroDEntry 0 zeroInput zeroPeeled zeroArgs .done true
  checkDSimpInvocation ctx zeroDEntry 0 zeroInput zeroPeeled zeroArgs .done
  let ordinaryTryDEntry := mkEntry (.inl forbiddenSimpProc)
  checkOrdinaryTryD ctx ordinaryTryDEntry 2 extraInput extraPeeled extraArgs
  checkArrayExhaustionCache
  logInfo "SIMP_ENGINE_SIMPROC_INVOCATION statuses=done,visit,continueSome,continueNone extraArgs=0,2: ok"

example : True := by
  check_simproc_invocation
  trivial

end SimprocInvocationProbe
