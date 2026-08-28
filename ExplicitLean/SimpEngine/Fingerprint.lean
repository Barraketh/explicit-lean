module
prelude

public import ExplicitLean.SimpEngine.IR

public section

namespace Lean.Meta.Simp.Engine

/-- Complete Core/Meta state used to make diagnostic and semantic observers
    genuinely effect-free. `Meta.saveState` intentionally restores only
    backtrackable fields and therefore does not isolate name generators or
    caches. -/
structure FullMetaState where
  core : Core.State
  metaState : Meta.State

def saveFullMetaState : MetaM FullMetaState := do
  return { core := ← getThe Core.State, metaState := ← getThe Meta.State }

def FullMetaState.restore (state : FullMetaState) : MetaM Unit := do
  modifyThe Core.State fun _ => state.core
  modifyThe Meta.State fun _ => state.metaState

def withRestoredFullMetaState (action : MetaM α) : MetaM α := do
  let saved ← saveFullMetaState
  try action finally saved.restore

/-- Simproc result-size diagnostics are deliberately bounded. The count is
    computed over the expression DAG, so reaching this limit does not allocate
    the corresponding expanded tree. -/
def exprTreeSizeLimit : Nat := 1000000000000

private structure ExprSizeState where
  treeSizes : ExprStructMap (Nat × Bool) := {}
  dagNodes : Nat := 0

private abbrev ExprSizeM := StateM ExprSizeState

private def addTreeSize (lhs : Nat × Bool) (rhs : Nat × Bool) : Nat × Bool :=
  if lhs.2 || rhs.2 || lhs.1 >= exprTreeSizeLimit ||
      rhs.1 >= exprTreeSizeLimit - lhs.1 then
    (exprTreeSizeLimit, true)
  else
    (lhs.1 + rhs.1, false)

private partial def computeExprTreeSize (expression : Expr) : ExprSizeM (Nat × Bool) := do
  if let some result := (← get).treeSizes.get? { val := expression } then
    return result
  modify fun state => { state with dagNodes := state.dagNodes + 1 }
  let mut result := (1, false)
  match expression with
  | .forallE _ domain body _ | .lam _ domain body _ =>
      result := addTreeSize result (← computeExprTreeSize domain)
      result := addTreeSize result (← computeExprTreeSize body)
  | .mdata _ body | .proj _ _ body =>
      result := addTreeSize result (← computeExprTreeSize body)
  | .letE _ type value body _ =>
      result := addTreeSize result (← computeExprTreeSize type)
      result := addTreeSize result (← computeExprTreeSize value)
      result := addTreeSize result (← computeExprTreeSize body)
  | .app function argument =>
      result := addTreeSize result (← computeExprTreeSize function)
      result := addTreeSize result (← computeExprTreeSize argument)
  | _ => pure ()
  modify fun state => {
    state with treeSizes := state.treeSizes.insert { val := expression } result }
  return result

def exprSize (expression : Expr) : MetaM ExprSize := do
  let expression ← instantiateMVars expression
  let (treeSize, state) := (computeExprTreeSize expression).run {}
  return {
    treeNodes := treeSize.1
    treeNodesCapped := treeSize.2
    dagNodes := state.dagNodes
  }

private structure CanonicalHashState where
  exprMVars : Std.HashMap MVarId Nat := {}
  levelMVars : Std.HashMap LMVarId Nat := {}
  exprHashes : Std.HashMap Expr UInt64 := {}
  levelHashes : Std.HashMap Level UInt64 := {}
  nextExprMVar : Nat := 0
  nextLevelMVar : Nat := 0

private abbrev CanonicalHashM := StateT CanonicalHashState MetaM

private def binderInfoHash : BinderInfo → UInt64
  | .default => 101
  | .implicit => 103
  | .strictImplicit => 107
  | .instImplicit => 109

private partial def canonicalLevelHash (level : Level) : CanonicalHashM UInt64 := do
  if let some cached := (← get).levelHashes.get? level then
    return cached
  let result ← match level with
    | .zero => pure 211
    | .succ child => return mixHash 223 (← canonicalLevelHash child)
    | .max lhs rhs =>
        return mixHash 227 (mixHash (← canonicalLevelHash lhs) (← canonicalLevelHash rhs))
    | .imax lhs rhs =>
        return mixHash 229 (mixHash (← canonicalLevelHash lhs) (← canonicalLevelHash rhs))
    | .param name => pure <| mixHash 233 (hash name)
    | .mvar mvarId => do
        let state ← get
        if let some ordinal := state.levelMVars.get? mvarId then
          pure <| mixHash 239 (hash ordinal)
        else
          modify fun _ => { state with
            levelMVars := state.levelMVars.insert mvarId state.nextLevelMVar
            nextLevelMVar := state.nextLevelMVar + 1 }
          pure <| mixHash 239 (hash state.nextLevelMVar)
  modify fun state => { state with
    levelHashes := state.levelHashes.insert level result }
  return result

/-- Hash the expression DAG directly. Memoizing by expression identity is
    semantic as well as an optimization: Lean expressions are shared DAGs, and
    expanding them into a canonical tree string can require exponential space. -/
private partial def canonicalExprHash (lctx : LocalContext) (eraseProofs : Bool)
    (boundFVars : Array Expr) (boundOrdinals : Std.HashMap FVarId Nat)
    (expression : Expr) : CanonicalHashM UInt64 := do
  let cacheable := !expression.hasLooseBVars
  if cacheable then
    if let some cached := (← get).exprHashes.get? expression then
      return cached
  let opened := if boundFVars.isEmpty then expression else expression.instantiateRev boundFVars
  let result ← if eraseProofs && (← liftM <| Meta.isProof opened) then
    let type ← liftM <| inferType opened
    pure <| mixHash 293
      (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals type)
  else match expression with
    | .bvar index => pure <| mixHash 307 (hash index)
    | .fvar fvarId =>
        pure <| match boundOrdinals.get? fvarId with
          | some ordinal => mixHash 311 (hash ordinal)
          | none => mixHash 313 <| hash <| (lctx.find? fvarId).map (·.index)
    | .mvar mvarId => do
        let state ← get
        if let some ordinal := state.exprMVars.get? mvarId then
          pure <| mixHash 313 (hash ordinal)
        else
          modify fun _ => { state with
            exprMVars := state.exprMVars.insert mvarId state.nextExprMVar
            nextExprMVar := state.nextExprMVar + 1 }
          pure <| mixHash 313 (hash state.nextExprMVar)
    | .sort level => pure <| mixHash 317 (← canonicalLevelHash level)
    | .const name levels => do
        let mut result := mixHash 331 (hash name)
        for level in levels do
          result := mixHash result (← canonicalLevelHash level)
        pure result
    | .app fn arg =>
        pure <| mixHash 337 <|
          mixHash (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals fn)
            (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals arg)
    | .lam name type body binderInfo | .forallE name type body binderInfo => do
        let typeHash ← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals type
        let state ← get
        let (bodyHash, state) ← liftM <| withLocalDecl name binderInfo opened.bindingDomain! fun x =>
          (canonicalExprHash lctx eraseProofs (boundFVars.push x)
            (boundOrdinals.insert x.fvarId! boundFVars.size) body).run state
        set state
        let tag := if expression.isLambda then 347 else 349
        pure <| mixHash tag <| mixHash (binderInfoHash binderInfo) <|
          mixHash typeHash bodyHash
    | .letE name type value body nondep => do
        let typeHash ← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals type
        let valueHash ← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals value
        let state ← get
        let openedType := type.instantiateRev boundFVars
        let openedValue := value.instantiateRev boundFVars
        let (bodyHash, state) ← liftM <| withLetDecl name openedType openedValue
            (nondep := nondep) fun x =>
          (canonicalExprHash lctx eraseProofs (boundFVars.push x)
            (boundOrdinals.insert x.fvarId! boundFVars.size) body).run state
        set state
        pure <| mixHash 353 <| mixHash (hash nondep) <|
          mixHash typeHash <| mixHash valueHash bodyHash
    | .lit literal => pure <| mixHash 359 (hash literal)
    | .mdata _ child =>
        canonicalExprHash lctx eraseProofs boundFVars boundOrdinals child
    | .proj name index child =>
        pure <| mixHash 367 <| mixHash (hash name) <|
          mixHash (hash index)
            (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals child)
  if cacheable then
    modify fun state => { state with
      exprHashes := state.exprHashes.insert expression result }
  return result

private def eraseProofTerms (expression : Expr) : MetaM Expr :=
  Meta.transform (skipConstInApp := true) expression
    (pre := fun subexpression => do
      if ← Meta.isProof subexpression then
        return .continue (← mkSorry (← inferType subexpression) true)
      return .continue)

private def observingMetaState (action : MetaM α) : MetaM α := do
  withRestoredFullMetaState action

def exprFingerprint (expression : Expr) : MetaM ExprFingerprint := observingMetaState do
  let expression ← instantiateMVars expression
  let lctx ← getLCtx
  let (fingerprint, _) ← (canonicalExprHash lctx true #[] {} expression).run {}
  let printableExpression ← eraseProofTerms expression
  let printable ← try
    let rendered ← withOptions
        (fun options => options.setBool `pp.mvars false
          |>.setBool `pp.mvars.levels false
          |>.setBool `pp.fvars.anonymous false) <| ppExpr printableExpression
    pure (toString rendered)
  catch _ =>
    pure "<callback-local expression>"
  let printable := printable.replace "_fvar._" "<free-variable>"
  let printable :=
    if printable.length > 512 then (printable.take 512).toString ++ "…" else printable
  return { printable, fingerprint := s!"expr-v2:{fingerprint}" }

def exprFingerprintHash (expression : Expr) : MetaM String := observingMetaState do
  let expression ← instantiateMVars expression
  let (fingerprint, _) ←
    (canonicalExprHash (← getLCtx) true #[] {} expression).run {}
  return s!"expr-v2:{fingerprint}"

/-- Fingerprint an expression without erasing proof subterms. This is used only
for certificate fields where the proof constructor itself is semantic. -/
def exprStructuralFingerprintHash (expression : Expr) : MetaM String := do
  observingMetaState do
    let expression ← instantiateMVars expression
    let lctx ← getLCtx
    let (fingerprint, _) ← (canonicalExprHash lctx false #[] {} expression).run {}
    return s!"expr-structural-v2:{fingerprint}"

private def digest (kind payload : String) : String :=
  s!"{kind}-v1:{hash payload}"

def optionsFingerprint (options : Options) : String :=
  digest "options" (toString options)

def metaConfigFingerprint (config : Meta.Config) : String :=
  digest "meta-config" (toString (repr config))

def localContextFingerprint : MetaM String := do
  let mut entries := #[]
  for localDecl in (← getLCtx) do
    let typeFingerprint ← exprFingerprintHash localDecl.type
    let valueFingerprint ← localDecl.value?.mapM exprFingerprintHash
    entries := entries.push
      s!"{localDecl.index}:{repr localDecl.binderInfo}:{typeFingerprint}:{valueFingerprint}"
  return digest "local-context" (String.intercalate "|" entries.toList)

private def sortedStrings (values : List String) : List String :=
  values.toArray.qsort (· < ·) |>.toList

private def listFingerprint (values : List String) : String :=
  s!"state-list-v1:{hash (String.intercalate "," (sortedStrings values))}"

private def stateStringFingerprint (kind value : String) : String :=
  s!"{kind}-v1:{hash value}"

private structure SimpStateExprIds where
  fvars : FVarIdSet := {}
  mvars : MVarIdSet := {}
  lmvars : LMVarIdSet := {}

private partial def collectSimpStateExprIds (expression : Expr)
    (initial : SimpStateExprIds) : SimpStateExprIds :=
  match expression with
  | .fvar id => { initial with fvars := initial.fvars.insert id }
  | .mvar id => { initial with mvars := initial.mvars.insert id }
  | .sort level => { initial with lmvars := level.collectMVars initial.lmvars }
  | .const _ levels =>
      { initial with
        lmvars := levels.foldl (init := initial.lmvars) fun result level =>
          level.collectMVars result }
  | .app function argument =>
      collectSimpStateExprIds argument (collectSimpStateExprIds function initial)
  | .lam _ type body _ | .forallE _ type body _ =>
      collectSimpStateExprIds body (collectSimpStateExprIds type initial)
  | .letE _ type value body _ =>
      collectSimpStateExprIds body <| collectSimpStateExprIds value <|
        collectSimpStateExprIds type initial
  | .mdata _ body | .proj _ _ body => collectSimpStateExprIds body initial
  | _ => initial

private def collectSimpStateResultIds (result : Simp.Result)
    (initial : SimpStateExprIds) : SimpStateExprIds :=
  -- The cached proof is compared only by presence. Its proposition is fixed by
  -- the cache key and result expression, so proof-local generated IDs must not
  -- perturb canonicalization of operational expressions.
  collectSimpStateExprIds result.expr initial

private def collectOriginIds (origin : Origin)
    (initial : SimpStateExprIds) : SimpStateExprIds :=
  match origin with
  | .fvar id => { initial with fvars := initial.fvars.insert id }
  | _ => initial

private def collectSimpStateIds (state : Simp.State) : SimpStateExprIds := Id.run do
  let mut ids : SimpStateExprIds := {}
  for (key, value) in state.cache.toList do
    ids := collectSimpStateResultIds value (collectSimpStateExprIds key ids)
  for (key, value) in state.congrCache.toList do
    ids := collectSimpStateExprIds key ids
    if let some thm := value then
      ids := collectSimpStateExprIds thm.type ids
  for (key, value) in state.dsimpCache.toList do
    ids := collectSimpStateExprIds value (collectSimpStateExprIds key.val ids)
  for thm in state.diag.thmsWithBadKeys.toList do
    ids := collectOriginIds thm.origin ids
  for origin in state.usedTheorems.toArray do
    ids := collectOriginIds origin ids
  for (origin, _) in state.diag.usedThmCounter.toList do
    ids := collectOriginIds origin ids
  for (origin, _) in state.diag.triedThmCounter.toList do
    ids := collectOriginIds origin ids
  ids

private structure SimpStateExprCanon where
  fvars : Array FVarId := #[]
  mvars : Array MVarId := #[]
  lmvars : Array LMVarId := #[]
  exprHashes : ExprStructMap UInt64 := {}
  levelHashes : Std.HashMap Level UInt64 := {}

private partial def canonicalSimpStateExpr (expression : Expr)
    (initial : SimpStateExprCanon) : UInt64 × SimpStateExprCanon :=
  let rec levelGo (level : Level) (state : SimpStateExprCanon) :
      UInt64 × SimpStateExprCanon :=
    if let some result := state.levelHashes.get? level then
      (result, state)
    else
      let (result, state) := match level with
        | .zero => (501, state)
        | .succ child =>
            let (child, state) := levelGo child state
            (mixHash 503 child, state)
        | .max lhs rhs =>
            let (lhs, state) := levelGo lhs state
            let (rhs, state) := levelGo rhs state
            (mixHash 509 (mixHash lhs rhs), state)
        | .imax lhs rhs =>
            let (lhs, state) := levelGo lhs state
            let (rhs, state) := levelGo rhs state
            (mixHash 521 (mixHash lhs rhs), state)
        | .param name => (mixHash 523 (hash name), state)
        | .mvar id =>
            let (index, lmvars) := match state.lmvars.findIdx? (· == id) with
              | some index => (index, state.lmvars)
              | none => (state.lmvars.size, state.lmvars.push id)
            (mixHash 541 (hash index), { state with lmvars })
      (result, { state with levelHashes := state.levelHashes.insert level result })
  let rec go (expression : Expr) (state : SimpStateExprCanon) :
      UInt64 × SimpStateExprCanon :=
    if let some result := state.exprHashes.get? { val := expression } then
      (result, state)
    else
      let (result, state) := match expression with
        | .bvar index => (mixHash 547 (hash index), state)
        | .fvar id =>
            let (index, fvars) := match state.fvars.findIdx? (· == id) with
              | some index => (index, state.fvars)
              | none => (state.fvars.size, state.fvars.push id)
            (mixHash 557 (hash index), { state with fvars })
        | .mvar id =>
            let (index, mvars) := match state.mvars.findIdx? (· == id) with
              | some index => (index, state.mvars)
              | none => (state.mvars.size, state.mvars.push id)
            (mixHash 563 (hash index), { state with mvars })
        | .sort level =>
            let (level, state) := levelGo level state
            (mixHash 569 level, state)
        | .const name levels =>
            let (result, state) := levels.foldl
              (init := (mixHash 571 (hash name), state)) fun (result, state) level =>
                let (level, state) := levelGo level state
                (mixHash result level, state)
            (result, state)
        | .lit literal => (mixHash 577 (hash literal), state)
        | .app function argument =>
            let (function, state) := go function state
            let (argument, state) := go argument state
            (mixHash 587 (mixHash function argument), state)
        | .lam _ type body info =>
            let (type, state) := go type state
            let (body, state) := go body state
            (mixHash 593 (mixHash (binderInfoHash info) (mixHash type body)), state)
        | .forallE _ type body info =>
            let (type, state) := go type state
            let (body, state) := go body state
            (mixHash 599 (mixHash (binderInfoHash info) (mixHash type body)), state)
        | .letE _ type value body nondep =>
            let (type, state) := go type state
            let (value, state) := go value state
            let (body, state) := go body state
            (mixHash 601 (mixHash (hash nondep) (mixHash type (mixHash value body))), state)
        | .mdata data body =>
            let (body, state) := go body state
            (mixHash 607 (mixHash (hash (reprStr data)) body), state)
        | .proj name index value =>
            let (value, state) := go value state
            (mixHash 613 (mixHash (hash name) (mixHash (hash index) value)), state)
      (result, { state with
        exprHashes := state.exprHashes.insert { val := expression } result })
  go expression initial

private def canonicalSimpStateResult (result : Simp.Result)
    (initial : SimpStateExprCanon) : String × SimpStateExprCanon :=
  let (expression, state) := canonicalSimpStateExpr result.expr initial
  -- Proof irrelevance makes the proof term itself non-operational.  In
  -- particular, custom dischargers may generate extension-local private proof
  -- declarations with fresh names on two otherwise identical executions.
  -- Presence remains operational because it changes later transport.
  let proof := if result.proof?.isSome then "some" else "none"
  (s!"{expression}|{proof}|{result.cache}", state)

private def canonicalOrigin (origin : Origin) (fvars : Array FVarId) : String :=
  match origin with
  | .decl name post inverse => s!"decl:{name}:{post}:{inverse}"
  | .fvar id => s!"fvar:{(fvars.findIdx? (· == id)).getD fvars.size}"
  | .stx id stx => s!"stx:{id}:{reprStr stx}"
  | .other name => s!"other:{name}"

private def canonicalSimpCache (cache : Simp.Cache) (initial : SimpStateExprCanon) :
    String × SimpStateExprCanon := Id.run do
  let mut state := initial
  let mut entries : Array String := #[]
  for (key, value) in cache.toList do
    let (key, next) := canonicalSimpStateExpr key state
    state := next
    let (value, next) := canonicalSimpStateResult value state
    state := next
    entries := entries.push <| stateStringFingerprint "simp-cache-entry" s!"{key}=>{value}"
  return (s!"stage₁={cache.stage₁};{listFingerprint entries.toList}", state)

private def canonicalCongrTheorem (theorem? : Option CongrTheorem)
    (initial : SimpStateExprCanon) : String × SimpStateExprCanon :=
  match theorem? with
  | none => ("none", initial)
  | some thm =>
      let (type, state) := canonicalSimpStateExpr thm.type initial
      (s!"{type}|proof|{reprStr thm.argKinds}", state)

private def canonicalCongrCache (cache : ExprMap (Option CongrTheorem))
    (initial : SimpStateExprCanon) : String × SimpStateExprCanon := Id.run do
  let mut state := initial
  let mut entries : Array String := #[]
  for (key, value) in cache.toList do
    let (key, next) := canonicalSimpStateExpr key state
    state := next
    let (value, next) := canonicalCongrTheorem value state
    state := next
    entries := entries.push <| stateStringFingerprint "congr-cache-entry" s!"{key}=>{value}"
  return (listFingerprint entries.toList, state)

private def canonicalDsimpCache (cache : ExprStructMap Expr)
    (initial : SimpStateExprCanon) : String × SimpStateExprCanon := Id.run do
  let mut state := initial
  let mut entries : Array String := #[]
  for (key, value) in cache.toList do
    let (key, next) := canonicalSimpStateExpr key.val state
    state := next
    let (value, next) := canonicalSimpStateExpr value state
    state := next
    entries := entries.push <| stateStringFingerprint "dsimp-cache-entry" s!"{key}=>{value}"
  return (listFingerprint entries.toList, state)

private def canonicalSimpTheorem (thm : SimpTheorem)
    (initial : SimpStateExprCanon) : String × SimpStateExprCanon :=
  (s!"keys={reprStr thm.keys}|levels={reprStr thm.levelParams}|" ++
    s!"proof|priority={thm.priority}|post={thm.post}|" ++
    s!"perm={thm.perm}|origin={canonicalOrigin thm.origin initial.fvars}|rfl={thm.rfl}|" ++
    s!"backwardRfl={thm.backwardRfl}", initial)

private def canonicalDiagnostics (diagnostics : Simp.Diagnostics)
    (initial : SimpStateExprCanon) : String × SimpStateExprCanon := Id.run do
  let used := diagnostics.usedThmCounter.toList.map fun (origin, count) =>
    s!"{canonicalOrigin origin initial.fvars}=>{count}"
  let tried := diagnostics.triedThmCounter.toList.map fun (origin, count) =>
    s!"{canonicalOrigin origin initial.fvars}=>{count}"
  let congr := diagnostics.congrThmCounter.toList.map fun (name, count) =>
    s!"{name}=>{count}"
  let mut state := initial
  let mut badKeys : Array String := #[]
  for thm in diagnostics.thmsWithBadKeys.toList do
    let (thm, next) := canonicalSimpTheorem thm state
    state := next
    badKeys := badKeys.push thm
  return (s!"used={listFingerprint used};tried={listFingerprint tried};" ++
    s!"congr={listFingerprint congr};badKeys={listFingerprint badKeys.toList}", state)

/-- Canonical fingerprints of the complete operational simplifier state. This
    is a differential-test value, not certificate authority. -/
structure SimpStateFingerprint where
  numSteps : Nat
  cache : String
  congrCache : String
  dsimpCache : String
  usedTheorems : String
  diagnostics : String
  deriving BEq, Repr

def simpStateFingerprint (state : Simp.State) : SimpStateFingerprint :=
  let ids := collectSimpStateIds state
  let initial : SimpStateExprCanon := {
    fvars := ids.fvars.toArray.qsort (fun lhs rhs => Name.lt lhs.name rhs.name)
    mvars := ids.mvars.toArray.qsort (fun lhs rhs => Name.lt lhs.name rhs.name)
    lmvars := ids.lmvars.toArray.qsort (fun lhs rhs => Name.lt lhs.name rhs.name)
  }
  let (cache, canon) := canonicalSimpCache state.cache initial
  let (congrCache, canon) := canonicalCongrCache state.congrCache canon
  let (dsimpCache, canon) := canonicalDsimpCache state.dsimpCache canon
  let (diagnostics, canon) := canonicalDiagnostics state.diag canon
  {
    numSteps := state.numSteps
    cache
    congrCache
    dsimpCache
    usedTheorems := listFingerprint <|
      state.usedTheorems.toArray.toList.map fun origin =>
        canonicalOrigin origin canon.fvars
    diagnostics
  }

private def goalFingerprint (goal : MVarId) : MetaM (String × String × String) :=
  goal.withContext do
    let decl ← goal.getDecl
    let mut instances := #[]
    for localInstance in decl.localInstances do
      instances := instances.push
        s!"{localInstance.className}:{← exprFingerprintHash localInstance.fvar}"
    let mvarDescriptor := s!"{decl.depth}:{repr decl.kind}:{decl.numScopeArgs}:" ++
      String.intercalate "|" instances.toList
    let target ← exprFingerprintHash decl.type
    let context ← localContextFingerprint
    return (target, context, mvarDescriptor)

/-- A stable fingerprint of the proof state visible to a tactic execution. -/
def proofStateFingerprint (goals : List MVarId) : MetaM StateFingerprint := do
  let mut targets := #[]
  let mut contexts := #[]
  let mut metavariables := #[]
  for goal in goals do
    unless (← goal.isAssigned) do
      let (target, context, metavariable) ← goalFingerprint goal
      targets := targets.push target
      contexts := contexts.push context
      metavariables := metavariables.push metavariable
  return {
    targetFingerprint := digest "targets" (String.intercalate "|" targets.toList)
    localContextFingerprint := digest "goal-contexts"
      (String.intercalate "|" contexts.toList)
    metavariableContextFingerprint := digest "metavariable-context"
      (String.intercalate "|" metavariables.toList)
    goalCount := targets.size
  }

end Lean.Meta.Simp.Engine
