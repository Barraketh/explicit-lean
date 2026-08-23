module
prelude

public import ExplicitLean.SimpEngine.IR

public section

namespace Lean.Meta.Simp.Engine

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
  let saved ← Meta.saveState
  try action finally saved.restore

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
