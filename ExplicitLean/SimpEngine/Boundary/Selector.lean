module
prelude

public meta import Lean.Meta.Basic
public meta import Lean.Meta.InferType
public meta import Lean.Data.Json

public meta section

open Lean Meta

namespace ExplicitLean.SimpEngine.Boundary

/-
  This module deliberately owns its fingerprint implementation.  In
  particular, it does not import the legacy recording/replay IR or any of the
  simplifier implementation modules.  The selector is an observation of the
  state at the boundary, not an observation of how a tactic reached it.
-/

private def digest (kind payload : String) : String :=
  s!"{kind}-v1:{hash payload}"

private def binderInfoTag : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private def localDeclKindTag : LocalDeclKind → String
  | .default => "default"
  | .implDetail => "implDetail"
  | .auxDecl => "auxDecl"

private def localDeclNondep : LocalDecl → Bool
  | .cdecl .. => false
  | .ldecl (nondep := nondep) .. => nondep

private def metavariableKindTag : MetavarKind → String
  | .natural => "natural"
  | .synthetic => "synthetic"
  | .syntheticOpaque => "syntheticOpaque"

private structure CanonicalState where
  exprMVars : Std.HashMap MVarId Nat := {}
  levelMVars : Std.HashMap LMVarId Nat := {}
  freeFVars : Std.HashMap FVarId Nat := {}
  nextExprMVar : Nat := 0
  nextLevelMVar : Nat := 0
  nextFreeFVar : Nat := 0
  exprHashes : ExprStructMap UInt64 := {}
  levelHashes : Std.HashMap Level UInt64 := {}

private abbrev CanonicalM := StateT CanonicalState MetaM

private partial def canonicalLevelHash (level : Level) : CanonicalM UInt64 := do
  if let some cached := (← get).levelHashes.get? level then
    return cached
  let result ← match level with
    | .zero => pure 211
    | .succ child =>
        return mixHash 223 (← canonicalLevelHash child)
    | .max lhs rhs =>
        return mixHash 227 (mixHash (← canonicalLevelHash lhs)
          (← canonicalLevelHash rhs))
    | .imax lhs rhs =>
        return mixHash 229 (mixHash (← canonicalLevelHash lhs)
          (← canonicalLevelHash rhs))
    | .param name => pure <| mixHash 233 (hash name)
    | .mvar id =>
        let state ← get
        if let some ordinal := state.levelMVars.get? id then
          pure <| mixHash 239 (hash ordinal)
        else
          let ordinal := state.nextLevelMVar
          modify fun state => { state with
            levelMVars := state.levelMVars.insert id ordinal
            nextLevelMVar := ordinal + 1 }
          pure <| mixHash 239 (hash ordinal)
  modify fun state => { state with
    levelHashes := state.levelHashes.insert level result }
  return result

/-
  Expression binders are represented with de Bruijn indices.  We therefore
  intentionally discard binder names below.  Bound free variables are assigned
  ordinals while walking the binder; ordinary free variables use their local
  declaration index, which is stable across regenerated contexts.

  When `eraseProofs` is true, every proof-valued subterm contributes the hash
  of its type only.  Proof constructors and private proof declaration names
  consequently cannot make two semantically identical boundary states select
  different variants.
-/
private partial def canonicalExprHash (lctx : LocalContext) (eraseProofs : Bool)
    (boundFVars : Array Expr) (boundOrdinals : Std.HashMap FVarId Nat)
    (expression : Expr) : CanonicalM UInt64 := do
  let expression ← liftM <| (instantiateMVars expression : MetaM Expr)
  let opened := if boundFVars.isEmpty then expression else
    expression.instantiateRev boundFVars
  if eraseProofs && (← liftM <| isProof opened) then
    let type ← liftM <| inferType opened
    return mixHash 293 <| ← canonicalExprHash lctx eraseProofs
      boundFVars boundOrdinals type
  let cacheable := !expression.hasLooseBVars
  if cacheable then
    if let some cached := (← get).exprHashes.get? expression then
      return cached
  let result ← match expression with
    | .bvar index => pure <| mixHash 307 (hash index)
    | .fvar id =>
        let state ← get
        if let some ordinal := boundOrdinals.get? id then
          pure <| mixHash 311 (hash ordinal)
        else if let some decl := lctx.find? id then
          pure <| mixHash 313 (hash decl.index)
        else if let some ordinal := state.freeFVars.get? id then
          pure <| mixHash 317 (hash ordinal)
        else
          let ordinal := state.nextFreeFVar
          modify fun state => { state with
            freeFVars := state.freeFVars.insert id ordinal
            nextFreeFVar := ordinal + 1 }
          pure <| mixHash 317 (hash ordinal)
    | .mvar id =>
        let state ← get
        if let some ordinal := state.exprMVars.get? id then
          pure <| mixHash 319 (hash ordinal)
        else
          let ordinal := state.nextExprMVar
          modify fun state => { state with
            exprMVars := state.exprMVars.insert id ordinal
            nextExprMVar := ordinal + 1 }
          pure <| mixHash 319 (hash ordinal)
    | .sort level => pure <| mixHash 323 (← canonicalLevelHash level)
    | .const name levels => do
        let mut result := mixHash 331 (hash name)
        for level in levels do
          result := mixHash result (← canonicalLevelHash level)
        pure result
    | .app function argument =>
        pure <| mixHash 337 <| mixHash
          (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals function)
          (← canonicalExprHash lctx eraseProofs boundFVars boundOrdinals argument)
    | .lam name type body binderInfo | .forallE name type body binderInfo => do
        let typeHash ← canonicalExprHash lctx eraseProofs boundFVars
          boundOrdinals type
        let state ← get
        let openedType := type.instantiateRev boundFVars
        let (bodyHash, state) ← liftM <| withLocalDecl name binderInfo openedType fun x =>
          (canonicalExprHash lctx eraseProofs (boundFVars.push x)
            (boundOrdinals.insert x.fvarId! boundFVars.size) body).run state
        set state
        let tag := if expression.isLambda then 347 else 349
        pure <| mixHash tag <| mixHash (hash (binderInfoTag binderInfo)) <|
          mixHash typeHash bodyHash
    | .letE name type value body nondep => do
        let typeHash ← canonicalExprHash lctx eraseProofs boundFVars
          boundOrdinals type
        let valueHash ← canonicalExprHash lctx eraseProofs boundFVars
          boundOrdinals value
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

private def observingMetaState (action : MetaM α) : MetaM α := do
  let core ← getThe Core.State
  let metaState ← getThe Meta.State
  try action finally
    modifyThe Core.State fun _ => core
    modifyThe Meta.State fun _ => metaState

private def runCanonicalHash (lctx : LocalContext) (expression : Expr)
    (state : CanonicalState := {}) : MetaM (UInt64 × CanonicalState) := do
  withLCtx lctx (← getLocalInstances) do
    (canonicalExprHash lctx true #[] {} expression).run state

/-- A canonical, ordered fingerprint of one open-goal proof state.

The field names intentionally match the legacy state observer so reports and
diagnostics remain easy to compare while the implementation stays independent
of the legacy recording/replay modules. -/
structure BoundaryStateFingerprint where
  targetFingerprint : String
  localContextFingerprint : String
  metavariableContextFingerprint : String
  goalCount : Nat
  deriving Inhabited, Repr, BEq, Lean.ToJson

abbrev StateFingerprint := BoundaryStateFingerprint

private def localDeclFingerprint (decl : LocalDecl) (state : CanonicalState) :
    MetaM (String × CanonicalState) := do
  let (typeHash, state) ← runCanonicalHash (← getLCtx) decl.type state
  let (valueHash?, state) ← match decl.value? (allowNondep := true) with
    | none => pure (none, state)
    | some value =>
        let (valueHash, state) ← runCanonicalHash (← getLCtx) value state
        pure (some valueHash, state)
  -- User names are intentionally omitted: theorem-parameter alpha-renaming is
  -- an allowed materialization fallback, while declaration order/index keeps
  -- the ordered context and all expression references stable.
  pure (s!"{decl.index}:{binderInfoTag decl.binderInfo}:" ++
    s!"{localDeclKindTag decl.kind}:{localDeclNondep decl}:" ++
    s!"{typeHash}:{valueHash?}", state)

private def goalFingerprint (goal : MVarId) (state : CanonicalState) :
    MetaM (String × String × String × CanonicalState) :=
  goal.withContext do
    let decl ← goal.getDecl
    let (targetHash, state) ← runCanonicalHash decl.lctx decl.type state
    let mut locals := #[]
    let mut state := state
    for localDecl in decl.lctx do
      let (fingerprint, nextState) ← localDeclFingerprint localDecl state
      locals := locals.push fingerprint
      state := nextState
    let mut instances := #[]
    for localInstance in decl.localInstances do
      let (instanceHash, nextState) ← runCanonicalHash decl.lctx
        localInstance.fvar state
      instances := instances.push s!"{localInstance.className}:{instanceHash}"
      state := nextState
    let context := String.intercalate "|" locals.toList
    let metavariable := s!"{decl.depth}:{metavariableKindTag decl.kind}:{decl.numScopeArgs}:" ++
      String.intercalate "|" instances.toList
    pure (s!"{targetHash}", context, metavariable, state)

private def proofStateFingerprintImpl (goals : List MVarId) :
    MetaM BoundaryStateFingerprint := do
  let mut targets := #[]
  let mut contexts := #[]
  let mut metavariables := #[]
  let mut state : CanonicalState := {}
  for goal in goals do
    unless (← goal.isAssigned) do
      let (target, context, metavariable, nextState) ← goalFingerprint goal state
      targets := targets.push target
      contexts := contexts.push context
      metavariables := metavariables.push metavariable
      state := nextState
  return {
    targetFingerprint := digest "targets" (String.intercalate "|" targets.toList)
    localContextFingerprint := digest "goal-contexts"
      (String.intercalate "|" contexts.toList)
    metavariableContextFingerprint := digest "metavariable-context"
      (String.intercalate "|" metavariables.toList)
    goalCount := targets.size
  }

/-- Observe the canonical expression hash without changing meta/elaboration state. -/
def boundaryExprFingerprintHash (expression : Expr) : MetaM String :=
  observingMetaState do
    let expression ← instantiateMVars expression
    let (fingerprint, _) ← (canonicalExprHash (← getLCtx) true #[] {}
      expression).run {}
    return s!"boundary-expr-v1:{fingerprint}"

/-- Observe the ordered open goals and their visible contexts without changing state. -/
def boundaryProofStateFingerprint (goals : List MVarId) :
    MetaM BoundaryStateFingerprint :=
  observingMetaState <| proofStateFingerprintImpl goals

/-- Return a deterministic fingerprint of the complete scoped `Options` map. -/
def boundaryOptionsFingerprint (options : Options) : String :=
  digest "boundary-options" (toString options)

/-- Canonicalize the enclosing declaration used by a boundary selector. Private
declaration prefixes and elaborator macro scopes are implementation details and
must not make the same authored caller select a different variant. -/
def boundaryCallerIdentity (caller : Name) : String :=
  (privateToUserName caller).eraseMacroScopes.toString

/-- Render an optional enclosing declaration for the guard syntax. An absent
caller is represented by the empty string. -/
def boundaryCallerIdentity? (caller? : Option Name) : String :=
  caller?.map boundaryCallerIdentity |>.getD ""

/- Compatibility aliases for callers that already live in the Boundary namespace. -/
def proofStateFingerprint (goals : List MVarId) : MetaM BoundaryStateFingerprint :=
  boundaryProofStateFingerprint goals

def optionsFingerprint (options : Options) : String :=
  boundaryOptionsFingerprint options

end ExplicitLean.SimpEngine.Boundary
