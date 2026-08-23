module
prelude

public import ExplicitLean.SimpEngine.IR

public section

namespace Lean.Meta.Simp.Engine

private structure CanonicalState where
  exprMVars : Std.HashMap MVarId Nat := {}
  levelMVars : Std.HashMap LMVarId Nat := {}
  nextExprMVar : Nat := 0
  nextLevelMVar : Nat := 0

private abbrev CanonicalM := StateM CanonicalState

private def canonicalLevel : Level → CanonicalM String
  | .zero => pure "0"
  | .succ level => return s!"(succ {← canonicalLevel level})"
  | .max lhs rhs => return s!"(max {← canonicalLevel lhs} {← canonicalLevel rhs})"
  | .imax lhs rhs => return s!"(imax {← canonicalLevel lhs} {← canonicalLevel rhs})"
  | .param name => pure s!"(param {name})"
  | .mvar mvarId => do
      let state ← get
      if let some ordinal := state.levelMVars.get? mvarId then
        return s!"(level-mvar {ordinal})"
      modify fun _ => { state with
        levelMVars := state.levelMVars.insert mvarId state.nextLevelMVar
        nextLevelMVar := state.nextLevelMVar + 1 }
      return s!"(level-mvar {state.nextLevelMVar})"

private def canonicalBinderInfo : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private partial def canonicalExpr (lctx : LocalContext) : Expr → CanonicalM String
  | .bvar index => pure s!"b{index}"
  | .fvar fvarId =>
      match lctx.find? fvarId with
      | some decl => pure s!"f{decl.index}"
      | none => pure "f?"
  | .mvar mvarId => do
      let state ← get
      if let some ordinal := state.exprMVars.get? mvarId then
        return s!"(mvar {ordinal})"
      modify fun _ => { state with
        exprMVars := state.exprMVars.insert mvarId state.nextExprMVar
        nextExprMVar := state.nextExprMVar + 1 }
      return s!"(mvar {state.nextExprMVar})"
  | .sort level => return s!"(sort {← canonicalLevel level})"
  | .const name levels =>
      return s!"(const {name} [{String.intercalate "," (← levels.mapM canonicalLevel)}])"
  | .app fn arg => return s!"(app {← canonicalExpr lctx fn} {← canonicalExpr lctx arg})"
  | .lam _ type body binderInfo =>
      return s!"(lam {← canonicalExpr lctx type} {← canonicalExpr lctx body} {canonicalBinderInfo binderInfo})"
  | .forallE _ type body binderInfo =>
      return s!"(forall {← canonicalExpr lctx type} {← canonicalExpr lctx body} {canonicalBinderInfo binderInfo})"
  | .letE _ type value body nondep =>
      return s!"(let {← canonicalExpr lctx type} {← canonicalExpr lctx value} {← canonicalExpr lctx body} {nondep})"
  | .lit literal => pure s!"(lit {repr literal})"
  | .mdata _ expression => canonicalExpr lctx expression
  | .proj name index expression =>
      return s!"(proj {name} {index} {← canonicalExpr lctx expression})"

private def eraseProofTerms (expression : Expr) : MetaM Expr :=
  Meta.transform (skipConstInApp := true) expression
    (pre := fun subexpression => do
      if ← Meta.isProof subexpression then
        return .continue (← mkSorry (← inferType subexpression) true)
      return .continue)

def exprFingerprint (expression : Expr) : MetaM ExprFingerprint := do
  let expression ← instantiateMVars expression
  let expression ← eraseProofTerms expression
  let lctx ← getLCtx
  let (canonical, _) := (canonicalExpr lctx expression).run {}
  let printable ← try
    let rendered ← withOptions
        (fun options => options.setBool `pp.mvars false
          |>.setBool `pp.mvars.levels false
          |>.setBool `pp.fvars.anonymous false) <| ppExpr expression
    pure (toString rendered)
  catch _ =>
    pure s!"<callback-local expression> {canonical}"
  let printable := printable.replace "_fvar._" "<free-variable>"
  let printable :=
    if printable.length > 512 then (printable.take 512).toString ++ "…" else printable
  return { printable, fingerprint := s!"expr-v1:{hash canonical}" }

def exprFingerprintHash (expression : Expr) : MetaM String := do
  return (← exprFingerprint expression).fingerprint

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
    return (← exprFingerprintHash decl.type, ← localContextFingerprint, mvarDescriptor)

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
