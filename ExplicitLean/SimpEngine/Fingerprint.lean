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

def exprFingerprint (expression : Expr) : MetaM ExprFingerprint := do
  let expression ← instantiateMVars expression
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

end Lean.Meta.Simp.Engine
