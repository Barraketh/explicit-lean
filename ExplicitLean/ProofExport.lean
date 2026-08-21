module

public meta import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Refl

public meta section

open Lean Meta Elab

namespace ExplicitLean

namespace ProofExport

/- The exporter is intentionally source-oriented.  It is used both for
   theorem bodies in the proof-term experiment and for local proof bindings
   emitted by the simplifier certificate printer. -/

structure Options where
  /-- Namespace in which the generated source will be elaborated. -/
  sourceNamespace : Name := .anonymous
  /-- Source names for binders opened while rendering a theorem body. -/
  binderNames : Array Name := #[]

structure Metrics where
  privateConstantsInlined : Nat := 0
  bindingCount : Nat := 0
  haveCount : Nat := 0
  prunedCount : Nat := 0
  unsharedBytes : Nat := 0
  sharedBytes : Nat := 0
  deriving Inhabited

structure Rendered where
  /-- The expression's inferred or supplied type, rendered as source. -/
  typeText : String
  /-- The expression or body, rendered as source. -/
  valueText : String
  metrics : Metrics := {}
  deriving Inhabited

private def namedBodyOptions (opts : Lean.Options) : Lean.Options :=
  opts
    |>.setBool `pp.explicit true
    |>.setBool `pp.instances true
    |>.setBool `pp.universes false
    |>.setBool `pp.fullNames true
    |>.setBool `pp.proofs true
    |>.setBool `pp.deepTerms true
    |>.setBool `pp.notation false
    |>.setBool `pp.match false
    |>.setBool `pp.fieldNotation false
    |>.setBool `pp.structureInstances false
    |>.setBool `pp.coercions false
    |>.set `pp.maxSteps (100000000 : Nat)
    |>.set `pp.width (100 : Nat)

/- Inline constants whose private internal names cannot be written as Lean
   source.  The stack check prevents recursive private definitions from
   looping. -/
private partial def inlinePrivate (env : Environment) (e : Expr)
    (stack : List Name := []) : StateM Nat Expr := do
  match e with
  | .app .. =>
    match e.getAppFn with
    | .const name levels =>
      if isPrivateName name && !stack.contains name then
        if let some info := env.find? name then
          if let some value := info.value? (allowOpaque := true) then
            modify (· + 1)
            let value := value.instantiateLevelParams info.levelParams levels
            return ← inlinePrivate env (value.beta e.getAppArgs) (name :: stack)
      return .app (← inlinePrivate env e.appFn! stack)
        (← inlinePrivate env e.appArg! stack)
    | _ =>
      return .app (← inlinePrivate env e.appFn! stack)
        (← inlinePrivate env e.appArg! stack)
  | .const name levels =>
    if isPrivateName name && !stack.contains name then
      if let some info := env.find? name then
        if let some value := info.value? (allowOpaque := true) then
          modify (· + 1)
          let value := value.instantiateLevelParams info.levelParams levels
          return ← inlinePrivate env value (name :: stack)
    return e
  | .lam name type body binderInfo =>
    return .lam name (← inlinePrivate env type stack)
      (← inlinePrivate env body stack) binderInfo
  | .forallE name type body binderInfo =>
    return .forallE name (← inlinePrivate env type stack)
      (← inlinePrivate env body stack) binderInfo
  | .letE name type value body nondep =>
    return .letE name (← inlinePrivate env type stack)
      (← inlinePrivate env value stack) (← inlinePrivate env body stack) nondep
  | .mdata data body =>
    return .mdata data (← inlinePrivate env body stack)
  | .proj typeName index body =>
    return .proj typeName index (← inlinePrivate env body stack)
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. => return e

private def exprChildren : Expr → Array Expr
  | .app fn arg => #[fn, arg]
  | .lam _ type body _ => #[type, body]
  | .forallE _ type body _ => #[type, body]
  | .letE _ type value body _ => #[type, value, body]
  | .mdata _ body => #[body]
  | .proj _ _ body => #[body]
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => #[]

private structure RepeatGraph where
  references : ExprStructMap Nat := {}
  visited : ExprStructMap Unit := {}
  nodes : Array Expr := #[]

private partial def collectRepeatGraph (e : Expr) : StateM RepeatGraph Unit := do
  let key : ExprStructEq := ⟨e⟩
  if (← get).visited.contains key then
    return
  modify fun state =>
    { state with visited := state.visited.insert key (), nodes := state.nodes.push e }
  for child in exprChildren e do
    let childKey : ExprStructEq := ⟨child⟩
    modify fun state =>
      let references := state.references.alter childKey fun count? =>
        some (count?.getD 0 + 1)
      { state with references }
    collectRepeatGraph child

private partial def exprTreeSize (e : Expr) : StateM (ExprStructMap Nat) Nat := do
  let key : ExprStructEq := ⟨e⟩
  if let some size := (← get)[key]? then
    return size
  let mut size := 1
  for child in exprChildren e do
    size := size + (← exprTreeSize child)
  modify (·.insert key size)
  return size

private structure ShareCandidate where
  expr : Expr
  references : Nat
  size : Nat

private def ShareCandidate.estimatedSavings (candidate : ShareCandidate) : Nat :=
  (candidate.references - 1) * (candidate.size - 1)

private def replaceShared (replacements : ExprStructMap Expr) (e : Expr) : Expr :=
  e.replace fun current =>
    let key : ExprStructEq := ⟨current⟩
    replacements[key]?

private structure SharingResult where
  body : Expr
  bindingCount : Nat
  haveCount : Nat
  prunedCount : Nat
  unsharedBytes : Nat := 0
  sharedBytes : Nat := 0

private def sharedBinderName (expr : Expr) (index : Nat)
    (isProof isType : Bool) : Name :=
  let base :=
    match expr.getAppFn with
    | .const name _ => name.getString!
    | .fvar .. => "local"
    | _ => "term"
  let stem :=
    if isProof then s!"h_{base}"
    else if isType then s!"{base}_type"
    else base
  Name.mkSimple s!"{stem}_{index}"

private def profitableBinding (candidate : ShareCandidate) (name : Name)
    (value : Expr) : MetaM Bool := do
  let valueBytes := (toString (← Meta.ppExpr value)).utf8ByteSize
  let nameBytes := name.toString.utf8ByteSize
  let savedBytes := (candidate.references - 1) * valueBytes
  let referenceBytes := candidate.references * nameBytes
  return savedBytes > referenceBytes + 16

private partial def sinkBinding (fvar body : Expr) : MetaM Expr := do
  let fvarId := fvar.fvarId!
  unless body.containsFVar fvarId do
    return body
  let wrap (body : Expr) :=
    mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) #[fvar] body
  match body with
  | .app fn arg =>
    let fnUses := fn.containsFVar fvarId
    let argUses := arg.containsFVar fvarId
    if fnUses && !argUses then
      wrap body
    else if argUses && !fnUses then
      return body.updateApp! fn (← sinkBinding fvar arg)
    else
      wrap body
  | .lam name type nestedBody binderInfo =>
    let typeUses := type.containsFVar fvarId
    let bodyUses := nestedBody.containsFVar fvarId
    if typeUses && !bodyUses then
      return body.updateLambdaE! (← sinkBinding fvar type) nestedBody
    else if bodyUses && !typeUses then
      withLocalDecl name binderInfo type fun opened => do
        let openedBody := nestedBody.instantiate1 opened
        mkLambdaFVars #[opened] (← sinkBinding fvar openedBody)
    else
      wrap body
  | .forallE name type nestedBody binderInfo =>
    let typeUses := type.containsFVar fvarId
    let bodyUses := nestedBody.containsFVar fvarId
    if typeUses && !bodyUses then
      return body.updateForallE! (← sinkBinding fvar type) nestedBody
    else if bodyUses && !typeUses then
      withLocalDecl name binderInfo type fun opened => do
        let openedBody := nestedBody.instantiate1 opened
        mkForallFVars #[opened] (← sinkBinding fvar openedBody)
    else
      wrap body
  | .letE name type value nestedBody nondep =>
    let typeUses := type.containsFVar fvarId
    let valueUses := value.containsFVar fvarId
    let bodyUses := nestedBody.containsFVar fvarId
    let usedChildren := (if typeUses then 1 else 0) + (if valueUses then 1 else 0) +
      (if bodyUses then 1 else 0)
    if usedChildren != 1 then
      wrap body
    else if typeUses then
      return body.updateLetE! (← sinkBinding fvar type) value nestedBody
    else if valueUses then
      return body.updateLetE! type (← sinkBinding fvar value) nestedBody
    else
      withLetDecl name type value (nondep := nondep) fun opened => do
        let openedBody := nestedBody.instantiate1 opened
        mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) #[opened]
          (← sinkBinding fvar openedBody)
  | .mdata _ nestedBody =>
    return body.updateMData! (← sinkBinding fvar nestedBody)
  | .proj _ _ nestedBody =>
    return body.updateProj! (← sinkBinding fvar nestedBody)
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. =>
    wrap body

private partial def introduceSharedBindings (candidates : Array ShareCandidate) (index : Nat)
    (replacements : ExprStructMap Expr) (fvars : Array Expr) (body : Expr) :
    MetaM SharingResult := do
  if h : index < candidates.size then
    let candidate := candidates[index]
    let value := replaceShared replacements candidate.expr
    let type ← inferType value
    let isProof ← isProp type
    let isType := (← whnf type).isSort
    let name := sharedBinderName candidate.expr index isProof isType
    if ← profitableBinding candidate name value then
      withLetDecl name type value (nondep := isProof) fun fvar =>
        introduceSharedBindings candidates (index + 1)
          (replacements.insert ⟨candidate.expr⟩ fvar) (fvars.push fvar) body
    else
      let result ← introduceSharedBindings candidates (index + 1) replacements fvars body
      return { result with prunedCount := result.prunedCount + 1 }
  else
    let mut result := replaceShared replacements body
    for fvar in fvars.reverse do
      result ← sinkBinding fvar result
    let mut haveCount := 0
    for fvar in fvars do
      let decl ← fvar.fvarId!.getDecl
      if ← isProp decl.type then
        haveCount := haveCount + 1
    return { body := result, bindingCount := fvars.size, haveCount, prunedCount := 0 }

private def shareRepeatedSubterms (body : Expr) (minSize : Nat := 12)
    (maxBindings : Nat := 512) : MetaM SharingResult := do
  let initial : RepeatGraph :=
    { references := ({} : ExprStructMap Nat).insert ⟨body⟩ 1 }
  let (_, graph) := (collectRepeatGraph body).run initial
  let (_, sizes) := (exprTreeSize body).run ({} : ExprStructMap Nat)
  let mut candidates := #[]
  for expr in graph.nodes do
    let key : ExprStructEq := ⟨expr⟩
    let references := graph.references[key]?.getD 0
    let size := sizes[key]?.getD 0
    if references > 1 && size ≥ minSize && !expr.hasLooseBVars && expr.isApp then
      candidates := candidates.push { expr, references, size }
  candidates := candidates.qsort fun lhs rhs =>
    lhs.estimatedSavings > rhs.estimatedSavings
  candidates := candidates.extract 0 (min candidates.size maxBindings)
  candidates := candidates.qsort fun lhs rhs => lhs.size < rhs.size
  introduceSharedBindings candidates 0 {} #[] body

private def renderBody (value : Expr) (binderNames : Array Name)
    (opts : Lean.Options) : MetaM (String × String × SharingResult) := do
  Meta.lambdaTelescope value fun fvars body => do
    unless fvars.size = binderNames.size do
      throwError "expected {binderNames.size} binders, found {fvars.size}"
    let mut lctx ← getLCtx
    for fvar in fvars, binderName in binderNames do
      lctx := lctx.setUserName fvar.fvarId! binderName
    Meta.withLCtx lctx (← getLocalInstances) do
      withOptions (fun _ => opts) do
        let typeText := toString (← Meta.ppExpr (← inferType body))
        let unsharedText := toString (← Meta.ppExpr body)
        let shared ← shareRepeatedSubterms body
        let sharedText := toString (← Meta.ppExpr shared.body)
        pure (typeText, sharedText, {
          shared with
            unsharedBytes := unsharedText.utf8ByteSize
            sharedBytes := sharedText.utf8ByteSize
        })

private def renderExpr (value type : Expr) (opts : Lean.Options) : MetaM (String × String × SharingResult) := do
  withOptions (fun _ => opts) do
    let unsharedText := toString (← Meta.ppExpr value)
    let shared ← shareRepeatedSubterms value
    let sharedText := toString (← Meta.ppExpr shared.body)
    let typeText := toString (← Meta.ppExpr type)
    pure (typeText, sharedText, {
        shared with
        body := shared.body
        unsharedBytes := unsharedText.utf8ByteSize
        sharedBytes := sharedText.utf8ByteSize
    })

private def withSourceNames (value type : Expr) (binderNames : Array Name)
    (opts : Lean.Options) : MetaM (String × String × SharingResult) := do
  if binderNames.isEmpty then
    renderExpr value type opts
  else
    renderBody value binderNames opts

private partial def validateSourceExpr (env : Environment) (e : Expr) : MetaM Unit := do
  if e.hasMVar then
    throwError "proof exporter rejected an expression containing metavariables"
  if e.hasSyntheticSorry then
    throwError "proof exporter rejected an expression containing synthetic `sorry`"
  match e with
  | .const name _ =>
      if isPrivateName name then
        throwError "proof exporter could not inline private constant '{name}'"
  | .fvar fvarId =>
      match (← getLCtx).find? fvarId with
      | some decl =>
          if decl.userName.isInaccessibleUserName || decl.userName.hasMacroScopes then
            throwError "proof exporter cannot render inaccessible local '{decl.userName}'"
      | none =>
          throwError "proof exporter encountered a free variable outside the local context"
  | .app fn arg =>
      validateSourceExpr env fn
      validateSourceExpr env arg
  | .lam _ type body _ | .forallE _ type body _ =>
      validateSourceExpr env type
      validateSourceExpr env body
  | .letE _ type value body _ =>
      validateSourceExpr env type
      validateSourceExpr env value
      validateSourceExpr env body
  | .mdata _ body | .proj _ _ body =>
      validateSourceExpr env body
  | .mvar _ =>
      throwError "proof exporter rejected an expression containing metavariables"
  | .bvar .. | .sort .. | .lit .. => pure ()

/-- Render an arbitrary expression and its inferred or supplied type as source.

The expression is first instantiated and private constants are inlined.  The
source namespace is installed while pretty-printing so declarations resolve as
they did at the replacement site.  When `binderNames` is supplied, the
expression is treated as a theorem value and its lambda body is rendered using
those source names; this is the compatibility path used by the proof-term
experiment. -/
meta def render (value : Expr) (type? : Option Expr := none)
    (config : ProofExport.Options := {}) : MetaM Rendered := do
  let env ← getEnv
  let value ← instantiateMVars value
  let (value, valuePrivateConstantsInlined) := (inlinePrivate env value).run 0
  let inferredType ← inferType value
  let (inferredType, inferredTypePrivateConstantsInlined) :=
    (inlinePrivate env inferredType).run 0
  let (type, typePrivateConstantsInlined) ← match type? with
    | some suppliedType => do
        let suppliedType ← instantiateMVars suppliedType
        let (suppliedType, suppliedPrivateConstantsInlined) :=
          (inlinePrivate env suppliedType).run 0
        unless ← isDefEq inferredType suppliedType do
          throwError "proof exporter supplied type is not definitionally equal to the expression's inferred type"
        pure (suppliedType, suppliedPrivateConstantsInlined)
    | none => pure (inferredType, inferredTypePrivateConstantsInlined)
  validateSourceExpr env value
  validateSourceExpr env type
  let baseOptions ← getOptions
  let opts := namedBodyOptions baseOptions
  let result ← withTheReader Core.Context (fun context =>
      { context with currNamespace := config.sourceNamespace }) do
    withSourceNames value type config.binderNames opts
  let (typeText, valueText, sharing) := result
  return {
    typeText
    valueText
    metrics := {
      privateConstantsInlined := valuePrivateConstantsInlined + typePrivateConstantsInlined
      bindingCount := sharing.bindingCount
      haveCount := sharing.haveCount
      prunedCount := sharing.prunedCount
      unsharedBytes := sharing.unsharedBytes
      sharedBytes := valueText.utf8ByteSize
    }
  }

end ProofExport

end ExplicitLean
