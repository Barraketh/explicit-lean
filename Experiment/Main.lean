import Mathlib.SetTheory.Cardinal.NatCount
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Data.List.Range
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.Divisors

open Lean Elab Command Meta

/-- Settings for a body inserted under a statement in which every theorem
parameter has been given a source-level name. This prints instance arguments
instead of replacing them with `_`. Universe arguments remain implicit because
theorem bodies cannot refer to universe parameters as terms. -/
private def namedBodyOptions (opts : Options) : Options :=
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

/-- Inline constants whose private internal names cannot be written as Lean
source. The stack check prevents recursive private definitions from looping. -/
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

/-- Immediate children of an expression. Keeping this traversal explicit lets
the sharing pass count edges in Lean's expression DAG rather than expanded tree
occurrences. -/
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

/-- Record each structurally distinct node once, while counting how many DAG
edges point to it. A repeated parent contributes only one set of child edges;
this prevents redundant lets for children used solely by that parent. -/
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

/-- Expanded syntax-tree size, memoized by structural expression identity. -/
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

/-- Produce a stable local name from the defining constant. The numeric suffix
keeps names unique without requiring a global name-allocation pass. -/
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

/-- Keep a binding only when its value remains large enough after previously
selected children have been replaced by names. This is a rendered-size cost
model: the saved repeated values must pay for the binding syntax and its uses. -/
private def profitableBinding (candidate : ShareCandidate) (name : Name)
    (value : Expr) : MetaM Bool := do
  let valueBytes := (toString (← Meta.ppExpr value)).utf8ByteSize
  let nameBytes := name.toString.utf8ByteSize
  let savedBytes := (candidate.references - 1) * valueBytes
  let referenceBytes := candidate.references * nameBytes
  return savedBytes > referenceBytes + 16

/-- Insert a local binding at the smallest expression node containing all uses
of its free variable. Descending through a single used child keeps unrelated
parts of the proof outside the binding's scope. Binders are opened before
descending into their bodies so rebuilding them preserves de Bruijn indices. -/
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
      -- With explicit arguments enabled, a binding in function position prints
      -- as the invalid source form `@(let ... )`. The whole application is the
      -- narrowest source-printable scope in this case.
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

/-- Introduce profitable candidates in dependency order. The locals remain open
until the final body is rewritten; they are then closed in reverse order and
sunk to their lowest common-use scopes. -/
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

/-- Share repeated application subterms as local bindings. Candidates must be
closed with respect to nested binders, large enough to offset binding syntax,
and among the most profitable 512 nodes when a term contains more candidates. -/
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

/-- Pretty-print an open proof body after assigning the supplied source names
to its theorem parameters. -/
private structure RenderedBodies where
  unsharedText : String
  sharedText : String
  bindingCount : Nat
  haveCount : Nat
  prunedCount : Nat

private def renderNamedBodies (value : Expr) (binderNames : Array Name)
    (opts : Options) : MetaM RenderedBodies := do
  Meta.lambdaTelescope value fun fvars body => do
    unless fvars.size = binderNames.size do
      throwError "expected {binderNames.size} binders, found {fvars.size}"
    let mut lctx ← getLCtx
    for fvar in fvars, binderName in binderNames do
      lctx := lctx.setUserName fvar.fvarId! binderName
    Meta.withLCtx lctx (← getLocalInstances) do
      withOptions (fun _ => opts) do
        let unsharedText := toString (← Meta.ppExpr body)
        let shared ← shareRepeatedSubterms body
        let sharedText := toString (← Meta.ppExpr shared.body)
        pure {
          unsharedText, sharedText
          bindingCount := shared.bindingCount
          haveCount := shared.haveCount
          prunedCount := shared.prunedCount
        }

/-- Export one completed theorem type and proof body as Lean source. The source
namespace is supplied to the pretty-printer so root declarations are qualified
when the target namespace contains a shadowing declaration. -/
private def exportTheorem (name : Name) (binderNames : Array Name)
    (sourceNamespace : Name := name.getPrefix) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? name
    | throwError "unknown declaration '{name}'"
  let some value := info.value? (allowOpaque := true)
    | throwError "declaration '{name}' has no accessible value"
  let (value, privateConstantsInlined) := (inlinePrivate env value).run 0
  let baseOptions ← getOptions
  let rendered ← liftTermElabM do
    withTheReader Core.Context (fun context => { context with currNamespace := sourceNamespace }) do
      renderNamedBodies value binderNames (namedBodyOptions baseOptions)
  let dir : System.FilePath := ".lake" / "proof-term-probe"
  IO.FS.createDirAll dir
  let stem := name.toString.replace "." "_"
  IO.FS.writeFile (dir / s!"{stem}.shared-body.lean") (rendered.sharedText ++ "\n")
  let statsText :=
    s!"private constants inlined: {privateConstantsInlined}\n" ++
    s!"shared bindings: {rendered.bindingCount}\n" ++
    s!"proof haves: {rendered.haveCount}\n" ++
    s!"value lets: {rendered.bindingCount - rendered.haveCount}\n" ++
    s!"pruned candidates: {rendered.prunedCount}\n" ++
    s!"unshared body bytes: {rendered.unsharedText.utf8ByteSize}\n" ++
    s!"shared body bytes: {rendered.sharedText.utf8ByteSize}\n"
  IO.FS.writeFile (dir / s!"{stem}.stats") statsText

run_cmd exportTheorem `Nat.count_le_setENCard #[`p, `decidablePredP, `n]
run_cmd exportTheorem `Nat.count_le_cardinal #[`p, `decidablePredP, `n]
run_cmd exportTheorem `Nat.count_le_setNCard #[`p, `decidablePredP, `n, `h]
run_cmd exportTheorem `DualNumber.commute_eps_left #[`R, `semiringR, `x]
run_cmd exportTheorem `DualNumber.commute_eps_right #[`R, `semiringR, `x]
run_cmd exportTheorem `DualNumber.ringHom_ext #[`R, `commSemiringR, `R', `commSemiringR', `f, `g, `h₀, `hε]
run_cmd exportTheorem `DualNumber.range_lift #[`R, `B, `A, `commSemiringR, `semiringA, `semiringB, `algebraRA, `algebraRB, `fe]
run_cmd exportTheorem `GenContFract.first_num_eq #[`K, `g, `divisionRingK, `gp, `zeroth_s_eq]
run_cmd exportTheorem `GenContFract.terminatedAt_iff_s_terminatedAt #[`α, `g, `n]
run_cmd exportTheorem `GenContFract.partNum_none_iff_s_none #[`α, `g, `n]
run_cmd exportTheorem `List.isChain_range #[`r, `n]
run_cmd exportTheorem `List.ranges_disjoint #[`l]
run_cmd exportTheorem `TopologicalSpace.ext_iff #[`X, `t, `t'] Name.anonymous
run_cmd exportTheorem `IsOpen.union #[`X, `s₁, `s₂, `topologicalSpaceX, `h₁, `h₂] Name.anonymous
run_cmd exportTheorem `isOpen_iff_of_cover #[`X, `α, `s, `topologicalSpaceX, `f, `ho, `hU] Name.anonymous
run_cmd exportTheorem `Set.Finite.isOpen_sInter #[`X, `topologicalSpaceX, `s, `hs, `h] Name.anonymous
run_cmd exportTheorem `Nat.divisor_le #[`n, `m]
run_cmd exportTheorem `Nat.card_divisors_le_self #[`n]
run_cmd exportTheorem `Nat.divisors_subset_of_dvd #[`n, `m, `hzero, `h]

def main : IO Unit := pure ()
