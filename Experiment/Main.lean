import Mathlib.SetTheory.Cardinal.NatCount
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.ContinuedFractions.Translations

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

/-- Introduce selected common subexpressions from smallest to largest, so a
larger shared value can itself refer to already shared children. -/
private partial def introduceSharedLets (candidates : Array ShareCandidate) (index : Nat)
    (replacements : ExprStructMap Expr) (body : Expr) : MetaM Expr := do
  if h : index < candidates.size then
    let candidate := candidates[index]
    let value := replaceShared replacements candidate.expr
    let type ← inferType value
    Meta.mapLetDecl (Name.mkSimple s!"shared_{index}") type value fun shared =>
      introduceSharedLets candidates (index + 1)
        (replacements.insert ⟨candidate.expr⟩ shared) body
  else
    return replaceShared replacements body

private structure SharingResult where
  body : Expr
  letCount : Nat

/-- Share repeated application subterms as `let` bindings. Candidates must be
closed with respect to nested binders, large enough to offset let syntax, and
among the most profitable 512 nodes when a term contains more candidates. -/
private def shareRepeatedSubterms (body : Expr) (minSize : Nat := 12)
    (maxLets : Nat := 512) : MetaM SharingResult := do
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
  candidates := candidates.extract 0 (min candidates.size maxLets)
  candidates := candidates.qsort fun lhs rhs => lhs.size < rhs.size
  let compressed ← introduceSharedLets candidates 0 {} body
  return { body := compressed, letCount := candidates.size }

/-- Pretty-print an open proof body after assigning the supplied source names
to its theorem parameters. -/
private def renderNamedBodies (value : Expr) (binderNames : Array Name)
    (opts : Options) : MetaM (String × String × Nat) := do
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
        pure (unsharedText, sharedText, shared.letCount)

/-- Export one completed theorem type and proof body as Lean source. -/
private def exportTheorem (name : Name) (binderNames : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? name
    | throwError "unknown declaration '{name}'"
  let some value := info.value? (allowOpaque := true)
    | throwError "declaration '{name}' has no accessible value"
  let (value, privateConstantsInlined) := (inlinePrivate env value).run 0
  let baseOptions ← getOptions
  let (unsharedBodyText, sharedBodyText, sharedLetCount) ← liftTermElabM do
    renderNamedBodies value binderNames (namedBodyOptions baseOptions)
  let dir : System.FilePath := ".lake" / "proof-term-probe"
  IO.FS.createDirAll dir
  let stem := name.toString.replace "." "_"
  IO.FS.writeFile (dir / s!"{stem}.shared-body.lean") (sharedBodyText ++ "\n")
  IO.FS.writeFile (dir / s!"{stem}.stats")
    s!"private constants inlined: {privateConstantsInlined}\nshared lets: {sharedLetCount}\nunshared body bytes: {unsharedBodyText.utf8ByteSize}\nshared body bytes: {sharedBodyText.utf8ByteSize}\n"

run_cmd exportTheorem `Nat.count_le_setENCard #[`p, `decidablePredP, `n]
run_cmd exportTheorem `DualNumber.commute_eps_left #[`R, `semiringR, `x]
run_cmd exportTheorem `DualNumber.range_lift #[`R, `B, `A, `commSemiringR, `semiringA, `semiringB, `algebraRA, `algebraRB, `fe]
run_cmd exportTheorem `GenContFract.first_num_eq #[`K, `g, `divisionRingK, `gp, `zeroth_s_eq]

def main : IO Unit := pure ()
