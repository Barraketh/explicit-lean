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

/-- Pretty-print an open proof body after assigning the supplied source names
to its theorem parameters. -/
private def ppNamedBody (value : Expr) (binderNames : Array Name)
    (opts : Options) : MetaM String := do
  Meta.lambdaTelescope value fun fvars body => do
    unless fvars.size = binderNames.size do
      throwError "expected {binderNames.size} binders, found {fvars.size}"
    let mut lctx ← getLCtx
    for fvar in fvars, binderName in binderNames do
      lctx := lctx.setUserName fvar.fvarId! binderName
    Meta.withLCtx lctx (← getLocalInstances) do
      withOptions (fun _ => opts) do
        pure (toString (← Meta.ppExpr body))

/-- Export one completed theorem type and proof body as Lean source. -/
private def exportTheorem (name : Name) (binderNames : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? name
    | throwError "unknown declaration '{name}'"
  let some value := info.value? (allowOpaque := true)
    | throwError "declaration '{name}' has no accessible value"
  let (value, privateConstantsInlined) := (inlinePrivate env value).run 0
  let baseOptions ← getOptions
  let namedBodyText ← liftTermElabM do
    ppNamedBody value binderNames (namedBodyOptions baseOptions)
  let dir : System.FilePath := ".lake" / "proof-term-probe"
  IO.FS.createDirAll dir
  let stem := name.toString.replace "." "_"
  IO.FS.writeFile (dir / s!"{stem}.named-body.lean") (namedBodyText ++ "\n")
  IO.FS.writeFile (dir / s!"{stem}.stats")
    s!"private constants inlined: {privateConstantsInlined}\nnamed body bytes: {namedBodyText.utf8ByteSize}\n"

run_cmd exportTheorem `Nat.count_le_setENCard #[`p, `decidablePredP, `n]
run_cmd exportTheorem `DualNumber.commute_eps_left #[`R, `semiringR, `x]
run_cmd exportTheorem `DualNumber.range_lift #[`R, `B, `A, `commSemiringR, `semiringA, `semiringB, `algebraRA, `algebraRB, `fe]
run_cmd exportTheorem `GenContFract.first_num_eq #[`K, `g, `divisionRingK, `gp, `zeroth_s_eq]

def main : IO Unit := pure ()
