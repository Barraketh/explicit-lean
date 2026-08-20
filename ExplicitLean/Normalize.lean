module

public import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Tactic.Refl
public meta import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Tactic.Rewrite

public section

open Lean Meta Elab Tactic

namespace ExplicitLean

private meta def dottedName (text : String) : Name :=
  text.splitOn "." |>.foldl (fun name part ↦ .str name part) .anonymous

private meta def normalizerNames (texts : List String) : Array Name :=
  texts.toArray.map dottedName

private meta def normalizerSyntax (names : Array Name) : MacroM (TSyntax `tactic) := do
  let rules ← names.mapM fun name ↦
    `(Parser.Tactic.simpLemma| $(mkIdent name):term)
  `(tactic| simp only [$[$rules],*])

private meta def normalizerSyntaxUsing (names : Array Name)
    (extras : Array (TSyntax ``Parser.Tactic.simpLemma)) : MacroM (TSyntax `tactic) := do
  let rules ← names.mapM fun name ↦
    `(Parser.Tactic.simpLemma| $(mkIdent name):term)
  `(tactic| simp only [$[$extras],*, $[$rules],*])

private meta def categoryCompName : Name :=
  dottedName "CategoryTheory.CategoryStruct.comp"

private meta def categoryIdName : Name :=
  dottedName "CategoryTheory.CategoryStruct.id"

private meta def categoryAssocName : Name :=
  dottedName "CategoryTheory.Category.assoc"

private meta def categoryIdCompName : Name :=
  dottedName "CategoryTheory.Category.id_comp"

private meta def categoryCompIdName : Name :=
  dottedName "CategoryTheory.Category.comp_id"

/-- The compatibility `using` form still needs the category laws in the same
simplifier fixed point as caller-supplied exposure rules. The bare normalizer
below does not use this catalog. -/
private meta def categoryExposureRules : Array Name := normalizerNames [
  "CategoryTheory.Category.assoc",
  "CategoryTheory.Category.id_comp",
  "CategoryTheory.Category.comp_id"]

namespace Normalize

/-- The output of a proof-producing target normalizer. `proof` has type
`original = expr`. -/
structure Result where
  expr : Expr
  proof : Expr

end Normalize

private abbrev CategoryNormResult := Normalize.Result

private meta def unchangedCategoryResult (expr : Expr) : MetaM CategoryNormResult := do
  return { expr, proof := ← mkEqRefl expr }

private meta def categoryComp? (expr : Expr) : Option (Expr × Expr) := do
  let expr := expr.consumeMData
  guard <| expr.getAppFn.constName? == some categoryCompName
  let args := expr.getAppArgs
  guard <| args.size >= 2
  return (args[args.size - 2]!, args[args.size - 1]!)

private meta def isCategoryId (expr : Expr) : Bool :=
  expr.consumeMData.getAppFn.constName? == some categoryIdName

private meta def mkCategoryComp (left right : Expr) : MetaM Expr :=
  mkAppM categoryCompName #[left, right]

private meta def congrCategoryLeft (proof right : Expr) : MetaM Expr := do
  let some (type, _, _) := (← inferType proof).eq?
    | throwError "category normalizer produced a non-equality certificate"
  withLocalDeclD `left type fun left => do
    let body ← mkCategoryComp left right
    mkCongrArg (← mkLambdaFVars #[left] body) proof

private meta def congrCategoryRight (left proof : Expr) : MetaM Expr := do
  let some (type, _, _) := (← inferType proof).eq?
    | throwError "category normalizer produced a non-equality certificate"
  withLocalDeclD `right type fun right => do
    let body ← mkCategoryComp left right
    mkCongrArg (← mkLambdaFVars #[right] body) proof

/-- Compose two already-normal category chains. The left chain determines the
recursion: peel its first atom, reassociate once, and normalize the remaining
suffix. Consequently the output is right-associated without a rewrite search. -/
private meta partial def appendCategoryNFs
    (left right : Expr) : MetaM CategoryNormResult := do
  let input ← mkCategoryComp left right
  if isCategoryId left then
    return {
      expr := right
      proof := ← mkAppM categoryIdCompName #[right]
    }
  if isCategoryId right then
    return {
      expr := left
      proof := ← mkAppM categoryCompIdName #[left]
    }
  let some (head, tail) := categoryComp? left
    | return ← unchangedCategoryResult input
  let suffix ← appendCategoryNFs tail right
  let assocProof ← mkAppM categoryAssocName #[head, tail, right]
  let suffixProof ← congrCategoryRight head suffix.proof
  return {
    expr := ← mkCategoryComp head suffix.expr
    proof := ← mkEqTrans assocProof suffixProof
  }

/-- Normalize one categorical expression. All non-composition, non-identity
expressions are opaque atoms. -/
private meta partial def normalizeCategoryExpr
    (expr : Expr) : MetaM CategoryNormResult := do
  let expr := expr.consumeMData
  let some (left, right) := categoryComp? expr
    | return ← unchangedCategoryResult expr
  let leftResult ← normalizeCategoryExpr left
  let rightResult ← normalizeCategoryExpr right
  let leftProof ← congrCategoryLeft leftResult.proof right
  let rightProof ← congrCategoryRight leftResult.expr rightResult.proof
  let childrenProof ← mkEqTrans leftProof rightProof
  let appended ← appendCategoryNFs leftResult.expr rightResult.expr
  return {
    expr := appended.expr
    proof := ← mkEqTrans childrenProof appended.proof
  }

/-- Find the first outermost categorical composition that is not in normal
form. Application arguments are visited from left to right, giving traversal a
fixed order independent of the simp set. -/
private meta partial def findCategoryReduction?
    (expr : Expr) : MetaM (Option CategoryNormResult) := do
  let expr := expr.consumeMData
  if (categoryComp? expr).isSome then
    let result ← normalizeCategoryExpr expr
    unless Expr.equal expr result.expr do
      return some result
  for arg in expr.getAppArgs do
    if let some result ← findCategoryReduction? arg then
      return some result
  return none

private meta partial def normalizeCategoryTargetAux
    (goal : MVarId) (target : Expr) : MetaM Normalize.Result := do
  goal.withContext do
    match ← findCategoryReduction? target with
    | some result =>
        -- `rewrite` is used only to transport the target along the fully
        -- instantiated equality certificate computed above. It performs no
        -- theorem lookup and has no category rules to select or orient.
        let rewriteResult ← goal.rewrite target result.proof
        unless rewriteResult.mvarIds.isEmpty do
          throwError "category normalization unexpectedly created side goals"
        let rest ← normalizeCategoryTargetAux goal rewriteResult.eNew
        return {
          expr := rest.expr
          proof := ← mkEqTrans rewriteResult.eqProof rest.proof
        }
    | none => unchangedCategoryResult target

namespace Normalize

/-- Normalize every categorical composition visible in `target`. The supplied
goal provides its local context and rewrite elaboration context but is not
assigned. This expression-level API allows normalization to participate in a
larger deterministic certificate program. -/
meta def categoryTarget (goal : MVarId) (target : Expr) : MetaM Result :=
  normalizeCategoryTargetAux goal target

end Normalize

private meta def normalizeCategoryGoal (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let result ← Normalize.categoryTarget goal target
    let goal ← if Expr.equal target result.expr then
      pure goal
    else
      goal.replaceTargetEq result.expr result.proof
    try
      goal.refl
      return []
    catch _ =>
      return [goal]

private meta def projectionRules : Array Name := normalizerNames [
  "Function.comp_apply",
  "Pi.zero_apply",
  "Pi.one_apply",
  "Pi.add_apply",
  "Pi.sub_apply",
  "Pi.mul_apply",
  "Pi.neg_apply",
  "Pi.pow_apply",
  "Pi.smul_apply"]

private meta def listRules : Array Name := normalizerNames [
  "List.nil_append",
  "List.append_nil",
  "List.cons_append",
  "List.append_assoc",
  "List.reverse_nil",
  "List.reverse_cons",
  "List.reverse_append",
  "List.reverse_reverse",
  "List.drop_zero",
  "List.drop_nil",
  "List.drop_succ_cons",
  "List.take_zero",
  "List.take_nil",
  "List.take_succ_cons"]

/-- Normalize categorical composition to right-associated, identity-free form.

The implementation recognizes composition and identity syntax directly,
computes a canonical composition chain, and constructs an equality proof from
associativity and the two identity laws. It does not invoke the simplifier. -/
elab "normalize_category" : tactic => do
  liftMetaTactic normalizeCategoryGoal

syntax "normalize_category" " using " "["
  Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- Compatibility form for representation-changing exposure rules. These
rules and the three category laws run in one closed `simp only` fixed point;
the ambient simp set is still ignored. This is deliberately separate from the
syntax-directed implementation of bare `normalize_category`. -/
macro_rules
  | `(tactic| normalize_category using [$[$rules],*]) =>
      normalizerSyntaxUsing categoryExposureRules rules

/-- Push functor and natural-transformation structure through identities and
compositions. This is separate from `normalize_category` because exposing
functor implementations is not always desirable under semireducible types. -/
macro "normalize_functor" : tactic => normalizerSyntax (normalizerNames [
  "CategoryTheory.Functor.map_id",
  "CategoryTheory.Functor.map_comp",
  "CategoryTheory.Functor.comp_obj",
  "CategoryTheory.Functor.comp_map",
  "CategoryTheory.NatTrans.comp_app",
  "CategoryTheory.NatTrans.id_app"])

/-- Normalize the structural maps of category isomorphisms. -/
macro "normalize_iso" : tactic => normalizerSyntax (normalizerNames [
  "CategoryTheory.Iso.trans_hom",
  "CategoryTheory.Iso.trans_inv",
  "CategoryTheory.Iso.symm_hom",
  "CategoryTheory.Iso.symm_inv",
  "CategoryTheory.Iso.refl_hom",
  "CategoryTheory.Iso.refl_inv",
  "CategoryTheory.Iso.hom_inv_id",
  "CategoryTheory.Iso.inv_hom_id",
  "CategoryTheory.Iso.hom_inv_id_assoc",
  "CategoryTheory.Iso.inv_hom_id_assoc",
  "CategoryTheory.Iso.hom_inv_id_app",
  "CategoryTheory.Iso.inv_hom_id_app",
  "CategoryTheory.Iso.hom_inv_id_app_assoc",
  "CategoryTheory.Iso.inv_hom_id_app_assoc"])

/-- Normalize equivalence application by eliminating compositions, reflexive
equivalences, double inverses, and inverse/application pairs. -/
macro "normalize_equiv" : tactic => normalizerSyntax (normalizerNames [
  "Equiv.trans_apply",
  "Equiv.symm_trans_apply",
  "Equiv.symm_symm",
  "Equiv.refl_apply",
  "Equiv.apply_symm_apply",
  "Equiv.symm_apply_apply"])

/-- Normalize elementary monoid, additive-monoid, negation, subtraction, and
scalar-action structure. This is intentionally only structural cleanup; it is
not a commutative-ring decision procedure. -/
macro "normalize_algebra" : tactic => normalizerSyntax (normalizerNames [
  "add_zero",
  "zero_add",
  "mul_one",
  "one_mul",
  "MulZeroClass.mul_zero",
  "MulZeroClass.zero_mul",
  "sub_zero",
  "sub_self",
  "neg_zero",
  "zero_smul",
  "one_smul"])

/-- Normalize common function and pointwise-structure projections. -/
macro "normalize_projections" : tactic => normalizerSyntax projectionRules

syntax "normalize_projections" " using " "["
  Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| normalize_projections using [$[$rules],*]) =>
      normalizerSyntaxUsing projectionRules rules

/-- Normalize matrix constructors and the entrywise meaning of transpose and
matrix multiplication. -/
macro "normalize_matrix" : tactic => normalizerSyntax (normalizerNames [
  "Matrix.of_apply",
  "Matrix.transpose_apply",
  "Matrix.mul_apply",
  "Matrix.submatrix_apply"])

/-- Normalize natural powers by removing exponents zero and one and pushing
powers through products and sums of exponents. -/
macro "normalize_powers" : tactic => normalizerSyntax (normalizerNames [
  "pow_zero",
  "pow_one",
  "mul_pow",
  "pow_add"])

/-- Normalize list expressions by evaluating constructors and pushing reverse
through append and constructors. Append is right-associated. -/
macro "normalize_list" : tactic => normalizerSyntax listRules

syntax "normalize_list" " using " "["
  Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| normalize_list using [$[$rules],*]) =>
      normalizerSyntaxUsing listRules rules

/-- Normalize complex-coordinate projections and the standard embeddings of
real scalars. Polynomial cleanup is deliberately left to `normalize_algebra`. -/
macro "normalize_complex" : tactic => normalizerSyntax (normalizerNames [
  "Complex.add_re",
  "Complex.add_im",
  "Complex.sub_re",
  "Complex.sub_im",
  "Complex.mul_re",
  "Complex.mul_im",
  "Complex.neg_re",
  "Complex.neg_im",
  "Complex.ofReal_re",
  "Complex.ofReal_im",
  "Complex.ofReal_zero",
  "Complex.ofReal_one",
  "Complex.ofReal_neg",
  "Complex.ofReal_inv",
  "Complex.I_re",
  "Complex.I_im",
  "Complex.norm_I",
  "norm_neg"])

/-- Normalize the coordinate projections introduced by the standard
equivalence between an `RCLike` type and the complex numbers. -/
macro "normalize_rclike" : tactic => normalizerSyntax (normalizerNames [
  "RCLike.complexRingEquiv_apply",
  "RCLike.ofReal_re",
  "RCLike.ofReal_im"])

/-- Normalize inverse notation and push inversion outward through the real
square root and the standard embedding of reals into the complex numbers. -/
macro "normalize_inverses" : tactic => normalizerSyntax (normalizerNames [
  "one_div",
  "inv_inv",
  "inv_one",
  "Real.sqrt_inv",
  "Complex.ofReal_inv"])

end ExplicitLean
