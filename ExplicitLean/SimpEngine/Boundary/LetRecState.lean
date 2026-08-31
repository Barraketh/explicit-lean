module
prelude

public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Syntax

public meta section

open Lean Elab

namespace ExplicitLean.SimpEngine.Boundary

private def optionalEq (eq : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | some a, some b => eq a b
  | _, _ => false

private def terminationByEq (a b : TerminationBy) : Bool :=
  a.ref.eqWithInfo b.ref && a.structural == b.structural &&
  a.vars.isEqv b.vars (fun x y => x.raw.eqWithInfo y.raw) &&
  a.body.raw.eqWithInfo b.body.raw && a.synthetic == b.synthetic

private def partialFixpointTypeEq : PartialFixpointType → PartialFixpointType → Bool
  | .partialFixpoint, .partialFixpoint
  | .coinductiveFixpoint, .coinductiveFixpoint
  | .inductiveFixpoint, .inductiveFixpoint => true
  | _, _ => false

private def partialFixpointEq (a b : PartialFixpoint) : Bool :=
  a.ref.eqWithInfo b.ref &&
  optionalEq (fun x y => x.raw.eqWithInfo y.raw) a.term? b.term? &&
  partialFixpointTypeEq a.fixpointType b.fixpointType

private def decreasingByEq (a b : DecreasingBy) : Bool :=
  a.ref.eqWithInfo b.ref && a.tactic.raw.eqWithInfo b.tactic.raw

private def terminationHintsEq (a b : TerminationHints) : Bool :=
  a.ref.eqWithInfo b.ref && optionalEq Syntax.eqWithInfo a.terminationBy?? b.terminationBy?? &&
  optionalEq terminationByEq a.terminationBy? b.terminationBy? &&
  optionalEq partialFixpointEq a.partialFixpoint? b.partialFixpoint? &&
  optionalEq decreasingByEq a.decreasingBy? b.decreasingBy? &&
  a.extraParams == b.extraParams

private def attributeEq (a b : Attribute) : Bool :=
  a.kind == b.kind && a.name == b.name && a.stx.eqWithInfo b.stx

private def localDeclEq : LocalDecl → LocalDecl → Bool
  | .cdecl ai af an aty ab ak, .cdecl bi bf bn bty bb bk =>
      ai == bi && af == bf && an == bn && aty.equal bty && ab == bb && ak == bk
  | .ldecl ai af an aty av ad ak, .ldecl bi bf bn bty bv bd bk =>
      ai == bi && af == bf && an == bn && aty.equal bty && av.equal bv && ad == bd && ak == bk
  | _, _ => false

private def localContextEq (a b : LocalContext) : Bool :=
  a.decls.toArray.isEqv b.decls.toArray (optionalEq localDeclEq) &&
  a.fvarIdToDecl.toList.isEqv b.fvarIdToDecl.toList
    (fun x y => x.1 == y.1 && localDeclEq x.2 y.2) &&
  a.auxDeclToFullName.toList == b.auxDeclToFullName.toList

/-- Exact comparison of an entry retained from the common pre-state. This is
    deliberately not an alpha-renaming comparison for new lifted recursion.
    Raw expression IDs are retained; their assignments remain subject to the
    independent complete metavariable-state comparator. Syntax source info,
    binder annotations, local-context holes/maps, and instance classes count. -/
def boundaryExistingLetRecEq (a b : Term.LetRecToLift) : Bool :=
  a.ref.eqWithInfo b.ref && a.fvarId == b.fvarId &&
  a.attrs.isEqv b.attrs attributeEq &&
  a.shortDeclName == b.shortDeclName && a.declName == b.declName &&
  a.parentName? == b.parentName? && localContextEq a.lctx b.lctx &&
  a.localInstances.isEqv b.localInstances
    (fun x y => x.className == y.className && x.fvar.equal y.fvar) &&
  a.type.equal b.type && a.val.equal b.val && a.mvarId == b.mvarId &&
  terminationHintsEq a.termination b.termination &&
  a.binders.eqWithInfo b.binders &&
  optionalEq (fun x y => x.1.raw.eqWithInfo y.1.raw && x.2 == y.2) a.docString? b.docString?

/-- Existing pending recursion is unchanged by supported replay. New, removed,
    reordered, or modified entries are unsupported; no lifting/generator runs. -/
def boundaryExistingLetRecsEq (before after : List Term.LetRecToLift) : Bool :=
  before.isEqv after boundaryExistingLetRecEq

end ExplicitLean.SimpEngine.Boundary
