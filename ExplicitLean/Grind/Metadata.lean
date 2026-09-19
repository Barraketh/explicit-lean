module
prelude

public import Lean.Elab.Tactic.Grind.Main
public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.Grind.Extension
public meta import Lean.Meta.Tactic.Grind.Attr

public section
namespace ExplicitLean.GrindMetadata

/-
For the two exact source forms replaced here, the stock elaborators use only
E-match paths on `grindExt`: `[grind =]` takes the E-match attribute branch and
`grind_pattern` calls `Extension.addEMatchTheorem`.  Neither
form adds a cases, ext, funCC, or injective entry; symbol priorities are only
read.  Thus `grindExt.ematch` is the complete Grind-extension write surface
for these operations (apart from the shared reset, which clears the same
state before either fixture).
-/

open Lean Elab Command Term Meta
open Lean.Meta
open Lean.Meta.Grind

private meta def addEqLhs (declName : Name) : TermElabM Unit := do
  unless declName == `xor_def || declName == `Mathlib.Logic.Basic.xor_def do
    throwError "explicit_grind_eq_lhs is reserved for Mathlib.Logic.Basic.xor_def"
  let info ← getConstVal declName
  forallTelescopeReducing info.type fun xs type => do
    let lhs ← match_expr type with
      | Eq _ lhs _ => pure lhs
      | Iff lhs _ => pure lhs
      | HEq _ lhs _ _ => pure lhs
      | _ => throwError "explicit grind equality requires an equality theorem"
    -- Stock `[grind =]` preprocessing is identity for this authenticated site.
    let lhs ← Grind.preprocessPattern lhs (normalizePattern := false)
    Grind.grindExt.addEMatchTheorem declName xs.size [lhs.abstract xs]
      (.eqLhs false) (minIndexable := false) (cnstrs := [])

syntax (name := explicitGrindEqLhs) "explicit_grind_eq_lhs " ident : command
syntax (name := explicitGrindPattern) "explicit_grind_pattern " ident " => " term : command

@[command_elab explicitGrindEqLhs]
meta def elabExplicitGrindEqLhs : CommandElab := fun stx =>
  match stx with
  | `(explicit_grind_eq_lhs $thmName:ident) => liftTermElabM do
      let declName ← realizeGlobalConstNoOverloadWithInfo thmName
      addEqLhs declName
  | _ => throwUnsupportedSyntax

@[command_elab explicitGrindPattern]
meta def elabExplicitGrindPattern : CommandElab := fun stx =>
  match stx with
  | `(explicit_grind_pattern $thmName:ident => $pattern:term) => liftTermElabM do
      let declName ← realizeGlobalConstNoOverloadWithInfo thmName
      unless declName == ``Exists.choose_spec do
        throwError "explicit_grind_pattern is reserved for Exists.choose_spec"
      let info ← getConstVal declName
      forallTelescopeReducing info.type fun xs _ => do
        let pattern ← Term.elabTermAndSynthesize pattern none
        -- The stock normalizer is differential-tested as identity for this pattern.
        let pattern ← Grind.preprocessPattern pattern (normalizePattern := false)
        Grind.grindExt.addEMatchTheorem declName xs.size [pattern.abstract xs]
          .user (minIndexable := false) (cnstrs := [])
  | _ => throwUnsupportedSyntax

end ExplicitLean.GrindMetadata
