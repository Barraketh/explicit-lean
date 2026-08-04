import ExplicitLean.Capture

/-!
# Stable capture projection

A deterministic textual projection of what capture observed, used by the
coverage probes required by [C10](../CAPTURE.md#c10-coverage-probes-and-acceptance).

This is a debugging and testing artifact, not the manifest: it exists so a probe
can assert that repeated runs observe exactly the same thing, and so that a
fixture shows at a glance which facts capture actually recovered. No stable
compiler artifact is derived from it.

Everything here obeys the C8 stability rules. Pointer identity, metavariable and
free-variable IDs, macro scopes, and map traversal order never appear; names,
spans, ordinals, and sorted orders do.
-/

open Lean

namespace ExplicitLean

/-- Render a name as its dotted components.

Numeric components are rendered as their decimal digits, which is unambiguous
here because the projection is for human inspection and comparison rather than
round-tripping. -/
def projectName (n : Name) : String :=
  String.intercalate "." (n.componentsRev.reverse.map fun c =>
    match c with
    | .str _ s => s
    | .num _ i => toString i
    | .anonymous => "_")

/-- Render the kind of a completed declaration. -/
def projectKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Render an expression's structure without any unstable identity.

Free variables are rendered by their position in the enclosing binder telescope
rather than by `FVarId`, and metavariables are rendered as a marker so that a
projection can show one rather than crash; a metavariable reaching this point is
already a capture failure. -/
partial def projectExpr (e : Expr) : String :=
  go e 0
where
  go (e : Expr) (depth : Nat) : String :=
    match e with
    | .bvar i => s!"#{i}"
    | .fvar _ => "fvar"
    | .mvar _ => "MVAR"
    | .sort u => s!"Sort({projectLevel u})"
    | .const n us =>
      if us.isEmpty then projectName n
      else
        let levels := String.intercalate "," (us.map projectLevel)
        projectName n ++ ".{" ++ levels ++ "}"
    | .app f a => s!"({go f depth} {go a depth})"
    | .lam _ t b _ => s!"(fun : {go t depth} => {go b (depth + 1)})"
    | .forallE _ t b _ => s!"(forall : {go t depth} => {go b (depth + 1)})"
    | .letE _ t v b _ => s!"(let : {go t depth} := {go v depth}; {go b (depth + 1)})"
    | .lit (.natVal n) => s!"nat_lit {n}"
    | .lit (.strVal s) => s!"str_lit {s.quote}"
    | .mdata _ b => s!"mdata({go b depth})"
    | .proj n i b => s!"proj({projectName n},{i},{go b depth})"

  /-- Render a universe level. Universe metavariables get a marker for the same
  reason expression metavariables do. -/
  projectLevel : Level → String
    | .zero => "0"
    | .succ l => s!"succ({projectLevel l})"
    | .max a b => s!"max({projectLevel a},{projectLevel b})"
    | .imax a b => s!"imax({projectLevel a},{projectLevel b})"
    | .param n => projectName n
    | .mvar _ => "LMVAR"

/-- Render one captured declaration. -/
def projectDeclaration (d : CapturedDeclaration) : Array String :=
  let header :=
    s!"  decl {projectName d.name} kind={projectKind d.info} \
cmd={d.commandOrdinal} universes=[{String.intercalate "," (d.info.levelParams.map projectName)}]"
  let type := s!"    type {projectExpr d.info.type}"
  match d.value? with
  | some v => #[header, type, s!"    value {projectExpr v}"]
  | none => #[header, type]

/-- Render the syntactic shape of a command: its kind and source range.

The command's own text is not reproduced, so the projection stays stable under
whitespace-only differences that do not change what was elaborated. -/
def projectCommand (c : CapturedCommand) : String :=
  let range := match c.range with
    | some (s, e) => s!"{s}-{e}"
    | none => "-"
  s!"command {c.ordinal} kind={projectName c.stx.getKind} range={range} \
new={c.newConstants.size}"

/-- Render the imports declared by the module header.

The same module can legitimately appear more than once with different flags —
Lean's implicit `Init` prelude import and a module's own `import Init` differ
only in `isMeta` — so every flag that distinguishes two entries is shown. -/
def projectImports (m : CapturedModule) : Array String :=
  m.finalEnv.header.imports.map fun i =>
    let flags := #[
      ("all", i.importAll),
      ("exported", i.isExported),
      ("meta", i.isMeta)
    ].filterMap fun (n, on) => if on then some n else none
    s!"import {projectName i.module} [{String.intercalate "," flags.toList}]"

/-- The complete stable projection of one captured module.

Repeated capture of identical inputs must produce these exact bytes (C8, C10). -/
def projectModule (m : CapturedModule) : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push s!"module {projectName (m.module.foldl (init := Name.anonymous)
    fun n c => Name.mkStr n c)}"
  lines := lines.push s!"path {m.path}"
  lines := lines ++ projectImports m
  lines := lines.push s!"commands {m.commands.size}"
  for c in m.commands do
    lines := lines.push (projectCommand c)
  let delta := moduleDelta m
  lines := lines.push s!"declarations {delta.size}"
  for d in delta do
    lines := lines ++ projectDeclaration d
  return String.intercalate "\n" lines.toList ++ "\n"

end ExplicitLean
