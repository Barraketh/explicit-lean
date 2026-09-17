/-
Structural navigation and the replay **validator**.

The position-reconstruction machinery this module used to hold — `findBridge?`,
`findBridgeChain?`, `reducibleSites`, the stale-term `refresh`, `abstractSimpFVars`
and `findOccurrences` — is **deleted**.  Positions now come out of the forked
traversal exactly (`ExplicitLean/SimpTrace/Traversal.lean`), so nothing here
searches: three review rounds showed the search was the source of the critical
defects (REVIEW-3 C2's exponential chain search, C1's unattributed firings and
M4's leaked `_fvar` in a bridge target).

What survives is the safety net the task asks for: after the traversal, replay
the recorded steps structurally from the pre-state term — navigate `pos`, check
the subterm equals `before`, substitute `after` — and require the final term to
equal simp's result.  A mismatch is a hard, loud failure.
-/

module

public meta import Lean
public meta import ExplicitLean.SimpTrace.Types

public meta section

namespace ExplicitLean.SimpTrace

open Lean Meta

/-! ### Navigation

Child indices follow the spec: `app f a` has 0 = f, 1 = a; `lam`/`forallE` have
0 = binder type, 1 = body; `letE` has 0 = type, 1 = value, 2 = body; `mdata` and
`proj` have child 0.
-/

/-- Descend one child.  Returns `none` for an out-of-range index. -/
def childAt? (e : Expr) (i : Nat) : Option Expr :=
  match e, i with
  | .app f _, 0 => some f
  | .app _ a, 1 => some a
  | .lam _ t _ _, 0 => some t
  | .lam _ _ b _, 1 => some b
  | .forallE _ t _ _, 0 => some t
  | .forallE _ _ b _, 1 => some b
  | .letE _ t _ _ _, 0 => some t
  | .letE _ _ v _ _, 1 => some v
  | .letE _ _ _ b _, 2 => some b
  | .mdata _ b, 0 => some b
  | .proj _ _ b, 0 => some b
  | _, _ => none

/-- Does descending into child `i` of `e` cross a binder *node* — one that
raises the de Bruijn level inside the subterm?

Every `lam`/`forallE` body and every `letE` body does, including a
**non-dependent** `forallE` (an arrow `p → q`): although simp introduces no term
variable for it, the `Expr` node is still a binder, so `Expr.abstract` and
`Expr.instantiate` count it.  This is the difference between the two depths the
validator needs: `binderNodes` (this one) says how far the de Bruijn indices are
shifted, while the traversal's own binder stack says how many *term variables*
are actually in scope.  Conflating them shifts every index below an arrow, which
is what made a rewrite under `∀ y, y = a' → y = x` fail validation. -/
def crossesBinder (e : Expr) (i : Nat) : Bool :=
  match e, i with
  | .lam .., 1 => true
  | .forallE .., 1 => true
  | .letE .., 2 => true
  | _, _ => false

/-- Replace the subterm at `pos` with `repl`. -/
partial def replaceAt? (e : Expr) (pos : Pos) (repl : Expr) : Option Expr := do
  if pos.size = 0 then
    return repl
  else
    let i := pos[0]!
    let rest := pos.extract 1 pos.size
    let sub ← childAt? e i
    let sub' ← replaceAt? sub rest repl
    match e, i with
    | .app _ a, 0 => some (.app sub' a)
    | .app f _, 1 => some (.app f sub')
    | .lam n _ b bi, 0 => some (.lam n sub' b bi)
    | .lam n t _ bi, 1 => some (.lam n t sub' bi)
    | .forallE n _ b bi, 0 => some (.forallE n sub' b bi)
    | .forallE n t _ bi, 1 => some (.forallE n t sub' bi)
    | .letE n _ v b nd, 0 => some (.letE n sub' v b nd)
    | .letE n t _ b nd, 1 => some (.letE n t sub' b nd)
    | .letE n t v _ nd, 2 => some (.letE n t v sub' nd)
    | .mdata d _, 0 => some (.mdata d sub')
    | .proj s i' _, 0 => some (.proj s i' sub')
    | _, _ => none

/-- Navigate to `pos`, returning the subterm and the number of binder *nodes*
crossed to reach it.  Returns `none` for a position the term does not have. -/
partial def navigate? (e : Expr) (pos : Pos) (depth : Nat := 0) :
    Option (Expr × Nat) := do
  if pos.size = 0 then
    return (e, depth)
  else
    let i := pos[0]!
    let rest := pos.extract 1 pos.size
    let sub ← childAt? e i
    navigate? sub rest (if crossesBinder e i then depth + 1 else depth)

/-! ### Open and closed subterms

The traversal observes a subterm with its enclosing binders instantiated as
*free* variables (simp introduces one local per binder it descends under),
while the running term still has loose `bvar`s there.  The events carry the
local context they were observed in, so the validator abstracts exactly the
free variables that are not in the location's own context, innermost last.

`Expr.abstract` is used rather than `Expr.replace`: it accounts for binders
*inside* the subterm, so a variable occurring under a nested binder gets the
right de Bruijn index.  (`Expr.replace` does not, and getting this wrong was
review round 1's shadowed-binder defect.)
-/

/--
Abstract the traversal-introduced free variables of `target` so it matches the
open subterm sitting at a position under `binderNodes` binder nodes.

`simpFVars` are the free variables the traversal substituted for the *term*
binders it descended under, outermost first.  `binderNodes` is how many binder
`Expr` nodes the position path crossed, which can be larger: a non-dependent
arrow is a binder node that binds no term variable.

`Expr.abstract xs` assigns `bvar (xs.size - 1 - i)` to `xs[i]`, i.e. it assumes
the variables are the innermost `xs.size` binders.  When binder nodes that bind
nothing sit *below* the term binders (exactly the arrow case), the real indices
are shifted up by the number of such nodes, so we pad the scope with that many
dummy slots at the inner end.

`Expr.abstract` is used rather than `Expr.replace`: it accounts for binders
*inside* `target`, so a variable occurring under a nested binder gets the right
de Bruijn index.  (`Expr.replace` does not, and getting that wrong was review
round 1's shadowed-binder defect.)
-/
def abstractSimpFVars (target : Expr) (simpFVars : Array FVarId)
    (binderNodes : Nat) : Expr :=
  if simpFVars.isEmpty then target
  else
    let n := simpFVars.size
    -- Term binders in scope, outermost first, capped at the nodes crossed.
    let depth := min n binderNodes
    if depth == 0 then target
    else
      let scope := (simpFVars.extract (n - depth) n).map Expr.fvar
      -- Binder nodes that bind no term variable, sitting inside the term
      -- binders: they shift every index up by one each.
      let padding := binderNodes - depth
      if padding == 0 then
        target.abstract scope
      else
        -- `mkFVar` on fresh, unused ids: they occur nowhere in `target`, so they
        -- only consume de Bruijn slots, which is exactly the shift we need.
        let pad := (Array.range padding).map fun i =>
          Expr.fvar ⟨Name.mkSimple s!"_simpTracePad{i}"⟩
        target.abstract (scope ++ pad)

end ExplicitLean.SimpTrace
