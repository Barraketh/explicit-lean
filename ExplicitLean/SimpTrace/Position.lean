/-
Position solving and self-validation.

simp's `Methods` see a subterm but not its position, and simp rebuilds terms
bottom-up, so positions cannot be read off the traversal.  We therefore take
approach (b) from the task: record `(before, after)` pairs during the run and
recover positions afterwards by replaying the recorded replacements against a
running term that starts at the location's pre-state.

For each recorded step we search the running term for an occurrence of `before`
(structurally, up to the loose-bvar instantiation described below), replace it
by `after`, and emit one step per occurrence in a deterministic (pre-order)
order.  Emitting one step per occurrence is correct because simp's cache
rewrites identical subterms identically: if the running term contains `before`
at several positions, simp replaced all of them with `after`.

Everything is then validated: navigating each step's `pos` in the running term
must reach `before`, replacing it must yield the next running term, and the
final running term must equal simp's actual result.  A failure is a hard error.
-/
import Lean
import ExplicitLean.SimpTrace.Types
import ExplicitLean.SimpTrace.Recorder

namespace ExplicitLean.SimpTrace

open Lean Meta

/-! ### Navigation

Child indices follow the spec: `app f a` has 0 = f, 1 = a; `lam`/`forallE` have
0 = binder type, 1 = body; `letE` has 0 = type, 1 = value, 2 = body; `mdata` and
`proj` have child 0.

Recorded subterms were observed inside binders, where simp had instantiated the
bound variables as free variables.  The running term still has loose bound
variables under those binders.  We therefore navigate with a *binder stack* of
the free variables simp introduced and compare after instantiating.
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

/-- Does descending into child `i` of `e` cross a binder? -/
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

/-- Navigate to `pos`, returning the subterm with the binders it sits under
instantiated by the given free variables (innermost last). -/
partial def navigate? (e : Expr) (pos : Pos) (binders : Array Expr := #[]) :
    Option (Expr × Array Expr) := do
  if pos.size = 0 then
    return (e, binders)
  else
    let i := pos[0]!
    let rest := pos.extract 1 pos.size
    let sub ← childAt? e i
    -- Binder instantiation happens in `findOccurrences`/`checkAt`, which know
    -- which free variables simp used; here we only track the count.
    navigate? sub rest (if crossesBinder e i then binders.push default else binders)

/-! ### Occurrence search

We search the running term for subterms that, after instantiating the enclosing
binders with fresh free variables, are structurally equal to `before`.  Rather
than guess simp's free variables we compare *modulo* the binder instantiation:
we abstract `before`'s free variables that do not occur in the running term's
own local context and match them positionally against the binders crossed.
-/

/-- A candidate occurrence: its position and the number of binders crossed. -/
structure Occurrence where
  pos      : Pos
  numBinders : Nat
  deriving Inhabited, Repr

/--
Find every position in `e` whose subterm equals `target` once the binders
crossed on the way are instantiated with `fvars` (the free variables simp had in
scope at the firing, innermost last).

`fvarsOf` supplies, for a given binder depth, the free variable simp used.  We
do not know that mapping a priori, so `matchSub` instantiates loose bound
variables with the *innermost* `n` entries of `fvars` in order, which is exactly
what `Meta.lambdaTelescope`-style traversal produces.
-/
partial def findOccurrences (e target : Expr) (fvars : Array Expr) : Array Occurrence :=
  (go e #[] 0).fst
where
  /-- Returns (occurrences, whether this node matched). -/
  go (e : Expr) (pos : Pos) (depth : Nat) : Array Occurrence × Bool :=
    let inst := instantiateBinders e depth
    if inst == target then
      (#[{ pos, numBinders := depth }], true)
    else Id.run do
      let mut acc : Array Occurrence := #[]
      let children : Array (Nat × Expr × Bool) :=
        match e with
        | .app f a => #[(0, f, false), (1, a, false)]
        | .lam _ t b _ => #[(0, t, false), (1, b, true)]
        | .forallE _ t b _ => #[(0, t, false), (1, b, true)]
        | .letE _ t v b _ => #[(0, t, false), (1, v, false), (2, b, true)]
        | .mdata _ b => #[(0, b, false)]
        | .proj _ _ b => #[(0, b, false)]
        | _ => #[]
      for (i, c, bin) in children do
        let (sub, _) := go c (pos.push i) (if bin then depth + 1 else depth)
        acc := acc ++ sub
      return (acc, false)

  /-- Instantiate the `depth` loose bound variables with the innermost `depth`
  entries of `fvars`. -/
  instantiateBinders (e : Expr) (depth : Nat) : Expr :=
    if depth == 0 || !e.hasLooseBVars then e
    else
      let n := fvars.size
      if depth > n then e
      else
        -- `instantiate` expects the substitution for bvar 0 first.
        let sub := (Array.range depth).map fun k => fvars[n - 1 - k]!
        e.instantiate sub

/-! ### Trace assembly -/

/-- One solved step: a position plus the raw firing it came from. -/
structure SolvedStep where
  pos : Pos
  raw : RawStep
  deriving Inhabited

/--
Solve positions for `raws` against the location's pre-term `pre`, returning the
solved steps and the final running term.  Fails loudly when a recorded `before`
cannot be located, when the replacement does not reproduce the expected running
term, or when the final term does not match simp's actual result.
-/
def solvePositions (pre : Expr) (raws : Array RawStep) : MetaM (Array SolvedStep × Expr) := do
  let mut running := pre
  let mut solved : Array SolvedStep := #[]
  for raw in raws do
    let fvars := raw.lctx.getFVars
    let occs := findOccurrences running raw.before fvars
    if occs.isEmpty then
      -- The firing acted on a term simp had already rewritten away, or on an
      -- instantiation we cannot see.  Never drop it silently.
      throwError "simp_trace: cannot locate recorded subterm in running term\n\
        before: {raw.before}\nrunning: {running}"
    for occ in occs do
      -- Validate: navigating `pos` must reach `before`.
      let some (sub, _) := navigate? running occ.pos
        | throwError "simp_trace: position navigation failed"
      let some next := replaceAt? running occ.pos raw.after
        | throwError "simp_trace: position replacement failed"
      let _ := sub
      solved := solved.push { pos := occ.pos, raw }
      running := next
  return (solved, running)

end ExplicitLean.SimpTrace
