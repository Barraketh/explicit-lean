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

We must compare a recorded subterm, which simp observed with its enclosing
binders instantiated as *free* variables, against the running term, where those
binders are still `bvar`s.

Rather than guess which free variables simp used, we abstract them out of the
recorded subterm: any free variable in `before` that is **not** present in the
location's own local context (the one the tactic started in) must have been
introduced by simp when it descended under a binder.  Replacing each such
variable by the `bvar` for its binder depth turns the recorded subterm back into
the open form that appears in the running term.

`depth` is the number of binders crossed to reach the candidate position, and
simp introduces its locals outermost-first, so the fvar introduced at binder
depth `d` (0-based, outermost first) corresponds to `bvar (depth - 1 - d)`.
-/

/-- A candidate occurrence: its position and the number of binders crossed. -/
structure Occurrence where
  pos : Pos
  numBinders : Nat
  deriving Inhabited, Repr

/--
Abstract the simp-introduced free variables of `target`, given the free
variables introduced on the way to a position at binder `depth`.  `simpFVars`
lists them outermost-first.
-/
def abstractSimpFVars (target : Expr) (simpFVars : Array FVarId) (depth : Nat) : Expr :=
  if simpFVars.isEmpty || depth == 0 then target
  else
    -- Only the innermost `depth` binders are in scope at this position.
    let n := simpFVars.size
    if depth > n then target
    else
      let scope := simpFVars.extract (n - depth) n  -- outermost-first
      target.replace fun e =>
        match e with
        | .fvar fid =>
          match scope.findIdx? (· == fid) with
          | some d => some (.bvar (depth - 1 - d))
          | none => none
        | _ => none

/--
Find every position in `e` whose subterm equals `target` after abstracting
simp's binder variables.  Returns positions in pre-order; a matched node is not
searched further, since its subterms were rewritten as part of it.
-/
partial def findOccurrences (e target : Expr) (simpFVars : Array FVarId)
    (ctxDepth : Nat := 0) : Array Occurrence :=
  go e #[] 0 0
where
  go (e : Expr) (pos : Pos) (depth : Nat) (arrows : Nat) : Array Occurrence := Id.run do
    -- A firing made under `ctxDepth` contextual hypotheses can only have
    -- happened in the consequent of at least that many implications, so a
    -- shallower position is not a real occurrence.
    if arrows >= ctxDepth && e == abstractSimpFVars target simpFVars depth then
      return #[{ pos, numBinders := depth }]
    -- (index, child, crosses a term binder, crosses an implication arrow)
    let isArrow := e.isArrow
    let children : Array (Nat × Expr × Bool × Bool) :=
      match e with
      | .app f a => #[(0, f, false, false), (1, a, false, false)]
      | .lam _ t b _ => #[(0, t, false, false), (1, b, true, false)]
      | .forallE _ t b _ =>
        #[(0, t, false, false), (1, b, !isArrow, isArrow)]
      | .letE _ t v b _ =>
        #[(0, t, false, false), (1, v, false, false), (2, b, true, false)]
      | .mdata _ b => #[(0, b, false, false)]
      | .proj _ _ b => #[(0, b, false, false)]
      | _ => #[]
    let mut acc : Array Occurrence := #[]
    for (i, c, bin, arrow) in children do
      acc := acc ++ go c (pos.push i) (if bin then depth + 1 else depth)
        (if arrow then arrows + 1 else arrows)
    return acc

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
def solvePositions (baseLCtx : LocalContext) (pre : Expr) (raws : Array RawStep) :
    MetaM (Array SolvedStep × Expr) := do
  let mut running := pre
  let mut solved : Array SolvedStep := #[]
  for raw in raws do
    -- Free variables simp introduced for binders it descended under: those in
    -- the firing's local context but not in the location's own context, in
    -- declaration order (outermost first).
    -- Term binders simp descended under: simp-introduced locals that are not
    -- proofs.  Proof locals come from `+contextual` and bind no term position.
    let introduced := raw.fvarKinds.filter fun (fid, _) => !(baseLCtx.contains fid)
    let simpFVars : Array FVarId :=
      (introduced.filter fun (_, isPrf) => !isPrf).map (·.1)
    -- Contextual hypotheses in scope at this firing.  Their presence means the
    -- firing happened under an implication whose antecedent simp assumed, so a
    -- match must lie in the consequent of that many implications.
    let ctxDepth := (introduced.filter fun (_, isPrf) => isPrf).size
    let occs := findOccurrences running raw.before simpFVars ctxDepth
    if occs.isEmpty then
      -- The firing acted on a term simp had already rewritten away, or on an
      -- instantiation we cannot reconstruct.  Never drop a step silently.
      throwError "simp_trace: cannot locate recorded subterm in running term\n\
        before: {raw.before}\nrunning: {running}"
    for occ in occs do
      -- Validation, per the task: navigating `pos` must reach `before` (in its
      -- abstracted, open form), and replacing it must yield the next term.
      let expected := abstractSimpFVars raw.before simpFVars occ.numBinders
      let some (sub, _) := navigate? running occ.pos
        | throwError "simp_trace: position navigation failed at {occ.pos}"
      unless sub == expected do
        throwError "simp_trace: validation failed: subterm at {occ.pos} is\n\
          {sub}\nbut the recorded step's `before` is\n{expected}"
      let replacement := abstractSimpFVars raw.after simpFVars occ.numBinders
      let some next := replaceAt? running occ.pos replacement
        | throwError "simp_trace: position replacement failed at {occ.pos}"
      solved := solved.push { pos := occ.pos, raw }
      running := next
  return (solved, running)

end ExplicitLean.SimpTrace
