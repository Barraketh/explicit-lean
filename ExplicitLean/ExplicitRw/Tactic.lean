module
prelude

public meta import ExplicitLean.ExplicitRw.Basic
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Intro
public meta import Lean.Parser.Tactic

public meta section

/-!
# The `explicit_rw` tactic

`explicit_rw` replays a recorded simp trace positionally, with no search.

```
explicit_rw [foo at [1, 1], ← bar at [], baz a b at [0, 1, 1],
             unfold f at [1], beta at [1, 1], eq (2 + 3 = 5) by rfl at [1]] at h
```

Each step names a position (a `SubExpr.Pos` child-index list, see
`tracking/SIMP-TRACE-SPEC.md`), navigates to exactly that subterm, and replaces
it. Steps apply in order; each position is relative to the result of the
previous step. There is no fallback, no search and no retry at other positions:
every failure names the step index and the reason.

## Step forms

| Form                              | Meaning                                         |
| --------------------------------- | ----------------------------------------------- |
| `e at [..]`                       | rewrite left-to-right with the equation/iff `e`  |
| `← e at [..]`                     | rewrite right-to-left                            |
| `unfold c at [..]`                | delta-unfold the constant `c` (definitional)     |
| `beta at [..]`                    | beta-reduce the subterm (definitional)           |
| `eta at [..]`                     | eta-reduce the subterm (definitional)            |
| `proj at [..]`                    | reduce a structure projection (definitional)     |
| `zeta at [..]`                    | replace `let x := v; b` by `b[v/x]` (the only    |
|                                   | step that destroys a `let`)                      |
| `change t at [..]`                | replace by the defeq term `t` (definitional)     |
| `eq (lhs = rhs) by rfl at [..]`   | prove the equation with `rfl`/`decide`, rewrite  |
| `intro_ctx h at [..]`             | recognised, **not implemented**; fails by name   |

`e` is an ordinary term, so explicit arguments (`baz a b`), local hypotheses and
side-condition proofs are written as usual and elaborated as usual: implicits,
universes and instances are recovered by elaboration and unification.

Positions are raw child indices, *not* `conv`'s `arg n` numbering: `conv`'s
`arg` counts explicit arguments, while `0`/`1` here are the `fn`/`arg` children
of `Expr.app`, so `f a b` has `b` at `[1]` and `a` at `[0, 1]`.

## Closing form

`explicit_rw [...] then rfl` runs `rfl` on the remaining goal after the last
step. The closer is a **closed enumeration** — `rfl`, `decide`, `exact <term>` —
and `eq ... by` likewise accepts only `rfl` or `decide`. Omit the clause to leave
the goal open. `trivial` and bare `assumption` are excluded because both search
where the spec recorded an exact choice; the spec's `true_intro`,
`assumption:<name>` and `absurd:<hyp>` all render as `exact <term>`. `rfl` is the
ordinary `rfl` tactic (`Eq`/`Iff`/`HEq` reflexivity and `@[refl]` lemmas), not a
simp-backed one.

The `then` clause applies to the goal. A trace that rewrites a hypothesis leaves
the closer to the next line, which is where the spec's `absurd:<hyp>` form lands.

Neither slot is a `tacticSeq`, deliberately. A free `tacticSeq` would let a
generated trace carry `simp` (or any forbidden tactic) *inside* the product
tactic, where a lint scanning `ExplicitLean/ExplicitRw*` could never see it,
because the offending text lives at the generated call site. For the same
reason every term this tactic elaborates — a lemma, a `change` target, an `eq`
equation, an `exact` closer — is rejected if it contains a `by` block.

## No simp

Nothing in this tactic calls, imports for use, or expands to `Lean.Meta.Simp` or
any simp-family tactic, and no trace written in this syntax can introduce one:
the two tactic slots are closed enumerations, and every term the tactic
elaborates is refused if it elaborates a tactic block, however that block got
there (written, via `macro`/`notation`, or via a custom term elaborator).
`Experiment/check_no_simp_family.py` enforces the former.
-/

namespace ExplicitLean.ExplicitRw

open Lean Elab Tactic Meta

/-- `at [0, 1, 1]` — the position a step applies at. `at []` is the whole location. -/
syntax explicitRwPos := " at " "[" num,* "]"

/-- A lemma rewrite, forwards or backwards: `foo a b at [1]`, `← bar at []`. -/
syntax explicitRwRw := ("← ")? term explicitRwPos

/-- `unfold f at [1]` — delta-unfold one constant, definitionally. -/
syntax explicitRwUnfold := "unfold " ident explicitRwPos

/--
`beta at [1]`, `eta at [1]`, `proj at [1]`, `zeta at [1]` — the silent
definitional reductions of the spec's `beta|eta|proj|zeta` step kinds.

`zeta` is the *only* step that destroys a `let`: it replaces `let x := v; b` by
`b[v/x]`. Rewriting inside a `let` body keeps the `let`, so that positions
recorded after such a step still describe the term.
-/
syntax explicitRwRed := (&"beta" <|> &"eta" <|> &"proj" <|> &"zeta") explicitRwPos

/--
`intro_ctx <name> at [1]` — the spec's contextual-simp step, which makes the
antecedent of an implication available as a hypothesis for later steps.

It is **recognised but not implemented**: contextual rewriting changes what is in
scope for subsequent positions, which this tactic's single-location model does
not represent. It is given syntax anyway so that a trace containing it fails with
an honest "not implemented" error naming the kind, rather than being parsed as a
lemma called `intro_ctx`.
-/
syntax explicitRwIntroCtx := &"intro_ctx " ident explicitRwPos

/-- `change t at [1]` — last-resort definitional replacement, checked by defeq. -/
syntax explicitRwChange := "change " term explicitRwPos

/--
The closers a trace may use, as a **closed enumeration**. `explicit_rw` is
product code, so it must not embed a free `tacticSeq`: that would let a
generated trace carry `simp` (or any other forbidden tactic) inside the product
tactic, where `Experiment/check_no_simp_family.py` could never see it. The
spec's `close` field maps onto `rfl` and `decide`, plus `exact <term>` for every
form that names something: `true_intro` is `exact True.intro`,
`assumption:<name>` is `exact <name>`, `absurd:<hyp>` is `exact <hyp>.elim`.

Two tactics are deliberately **not** offered, both because they search where the
spec recorded an exact choice. `trivial` is a macro that tries several tactics in
turn. Bare `assumption` scans the whole local context, so it can succeed by
finding a *different* hypothesis than the one the trace recorded; the spec writes
`assumption:<name>`, and `exact <name>` renders that exactly.

`rfl` here is the ordinary `rfl` tactic — `Eq`/`Iff`/`HEq` reflexivity and
`@[refl]` lemmas. It is not `simp`-backed and performs no simplification.
-/
syntax explicitRwCloser :=
  &"rfl" <|> &"decide" <|> (&"exact " term)

/--
`eq (2 + 3 = 5) by rfl at [1]` — a simproc-computed equation, proved by an
ordinary tactic. The spec's `by` field is exactly `rfl | decide`, so only those
two are accepted; see `explicitRwCloser` for why this is not a `tacticSeq`.
-/
syntax explicitRwEq := &"eq " term " by " (&"rfl" <|> &"decide") explicitRwPos

/-- One step of an `explicit_rw` trace. -/
syntax explicitRwStep :=
  explicitRwUnfold <|> explicitRwRed <|> explicitRwIntroCtx <|> explicitRwChange <|>
  explicitRwEq <|> explicitRwRw

/-- Optional closing tactic: `explicit_rw [...] then rfl`. -/
syntax explicitRwClose := " then " explicitRwCloser

/--
Replay a recorded simp trace positionally, with no search.

Each step names a `SubExpr.Pos` child-index path and the rewrite to perform
there. See the module documentation for the step forms.
-/
syntax (name := explicitRw) "explicit_rw " "[" explicitRwStep,* "]"
  (Lean.Parser.Tactic.location)? (explicitRwClose)? : tactic

namespace Impl

/-- Parse the child-index list out of an `explicitRwPos` node. -/
def parsePos (stx : Syntax) : Pos :=
  stx[2].getSepArgs.toList.map fun s => (s.isNatLit?.getD 0)

/-- Which location a step sequence applies to: the goal, or one hypothesis. -/
abbrev Target := Option FVarId

/-- The synthetic metavariables that exist right now, to diff against later. -/
def syntheticMVarSnapshot : TacticM (Std.HashSet MVarId) := do
  return (← getThe Term.State).syntheticMVars.toList.foldl (fun acc (m, _) => acc.insert m) {}

/--
Refuse a term that elaborated a tactic block.

This is the authoritative check, and it is *semantic*: every `by ...`, however
it got there — written directly, produced by a macro, by `notation`, or by a
custom term elaborator that calls `elabTerm` on it — registers a synthetic
metavariable whose `stx` *is* that `by` block. Matching on the recorded syntax
rather than on the kind is what makes this robust: a nested `elabTerm` can
register the block as `.postponed` instead of `.tactic`, so the kind alone
misses it, while the recorded syntax is the block either way.

`before` is a `syntheticMVarSnapshot` taken before the term was elaborated,
excluding metavariables that already existed — in particular the `by` block of
the proof that invoked `explicit_rw` itself.

Call this after elaborating and before synthetic metavariables are synthesized,
i.e. inside `Term.withSynthesize`'s body rather than after it.
-/
def checkNoPendingTactic (what : String) (idx? : Option Nat)
    (before : Std.HashSet MVarId) : TacticM Unit := do
  for (mvarId, decl) in (← getThe Term.State).syntheticMVars.toList do
    if before.contains mvarId then
      continue
    let isTactic :=
      match decl.kind with
      | .tactic .. => true
      | _ => decl.stx.getKind == ``Lean.Parser.Term.byTactic
    if isTactic then
      let msg := m!"{what} elaborates a tactic block. `explicit_rw` is product \
        code, so a trace may not run tactics inside a term: that would let a \
        tactic forbidden by the governing rule run where a lint over this module \
        could not see it. Write a closed term, or prove the lemma separately and \
        name it."
      match idx? with
      | some idx => stepError idx msg
      | none => throwError "explicit_rw: {msg}"

/--
Syntactic pre-check for a tactic block, kept as a second line of defence in
front of `checkNoPendingTactic`. It runs on macro-expanded syntax, so a macro
whose expansion is `by ...` is caught here too, and it gives a better message
because it names the offending node.
-/
partial def checkNoTacticBlock (what : String) (idx? : Option Nat) (stx : Syntax) :
    TacticM Unit := do
  -- Expand macros first: the written syntax of `SM` carries no `by` node, but
  -- its expansion does.
  let expanded ← try Elab.liftMacroM (expandMacros stx) catch _ => pure stx
  let offending? := find? stx <|> find? expanded
  if let some kind := offending? then
    let msg := m!"{what} contains a `{kind}` block. `explicit_rw` is product code, so a \
      trace may not embed a tactic block: it would let a tactic forbidden by the \
      governing rule run inside the product tactic, where a lint over this module \
      could not see it. Write a closed term, or prove the lemma separately and \
      name it."
    match idx? with
    | some idx => stepError idx msg
    | none => throwError "explicit_rw: {msg}"
where
  /-- The first `by`/tactic-sequence node in the tree, if any. -/
  find? (s : Syntax) : Option String := Id.run do
    let k := s.getKind
    if k == ``Lean.Parser.Term.byTactic then
      return some "by"
    if k == ``Lean.Parser.Tactic.tacticSeq || k == ``Lean.Parser.Tactic.tacticSeq1Indented then
      return some "tactic sequence"
    for arg in s.getArgs do
      if let some r := find? arg then
        return some r
    return none

/--
Elaborate a term to a proof of an equation or iff, returning `lhs`, `rhs` and a
proof of `lhs = rhs`, together with the metavariables introduced for the
lemma's own arguments so the caller can insist they all get assigned.
-/
def elabEquation (idx : Nat) (stx : Term) : TacticM (Expr × Expr × Expr × Array Expr) := do
  checkNoTacticBlock s!"the lemma term of this step" (some idx) stx
  let lemmaMsg := m!"`{stx}`"
  let snapshot ← syntheticMVarSnapshot
  let proof ← Term.withSynthesize (postpone := .no) do
    let e ← Term.elabTerm stx none
    checkNoPendingTactic s!"the lemma term of this step" (some idx) snapshot
    pure e
  -- Force any still-postponed synthetic metavariables. A `Sort*`-polymorphic
  -- lemma such as `not_nonempty_iff` can otherwise leave its universe level
  -- unresolved, in which case `inferType` reports a bare `?m` instead of the
  -- `Iff`, and whether that happens depends on unrelated imports. Replay must
  -- not depend on the import context.
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  -- A term that failed to elaborate (an unknown identifier, say, because the
  -- lemma's module is not imported here) comes back as `sorryAx`, whose type is
  -- a bare metavariable. Reporting that as "does not prove an equation" sends
  -- the trace author hunting for the wrong problem, so name it.
  if proof.hasSorry then
    stepError idx m!"lemma {lemmaMsg} failed to elaborate. If it is a global \
      lemma, its module is probably not imported in this file; if it is a local \
      hypothesis, it is not in scope at this position. (Lean reports the \
      underlying error separately.)"
  let type ← instantiateMVars (← inferType proof)
  -- Open the lemma's own leading binders as metavariables, so that matching the
  -- position determines them by unification rather than by search.
  let (mvars, _, type') ← forallMetaTelescopeReducing type
  let proof' := mkAppN proof mvars
  let (lhs, rhs, eqProof) ← asEquation idx lemmaMsg proof' type'
  -- Metavariables can also enter through elaboration of the written term itself
  -- (an implicit argument the syntax leaves open), not only through the
  -- telescope above. Collect both so none can escape into the goal.
  let fromTerm := (← instantiateMVars proof).collectMVars {} |>.result
  let fromType := (← instantiateMVars type).collectMVars {} |>.result
  let extra := (fromTerm ++ fromType).map Expr.mvar
  return (lhs, rhs, eqProof, mvars ++ extra)

/--
Fail when any universe level metavariable survives in the given expressions.

Levels are determined by unifying the lemma's side with the subterm at the
recorded position. A leftover level metavariable means the trace did not pin it;
letting Lean default it would make the same trace replay differently depending
on elaboration order and on which modules happen to be imported.
-/
def checkNoLevelMVars (idx : Nat) (lemmaStx : MessageData) (es : Array Expr) :
    TacticM Unit := do
  for e in es do
    let e ← instantiateMVars e
    if e.hasLevelMVar then
      stepError idx m!"lemma {lemmaStx} still has an unassigned universe level \
        after matching at the given position. The position does not determine it, \
        and `explicit_rw` never defaults a level: that would make the replay \
        depend on the import context. Write the universe explicitly on the lemma \
        name, or fix the position."

/-- Run a rewrite step at `pos` inside `e`. -/
def runRwStep (idx : Nat) (e : Expr) (pos : Pos) (stx : Term) (symm : Bool) :
    TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let (lhs, rhs, eqProof, mvars) ← elabEquation idx stx
      let (source, target) := if symm then (rhs, lhs) else (lhs, rhs)
      unless ← isDefEq source sub do
        stepError idx m!"lemma `{stx}` does not match the subterm at \
          position {Pos.render pos}.\nExpected{indentExpr (← instantiateMVars source)}\n\
          but the subterm is{indentExpr sub}"
      closeLemmaMVars idx m!"`{stx}`" mvars
      let eqProof ← instantiateMVars eqProof
      let target ← instantiateMVars target
      -- Universe levels are fixed by unifying the lemma's side with the subterm.
      -- One still unassigned means the position did not determine it; defaulting
      -- it would make the replay depend on elaboration order and on imports, so
      -- this is an error like any other unresolved argument.
      checkNoLevelMVars idx m!"`{stx}`" #[eqProof, target]
      let h ← if symm then mkEqSymm eqProof else pure eqProof
      return Replacement.eq target h)
    (fun pfx child sub => badPosError idx pos pfx child sub)

/-- Run a definitional step at `pos` inside `e`, using `reduce` on the subterm. -/
def runDefeqStep (idx : Nat) (e : Expr) (pos : Pos) (what : MessageData)
    (reduce : Expr → TacticM Expr) : TacticM Replacement := do
  rewriteAt e pos
    (fun sub => do
      let newSub ← reduce sub
      unless ← isDefEq sub newSub do
        stepError idx m!"{what} at position {Pos.render pos} produced a term that is \
          not definitionally equal to the original.\nBefore{indentExpr sub}\n\
          After{indentExpr newSub}"
      return Replacement.defeq newSub)
    (fun pfx child sub => badPosError idx pos pfx child sub)

/-- Delta-unfold exactly the constant `c` at the head of `sub`. -/
def unfoldConst (idx : Nat) (c : Name) (sub : Expr) : TacticM Expr := do
  unless (← getEnv).contains c do
    stepError idx m!"`unfold {c}` names a constant that does not exist."
  -- Check the head before unfolding, so naming the wrong constant is reported as
  -- such rather than as whatever the subterm happened to reduce to.
  unless sub.getAppFn.constName? == some c do
    stepError idx m!"`unfold {c}` was applied where the head constant is \
      `{sub.getAppFn}`."
  -- `unfoldDefinition?` fails for plain definitions under `withReducible`, so
  -- fall back to default transparency. Both are delta steps on `c` alone.
  match ← withReducible (unfoldDefinition? sub) with
  | some e => return e
  | none =>
    match ← unfoldDefinition? sub with
    | some e => return e
    | none =>
      stepError idx m!"`unfold {c}` cannot unfold the subterm at this position; \
        `{c}` has no delta-reduction here."

/-- Eta-reduce `fun x => f x` to `f`, failing when the subterm is not an eta-redex. -/
def etaReduce (idx : Nat) (sub : Expr) : TacticM Expr := do
  let r := sub.eta
  if r == sub then
    stepError idx m!"`eta` at this position: the subterm is not an eta-redex."
  return r

/--
Reduce a structure projection applied to a constructor application, or a
projection-function application. This is projection reduction only: it refuses a
subterm that is not headed by a projection, so a `proj` step can never stand in
for an arbitrary `whnf`.
-/
def projReduce (idx : Nat) (sub : Expr) : TacticM Expr := do
  let isProjLike ←
    match sub with
    | .proj .. => pure true
    | _ =>
      match sub.getAppFn with
      | .const c _ => pure ((← getEnv).getProjectionFnInfo? c).isSome
      | _ => pure false
  unless isProjLike do
    stepError idx m!"`proj` at this position: the subterm is not a projection; \
      its head is `{sub.getAppFn}`."
  -- A raw `Expr.proj` reduces by `whnfCore` alone. A projection *function*
  -- application (what the elaborator produces for `s.field`) needs a delta step
  -- to unfold the function first; `whnfCore` performs no delta, so without this
  -- the step would always report "does not reduce".
  -- Require the projected structure to be a constructor application, so that the
  -- step really is a projection reduction. Without this, a class projection such
  -- as `HAdd.hAdd` (which `getProjectionFnInfo?` also reports) would let `proj`
  -- perform arbitrary unfolding.
  let env ← getEnv
  let structArg? : Option Expr :=
    match sub with
    | .proj _ _ b => some b
    | _ =>
      match sub.getAppFn with
      | .const c _ =>
        match env.getProjectionFnInfo? c with
        | some info => sub.getAppArgs[info.numParams]?
        | none => none
      | _ => none
  let some structArg := structArg?
    | stepError idx m!"`proj` at this position: the projection is not applied to a \
        structure argument."
  let isCtor ←
    match (← whnfCore structArg).getAppFn with
    | .const c _ => pure ((env.find? c).any (· matches .ctorInfo _))
    | _ => pure false
  unless isCtor do
    stepError idx m!"`proj` at this position: the projection's argument is not a \
      constructor application, so there is nothing to reduce."
  let r ← whnfCore sub
  if r != sub then
    return r
  if let some unfolded ← unfoldDefinition? sub then
    let r ← whnfCore unfolded
    if r != sub then
      return r
  stepError idx m!"`proj` at this position: the projection does not reduce."

/-- Apply one parsed step to the current expression. -/
def runStep (idx : Nat) (e : Expr) (stx : TSyntax ``explicitRwStep) : TacticM Replacement := do
  let stx := stx.raw[0]
  match stx.getKind with
  | ``explicitRwUnfold =>
    let pos := parsePos stx[2]
    let c ← realizeGlobalConstNoOverloadWithInfo stx[1]
    runDefeqStep idx e pos m!"`unfold {c}`" (unfoldConst idx c)
  | ``explicitRwRed =>
    let pos := parsePos stx[1]
    -- The alternation wraps the keyword in a `token.<kw>` node, so the atom
    -- itself is one level down.
    let kind := stx[0][0].getAtomVal
    match kind with
    | "beta" => runDefeqStep idx e pos m!"`beta`" fun sub => do
        let r := sub.headBeta
        if r == sub then
          stepError idx m!"`beta` at this position: the subterm is not a beta-redex."
        return r
    | "eta" => runDefeqStep idx e pos m!"`eta`" (etaReduce idx)
    | "proj" => runDefeqStep idx e pos m!"`proj`" (projReduce idx)
    | "zeta" => runDefeqStep idx e pos m!"`zeta`" fun sub => do
        let .letE _ _ v b _ := sub
          | stepError idx m!"`zeta` at this position: the subterm is not a `let`."
        return b.instantiate1 v
    | k => throwError "explicit_rw: internal error: unknown reduction keyword `{k}`"
  | ``explicitRwIntroCtx =>
    stepError idx m!"`intro_ctx` is a recorded step kind that `explicit_rw` does not \
      implement: contextual rewriting changes what is in scope for later positions, \
      which this tactic's single-location model does not represent. This trace \
      cannot be replayed; hand-write the proof instead."
  | ``explicitRwChange =>
    let pos := parsePos stx[2]
    let target : Term := ⟨stx[1]⟩
    checkNoTacticBlock s!"the `change` term of this step" (some idx) target
    runDefeqStep idx e pos m!"`change {target}`" fun sub => do
      let ty ← inferType sub
      let snapshot ← syntheticMVarSnapshot
      let newSub ← Term.withSynthesize (postpone := .no) do
        let e ← Term.elabTermEnsuringType target ty
        checkNoPendingTactic s!"the `change` term of this step" (some idx) snapshot
        pure e
      instantiateMVars newSub
  | ``explicitRwEq =>
    let pos := parsePos stx[4]
    let eqStx : Term := ⟨stx[1]⟩
    checkNoTacticBlock s!"the `eq` equation of this step" (some idx) eqStx
    -- The `by` slot is the closed keyword `rfl` or `decide`, never a tacticSeq.
    let byKind := stx[3][0].getAtomVal
    -- Prove the stated equation with the named ordinary tactic, then rewrite.
    rewriteAt e pos
      (fun sub => do
        let snapshot ← syntheticMVarSnapshot
        let eqType ← Term.withSynthesize (postpone := .no) do
          let e ← Term.elabType eqStx
          checkNoPendingTactic s!"the `eq` equation of this step" (some idx) snapshot
          pure e
        let eqType ← instantiateMVars eqType
        let some (_, lhs, rhs) := eqType.eq?
          | stepError idx m!"`eq {eqStx}` must state an equation `lhs = rhs`; it states\
              {indentExpr eqType}"
        unless ← isDefEq lhs sub do
          stepError idx m!"`eq {eqStx}`: its left-hand side does not match the subterm \
            at position {Pos.render pos}.\nExpected{indentExpr lhs}\n\
            but the subterm is{indentExpr sub}"
        let goal ← mkFreshExprSyntheticOpaqueMVar eqType
        let remaining ←
          match byKind with
          | "rfl" => Tactic.run goal.mvarId! (evalTactic (← `(tactic| rfl)))
          | "decide" => Tactic.run goal.mvarId! (evalTactic (← `(tactic| decide)))
          | k => stepError idx m!"`eq ... by {k}`: only `rfl` and `decide` are accepted."
        unless remaining.isEmpty do
          stepError idx m!"`eq {eqStx} by {byKind}`: the tactic left \
            {remaining.length} goal(s) open."
        let h ← instantiateMVars goal
        return Replacement.eq (← instantiateMVars rhs) h)
      (fun pfx child sub => badPosError idx pos pfx child sub)
  | ``explicitRwRw =>
    let symm := !stx[0].isNone
    let term : Term := ⟨stx[1]⟩
    let pos := parsePos stx[2]
    runRwStep idx e pos term symm
  | k => throwError "explicit_rw: internal error: unexpected step kind `{k}`"

/-- Apply every step in order to the expression at `target`, rebuilding the goal. -/
def runSteps (steps : Array (TSyntax ``explicitRwStep)) (target : Target) : TacticM Unit := do
  for h : idx in [0 : steps.size] do
    let stx := steps[idx]
    let goal ← getMainGoal
    goal.withContext do
      let e ← match target with
        | none => instantiateMVars (← goal.getType)
        | some fvarId => instantiateMVars (← fvarId.getType)
      -- Navigation errors are raised inside `rewriteAt`, which does not know the
      -- step index. Prefix any message that does not already carry it, so every
      -- failure names the step it came from.
      let r ←
        try
          runStep idx e stx
        catch ex => do
          let msg ← ex.toMessageData.toString
          if msg.startsWith "explicit_rw:" then
            throw ex
          else
            stepError idx ex.toMessageData
      let newE ← instantiateMVars r.newExpr
      match target with
      | none =>
        match r.proof? with
        | none => replaceMainGoal [← goal.replaceTargetDefEq newE]
        | some h => replaceMainGoal [← goal.replaceTargetEq newE (← instantiateMVars h)]
      | some fvarId =>
        match r.proof? with
        | none =>
          let res ← goal.replaceLocalDeclDefEq fvarId newE
          replaceMainGoal [res]
        | some h =>
          -- `Eq.mp h hyp : newType` transports the hypothesis forwards.
          let h ← instantiateMVars h
          let newProof ← mkEqMP h (mkFVar fvarId)
          let res ← goal.replace fvarId newProof newE
          replaceMainGoal [res.mvarId]

/--
Run the closing tactic of a `then` clause.

The parser already restricts this to the closed enumeration, so this only has to
dispatch. `exact <term>` additionally rejects a term containing a tactic block,
which is the one way a term could reintroduce arbitrary tactics.
-/
def runCloser (stx : Syntax) : TacticM Unit := do
  -- Each alternative wraps its keyword one level down: a bare keyword as
  -- `token.<kw>`, and `exact <term>` as a `group` whose child 0 is the atom.
  match stx[0][0].getAtomVal with
  | "rfl" => evalTactic (← `(tactic| rfl))
  | "decide" => evalTactic (← `(tactic| decide))
  | "exact" =>
    let t : Term := ⟨stx[0][1]⟩
    checkNoTacticBlock "the closing `exact` term" none t
    let goal ← getMainGoal
    goal.withContext do
      let snapshot ← syntheticMVarSnapshot
      let val ← Term.withSynthesize (postpone := .no) do
        let e ← Term.elabTermEnsuringType t (← goal.getType)
        checkNoPendingTactic "the closing `exact` term" none snapshot
        pure e
      goal.assign (← instantiateMVars val)
      replaceMainGoal []
  | k =>
    throwError "explicit_rw: internal error: unknown closer `{k}`"

end Impl

open Impl in
@[tactic explicitRw]
def evalExplicitRw : Tactic := fun stx => do
  let steps := stx[2].getSepArgs.map fun s => (⟨s⟩ : TSyntax ``explicitRwStep)
  let locStx := stx[4]
  let closeStx := stx[5]
  -- Resolve the location: the goal, or exactly one hypothesis.
  let target ← do
    if locStx.isNone then
      pure (none : Target)
    else
      match expandLocation locStx[0] with
      | .targets hyps goalToo =>
        if goalToo || hyps.size != 1 then
          throwError "explicit_rw: a trace applies to exactly one location: either the \
            goal, or `at h` for a single hypothesis."
        let fvarId ← getFVarId hyps[0]!
        pure (some fvarId : Target)
      | .wildcard =>
        throwError "explicit_rw: `at *` is not supported: positions are relative to one \
          location. Write one `explicit_rw` per location."
  runSteps steps target
  unless closeStx.isNone do
    match target with
    | none => runCloser closeStx[0][1]
    | some _ =>
      throwError "explicit_rw: the `then` closing form applies to the goal, but this \
        trace rewrites a hypothesis. Write the closing tactic on the next line."

end ExplicitLean.ExplicitRw
