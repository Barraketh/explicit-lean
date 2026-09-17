# T2-explicit-rw result

Status: **complete**, all checks pass. Rounds 1-4: 7/7, 7/7, 3/3, 4/4.
`explicit_rw` replays a simp trace positionally with no search (design and
syntax: `ExplicitLean/ExplicitRw/Tactic.lean`). Nothing in it reaches
`Lean.Meta.Simp`. What a *trace* can introduce is a **conditional** guarantee,
which is what is actually true: no trace in this syntax can introduce a
simp-family tactic, *provided its file declares no term elaborators* (Round 3.1).

## Round 4 fixes
All four were **sufficiency**, not safety: the reviewer's 220-probe sweep found
no escape. The grammar admitted far less than Lean prints, so a generator could
not pass a recorded `lhs`/`rhs`/`to` string through.

1-3. *(2 major, 1 minor)* The grammar now covers pretty-printer output:
   `if _ then _ else _` (which T1's `reduceIte` already emits) and its dependent
   form; **projection on any parenthesised term**, which the spec's `absurd:<hyp>`
   close needs when the contradiction is an application (`(hp q).elim`) — this
   also removes a misleading "invalid 'by' tactic" message reported for files
   containing no `by`; untyped, unparenthesised binders; prefix `¬ - ↑ ⇑ ↥` and
   postfix `⁻¹`; the binary operators Mathlib pp emits; set-builder, pairs, and
   `Type`/`Prop`/`Type*`/`Sort*`. Terms and types are now **one** category —
   splitting them only duplicated every production.
   **Safety re-verified, not assumed.** The sweep was rebuilt as 216 probes (54
   terms x 4 slots) and re-run against the widened grammar: **all 140 escape
   probes still rejected at parse time, all 76 benign spellings now parse**. Two
   earlier sweep runs were discarded rather than reported — one ran against a
   mid-edit build, the other graded *any* error as rejection, hiding that benign
   terms were failing to elaborate rather than to parse.
4. *(spec)* `iota` implemented — one matcher or recursor reduction on a
   constructor, guarded like `proj` so it cannot stand in for a general `whnf`.
   A per-step `with [tac, ...]` clause discharges a conditional lemma's
   hypotheses in order from the closed set `rfl | decide | omega |
   exact <whitelisted term>`; `omega` is a decision procedure, not simp family,
   and a forbidden tactic there is a parse error like anywhere else. The `prop`
   flag needs no tactic support: the generator renders it as `eq_true <name>` /
   `eq_false <name>`, both ordinary lemmas, and a fixture pins each.

### Rounds 1-3 (all re-verified by later reviewers)
**Round 3** *(major)*: both guard layers keyed on syntax, so a term elaborator
calling the simplifier in `MetaM` produced neither a `by` node nor a synthetic
metavariable and passed — my claim that the guard caught a block "however it got
there" was false. Terms are now parsed in a whitelist grammar; the metavariable
check remains as defence in depth. *(minors)* `usedLetOnly := false`; counts.
**Residual hole, stated not papered over:** an identifier bound to a
`@[term_elab]` elaborator is indistinguishable from a constant at parse time.
Closed generator-side by the simp lint plus a ban on `elab`/`macro`/`syntax` in
generated regions — **noted for T4, not implemented here**.

**Round 2**: the `let`-body branch abstracted by *value*, destroying the `let`
when the value was closed and capturing unrelated occurrences when it was a free
variable — now `withLetDecl` + `mkLetFVars` by identity, with fixtures verified
to **fail** against the old code. `zeta` became a real step kind; `intro_ctx`
fails by name; bare `assumption` dropped (it searches).
**Round 1**: the `tacticSeq` hole in `then`/`eq ... by` (now closed
enumerations), `proj` delta, `change` messages, the dependent-function message,
`import` linting, coverage claims. Details in git.
**Addendum (T1 cross-check)**: the reported `IsEmpty` failure was **not** a
universe defect — `not_nonempty_iff` was simply not imported, and `?m.2` was the
`sorryAx`'s type. Level handling was implemented as directed anyway.

## Files (only owned; `ExplicitLean.lean`, `lakefile.toml` untouched)
`ExplicitLean/ExplicitRw{.lean,/Basic,/Tactic}.lean`; `test/ExplicitRw/` (6
fixtures + `RejectedSyntax/`: 13 cases, `expected.json`, README);
`Experiment/{check_explicit_rw,check_no_simp_family}.py`.

## Checks (re-run from scratch; Lean 4.32.2, pinned Mathlib)
- `lake build ExplicitLean.ExplicitRw` (clean): PASS, no warnings, 5.1 s
- `lake env lean test/ExplicitRw/<each>.lean` (6): PASS, no output, 1.8–2.6 s ea
- `python3 -B Experiment/check_explicit_rw.py`: PASS (6 + 13 cases), 44.7 s
- `python3 -B Experiment/check_no_simp_family.py`: PASS (3 files), 0.04 s

`#print axioms` on the 89 theorems of the five positive fixtures: **no
`sorryAx`** — 59 axiom-free, 14 `Quot.sound`, 15 `propext`, 1 both. Each check
was verified to *fail* when it should, including the `let` fixtures against the
pre-fix code and the escape sweep against the widened grammar.

## Limitations and open questions
- **Dependent positions are refused, not guessed**, each with a step-indexed
  message: dependent function argument and `∀` domain, binder types, `let`
  type/value, projection argument.
- `intro_ctx` recognised but unimplemented (T1 does not emit it); `at *` refused.
  Ordinary goals carry no `mdata`, so that fixture wraps the target.
- Recorded `lhs`/`rhs`/`to` must be **whitelist-dialect** terms. Round 4 widened
  the grammar to what Lean's pretty printer emits, so ordinary output passes
  through, but the dialect excludes `⟨…⟩`, `match`, `let`, `show … from` and big
  operators (`∑`), which a generator must re-render.
- Generator must emit raw child indices, **not** `conv`'s `arg n` numbering.
  `explicit_rw` also matches up to reducible defeq, succeeding where plain `rw`
  fails (`conditional_conv`); confirm before the post-pass collapses such steps.
- `ExplicitLean.lean` needs `ExplicitLean.ExplicitRw` wired in at merge.
