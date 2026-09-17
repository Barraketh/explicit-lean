# T16 theorem-rule derivations — independent review 1

## Verdict: MAJOR

Commit reviewed: `687daea52864a56632205773bd1a7ad9ec766652` (baseline
`9600009`).  The term-free payload boundary and the event-time matcher design
are substantially sound, but the replacement matcher does not preserve a
stock simplifier configuration that is part of the public `simp` behavior.

## Blocking finding

`ExplicitLean/SimpTrace/Recorder.lean:477-498` implements theorem lookup with
`tree.getMatchWithExtra e` unconditionally.  Stock
`Lean/Meta/Tactic/Simp/Rewrite.lean:207-272` branches on
`(← getConfig).index`: `true` uses `getMatchWithExtra`, while `false` uses
`getMatchLiberal` and its distinct candidate/argument path.  Consequently a
trace call with `(config := { index := false })` is executed by a different
matcher than stock simp.  This violates the required semantic-parity
contract even though the ordinary indexed fixtures pass; it needs an
implementation decision/fix before acceptance.

The operational core also differs from stock in smaller ways worth retaining
for follow-up review: it always constructs/checks `proof` before applying the
`implicitDefEqProofs` fast path, and checks `rhs` before `addExtraArgs` rather
than checking the final result expression.  These are not the verdict driver,
but they make the unconditional parity claim unsafe.

## Four user-congruence count differences

These are truthful nested operational events, not double counting.  A baseline
run of `UnresolvedFixtures.lean` at 9600009 with
`-Dtrace.Meta.Tactic.simp.rewrite=true` emitted the same stock events that T16
now records:

* `user_congr_ite` branch side 1: the contextual `a✝ : q` rewrites `q → True`;
  branch side 2: it rewrites `q → False`.
* `user_congr_dite` branch side 1: `h : q` rewrites `q → True`.
* `user_congr_dite` branch side 2: `h : q` rewrites `q → False`, followed by
  `not_false_eq_true`.

The old recorder’s output has zero/one branch steps at those locations because
its attribution wrapper missed repeated theorem firings; stock debug output
confirms that the T16 events occur during actual simp execution.  The checker
therefore needs expanded skeletons (or a deliberate checker mode for these
newly visible nested events).  This is a checker/documentation gap, not an
implementation double-counting finding.

## Representative evidence

* `lake build ExplicitLean.SimpTrace`: PASS (7 jobs; only existing linter
  warnings).
* Fresh `IsEmptyBasicTraced.lean`, `FunctionBasicTraced.lean`, and
  `LogicBasicTraced.lean`: expected nonzero unresolved classifications were
  reproduced.  `leftTotal_empty` records `prop_to_true` plus an `instance`
  binder; `Decidable.em` records `prop_to_true` plus an `instance` binder;
  source `if_neg` and source/local `Function.IsPartialInv.eq` record
  `sourceArg: 0` and are visibly classified unresolved for their unassigned
  explicit argument; reverse/Iff/direct-Eq examples record the expected
  direction/preprocess classes; failed discharge remains classified (including
  `user_congr_dite`’s unresolved `¬q` close).
* T16 fresh `test/SimpTrace/meas_out`: 111 JSON files, 593 `rw` steps, 530
  derivations; a recursive payload scan found zero `proof`, `term`, `expr`,
  `hash`, `fingerprint`, `DAG`, or `payload` keys under `derivation`.
* `python3 -B Experiment/check_simp_trace.py`: FAIL with exactly four known
  side-step count differences, listed above; no position/type mismatch.
* `git diff --check 9600009..687daea`: PASS.

## Contract review

Derivations are serialized as names, ordinals, strings, positions, counts and
binder/discharge classifications; no proof/term `Expr` is serialized and no
post-hoc proof decompilation is used.  Fixed redex positions and extra-argument
counts reproduced in the prefix-application fixtures (for example
`Option.orElse_eq_orElse` with `extraArgs: 2`).  The nested discharge frames
observed in the fixtures correspond to successful discharge calls.  Generic
simproc handling remains on the existing instrumented path; no generic
simproc matcher was added.

**Gap classification:** MAJOR — matcher configuration parity is missing;
checker expectations additionally need expansion for truthful nested events.
