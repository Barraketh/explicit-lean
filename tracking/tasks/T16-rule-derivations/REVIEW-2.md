# T16 theorem-rule derivations — independent review 2

## Verdict: PASS

Commit reviewed: `a9c2d4e` (baseline `687daea`, REVIEW-1 `db46a88`).

The REVIEW-1 blocker is fixed. `rewriteOperational?` now follows stock
`Lean.Meta.Tactic.Simp.Rewrite.rewrite?`: `index := true` uses
`getMatchWithExtra` and priority order, while `index := false` uses
`getMatchLiberal`, priority order, and the stock `numArgs - lhsNumArgs`
extra-argument calculation. Both paths apply the same erased/rfl filtering,
system check, event-time derivation capture, and result recording. The two
indexed-mode update fixtures produce normalized-identical traces, including
the same theorem/step positions and derivation fields. The existing
`partial_app` fixture genuinely records `extraArgs: 1`; its rewrite and the
two new index-mode fixtures exercise the required extra-argument and lookup
paths. No generic simproc matcher or proof/term serialization was added.

The checker expectations retain exactly the four newly visible nested
user-congruence proposition events: two `ite` branch-context rewrites (`q →
True`/`q → False`) and two `dite` branch-context rewrites (`q → True`/`q →
False`). The `dite` false branch's following `not_false_eq_true` is retained
as its separate ordinary theorem event. All other skeleton fields remain
strictly checked; no checker relaxation or masking was introduced.

## Reproducible checks

- `lake build ExplicitLean.SimpTrace` — PASS (7 jobs; existing linter warnings
  only).
- `lake env lean test/SimpTrace/Fixtures.lean` — PASS (exit 0).
- `lake env lean test/SimpTrace/UnresolvedFixtures.lean` — expected exit 1;
  the existing unresolved classifications were reproduced.
- Fresh output inventory — 111 JSON files, 593 `rw` steps, 530 derivations;
  recursive scan found zero `proof`, `term`, `expr`, `hash`, `fingerprint`,
  `DAG`, or `payload` keys under `derivation`.
- `python3 -B Experiment/check_simp_trace.py` — PASS; all 74 fixture
  skeletons match and containment checks pass.
- `git diff --check 687daea..HEAD` — PASS.

