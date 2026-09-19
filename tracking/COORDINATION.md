# Coordination protocol (revised September 19, 2026)

The campaign is compilation-driven. Routine coverage work is delegated in large,
non-overlapping batches to Luna at maximum reasoning. A worker implements,
self-reviews, and tests its own batch; a separate adversarial reviewer is not a
routine merge requirement. The coordinator assigns ownership, triages failures,
may implement fixes, runs integration gates, and commits named files.

Independent focused review is reserved for trust-boundary changes: the patched
compiler/driver, recorder semantics, source-site accounting, translated-import
isolation, no-new-axiom checking, and acceptance-gate logic.

## Worktrees and ownership

- Main checkout: `/Users/ptsier/projects/explicit-lean`, branch
  `codex/search-free-mathlib-2026-08-31`.
- Each task `T<n>-<slug>` normally gets
  `/Users/ptsier/projects/explicit-lean-worktrees/T<n>-<slug>` on
  `task/T<n>-<slug>`, created from current main HEAD.
- Link only the pinned package cache:
  `mkdir -p .lake && ln -s /Users/ptsier/projects/explicit-lean/.lake/packages .lake/packages`.
  Never write into `.lake/packages`, run `lake update`, or mutate an installed
  toolchain.
- Every prompt names owned modules/files. Parallel batches must not overlap.
  Preserve edits already present in the shared checkout and never revert another
  worker's work.
- Large generated trees, oleans, and logs stay under `.lake` or a fresh private
  temporary directory. Frozen evidence snapshots remain read-only.

## Routine batch loop

1. Assign a coherent module group or failure class, explicit file ownership,
   and a small focused regression set.
2. Reproduce failures through the end-to-end renderer/compiler path. Prefer a
   general recorder or renderer correction when several sites have the same
   cause; use readable ordinary-Lean overrides only for genuinely exceptional
   proofs.
3. Compile early and repeatedly. The compiler is the primary oracle; do not
   spend a round on speculative adversarial or security concerns unrelated to
   an observed failure or a trust boundary.
4. Self-review the diff for soundness, readability, scope, adjacent original
   call comments, and accidental generated artifacts. Fix findings and rerun
   the focused checks.
5. Write `tracking/tasks/T<n>-<slug>/RESULT.md` with changed files, exact checks
   and runtimes, observed coverage, unresolved failures, and limitations. Commit
   coherent work on the task branch.
6. The coordinator integrates passing batches, runs the integration-level
   mechanical gates, and immediately dispatches the next disjoint batches.

A routine task does not create `REVIEW-*.md`. A trust-boundary task gets one
fresh focused reviewer after implementation; review should attack the changed
boundary and reproduce its controls, not restart broad historical sweeps.

## Simp-disabled certification compiler

The accepted private compiler is built once in the main checkout:

```sh
cd /Users/ptsier/projects/explicit-lean
python3 -B Toolchain/SimpDisabled/build.py --json
python3 -B Experiment/check_simp_disabled.py
```

Workers use that attested main artifact read-only while compiling absolute
worktree sources and outputs. For a focused compile with stock dependencies:

```sh
mkdir -p "$PWD/.lake/certified"
LEAN_PATH="$(lake env printenv LEAN_PATH | head -1)" \
  python3 -B /Users/ptsier/projects/explicit-lean/Toolchain/SimpDisabled/run.py -- \
  -R "$PWD" -o "$PWD/.lake/certified/Target.olean" \
  "$PWD/Mathlib/path/Target.lean"
```

The output must be absent before each run. Accepted translated-dependency checks
must instead use the strict translated-root `LEAN_PATH` produced by
`Experiment/translated_imports.py`; stock Mathlib roots may not satisfy an
accepted translated import. Certification fails on any executed stock
`simp`/`dsimp` engine call and on `sorry`/`sorryAx`, including indirect calls
from other tactics. Its failure diagnostics are work assignments, not reasons
to weaken the gate.

## Mechanical merge gates

For the affected modules and required dependents:

- every targeted source site is accounted for; missing, duplicate, shifted, or
  extra sites fail closed;
- each replacement is readable ordinary Lean and keeps the exact original call
  as an adjacent comment;
- generated and override code contains no forbidden simp-family tactic or
  hidden simplifier replay;
- simp-disabled certification emits fresh outputs with no `sorry`/`admit`;
- translated builds resolve imports from the translated root rather than stock
  Mathlib;
- theorem statements and computational semantics are preserved;
- the separate no-new-axiom comparison passes;
- focused regressions and required dependent compilation pass;
- `git diff --check` passes and only owned files are committed.

Static remaining-call audits and certification complement each other: syntax
accounting finds dormant source calls, while certification finds simplifier
execution hidden behind tactics such as `grind` or `norm_num`. Neither may be
reported as whole-tree coverage until the dependency-ordered whole tree passes.

## Escalate rather than broaden scope when

- a fix needs files outside assigned ownership;
- recorder meaning, source identity, import isolation, axiom policy, or another
  trust boundary must change;
- a theorem statement or computational behavior appears to change;
- a single focused build exceeds 30 minutes or 40 GB RSS on the Mac;
- the same failure remains after three materially distinct principled attempts;
- a proposed fix would hide unresolved calls, invoke the simplifier in product
  code, add an axiom, weaken validation, or introduce opaque replay payloads.

Ordinary elaboration, implicit arguments, coercions, and typeclass synthesis are
allowed. The recorder may run stock simp to observe it; translated product code
may not. See `AGENTS.md` for the governing rule.

The AWS authorization is closed and unchanged. This protocol covers local,
no-cost work only; no cloud host, paid service, deadline change, or credit use is
implicit.
