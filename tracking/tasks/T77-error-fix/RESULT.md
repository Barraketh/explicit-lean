# T77 isolated recovery and pending-site run

Status: active local campaign. Implementation commit:
`79b2f6aa7f854f2a4ef6b06b0ba8e436c6d06682`.
Exact bulk-record/batch-compile fast path commit:
`78189c32636004d62e50b611e6f2c997456960ac`.
Subsequent reviewed mechanism commits:

- `4780f5a`: terminal hypothesis closes;
- `bf32f05`: atomic, evidence-preserving trace refresh;
- `4816f8a`: ordinary-Lean `change.to` printing;
- `7537456`: audit-gated T76 failure refresh;
- `251a659`: authenticated Lean tactic-syntax ancestry extraction groundwork.
- `16e32d5`: quantified proposition validation aligned with existing
  selected-redex `explicit_rw` replay.
- `ad3ed44`: self-delimiting generated exact-term closes.
- `edf2690`: exact path-tagged binder spines for dependent rewrite validation.
- `ac6a8a4`: authenticated source-application validation evidence.
- `82c33bf`: exact temporary term/universe metavariable snapshots.
- `273c4fb`: class-valued explicit-argument validator parity.
- `b676829` / `c0d2acd`: exact opaque-simproc attribution recovery.
- `aeec19c` / `a3128cb` / `02ba91e`: named zeta-delta replay as readable
  `change`.
- `f904265`: authenticated congruence-event roots and exact nested event-slice
  validation.
- `42d422d`: explicit failure-status-only merge refinement for audited retry
  databases.
- `70ed7b6`: projection reduction through WHNF-exposed constructor majors.

## Implemented controls and principled fixes

- `Experiment/isolated_trace_compile.py` now masks only an authenticated
  theorem/lemma body suffix after its top-level declaration assignment. Named
  arguments and top-level `let` assignments cannot be mistaken for the proof
  boundary. Explicit status retries archive the prior audit result.
- Existing successful replacements must be nonblank and proof-hole-free before
  they enter a compile baseline. Writable databases must be single-link copies
  inside the exact T76 jobs or T77 run roots; frozen snapshots, original
  databases, hard links, and empty manifests fail closed.
- `Experiment/retry_missing_traces.py` records missing source sites one at a
  time, reauthenticates resumed traces, compiles an unchanged baseline, and
  then compiles one full command replacement at a time. Manifest ownership,
  source hashes, command ownership, status transitions, and all database writes
  are checked transactionally.
- An unbounded module first attempts one exact multi-site recorder invocation.
  It accepts the result only if the source-site key set and full trace identity
  exactly match the request; any defect discards the entire batch and retries
  every site independently. Rendered commands likewise get one exact combined
  module compile; a failure falls back to isolation from the already-compiled
  baseline and accumulates only individually compiling commands.
- Module-absolute T22 `sourceArgs` spans are compared for exact equality with a
  canonical manifest derived from the pinned original source for every
  invocation record, then deep-copied and rebased to command-local Unicode
  coordinates. In-bounds wrong-argument spans and later-invocation tampering
  fail before rendering.
- The generated spelling `at []]` is rendered as `at [] ]`, which Lean parses
  as the empty rewrite path followed by the surrounding `explicit_rw` list
  close. Isolated command rendering now honors comment suppression.
- A proposed text/line-regex expansion of generic `<;>` was removed after
  review. Structural expansion remains limited to the existing parsed binary
  branch-spine contract; no heuristic syntax inference was accepted.
- A hypothesis-location close is emitted as the exact ordinary sequence
  `explicit_rw [...] at h; <recorded closer>`. Multiple or nonterminal closes
  remain refused. A real disposable retry compiled
  `Mathlib.Algebra.GroupWithZero.Basic.zero_pow_eq_zero` with its `@[simp]`
  annotation preserved and a 190-byte replacement.
- `change.to` is now printed as ordinary Lean in the captured local context,
  leaving implicits, instances, and universes to elaboration. Fresh real traces
  rendered `3` and `a + 0` and replayed successfully; authenticated term text
  is no longer lexically rewritten by the renderer.
- `--refresh-recorded` installs a durable shadow for the complete selected
  site set in one SQLite transaction before recording. Old bundle traces
  cannot re-enter after a failed, deferred, or interrupted refresh; prior
  evidence is archived. Exact recorder dictionaries reject Boolean/float key
  aliases and reauthenticate every invocation.
- Explicit render/compile failure retries may be selected from matching T76
  `isolated_trace_audit` evidence only when the row status and stage-specific
  trace state agree. Pinned source bytes and command hashes are still checked
  before work begins.
- The Lean syntax extractor authenticates the full module and exact site range,
  then reports the unique parsed `simp` ancestry and `<;>` child ranges. This is
  groundwork only: it performs no replacement and local macro syntax currently
  refuses the module rather than falling back to full elaboration.
- Quantified proposition rules now use the same contract in recording and
  replay: open the complete proof telescope, match the resulting proposition
  against the selected redex, and reject any binder that remains unassigned.
  The removed blanket rejection predated this `explicit_rw` capability. No
  inferred arguments or proof terms are serialized, and exact source-backed
  simp arguments retain their authenticated spelling.
- Generated named closes now use the closed `close [term]` form. Brackets end
  the term before a following unbulleted tactic, while the term still passes
  the existing whitelist, tactic-block rejection, strict elaboration, and
  pending-metavariable checks. Hypothesis closes use
  `explicit_rw [] then close [term]` after the hypothesis rewrite, keeping the
  same delimiter in every generated context. Legacy hand-written `exact term`
  remains accepted.
- Rewrite validation now records the exact ordered binder spine crossed by the
  simplifier, including dummy slots for nondependent arrows. Validation filters
  that spine by the selected redex path and fails closed on structural-depth
  mismatches instead of padding missing binders at the innermost end. This
  fixes interleaved dependent/nondependent binders such as the real
  `AlgEquiv.toLinearMap_apply` step in `map_div`.
- Direct source arguments retain an internal, nonserialized witness of the
  exact elaborated application spine joined to the registered source range.
  Explicit arguments already present in source are therefore validated before
  checking for unassigned binders; implicit and instance arguments remain
  ordinary elaboration. Term and universe metavariables cannot escape the
  recorder's local context. The renderer still emits only the authenticated
  source text. A bare conditional theorem remains valid only with its recorded
  proof-side trace.
- Events crossing a temporary metavariable depth now snapshot assigned term
  and universe metavariables, including local declaration and local-instance
  payloads. Unassigned child-depth payloads fail closed without changing the
  successful simplifier result; live outer-depth metavariables remain valid.
  This removes the false `unreplayable_rw:ne_eq` classification caused by dead
  metavariable identifiers rather than by a rewrite mismatch.
- LHS-only validation now matches `explicit_rw` for remaining class-valued
  explicit binders: ordinary instance synthesis must fill the exact binder,
  while an arbitrary explicit value binder still fails closed. Missing source
  statements also fail closed instead of being accepted.
- Opaque simproc theorem attribution now treats `usedTheorems` additions as
  candidates rather than causal proof. Each candidate must reproduce the exact
  observed before/after pair in an isolated diagnostic probe whose Meta, Simp,
  and recorder state is restored. Unverifiable enclosing changes remain visible
  genuine blockers instead of being falsely attributed to nested local rewrites.
- Named zeta-delta reductions now render as ordinary `change` steps at the
  recorded position. This covers local-definition unfolding such as `O₂` while
  retaining fail-closed rejection of a `name` field on beta, eta, projection,
  or iota reductions.
- Congruence and transport event slices are now recursively rooted in the
  exact selected expression. Cached provenance is rejected and recomputed when
  its root is stale, and exact no-op definitional events are omitted rather
  than retaining provisional positions that no longer identify a subterm.
- Projection reductions may expose the projection major by ordinary WHNF, but
  proceed only when it is a complete constructor application and the existing
  exact definitional-equality validation succeeds. Stuck structure variables
  continue to fail closed.

## Verified checks

- 19 isolated-compile focused tests.
- 25 per-site/batch retry focused tests.
- 30 per-site/batch/audited-refresh focused tests after the refresh extensions.
- 15 renderer regressions.
- 122 renderer/layout checks and 16 focused renderer regressions after the
  close and ordinary-term changes.
- 11 replacement-worker checks, including real recorder and Lean compile
  fixtures.
- Ordinary `change.to` recorder/render/replay fixtures, the SimpTrace build,
  T9 identity, and T22 source-argument checks passed.
- The syntax ancestry extractor passed seven focused checks, including a
  pinned `Mathlib.Logic.Basic` smoke and Unicode byte/scalar ranges.
- The quantified proposition recorder/render/replay fixture passed for a
  global theorem, quantified local `prop_true`, quantified local `prop_false`,
  and a theorem with an undetermined explicit value binder that simp refused.
  `test/ExplicitRw/Provenance.lean` independently compiled the existing
  selected-redex proposition cases. Independent trust review passed.
- The self-delimiting closer passed the ExplicitRw build, Basic and
  LocalHandles Lean fixtures, 116 renderer assertions, 16 focused renderer
  regressions, JSON validation, the no-simp-family audit, and independent
  trust review including a tactic-block rejection probe.
- The exact-binder-spine fixture passed nested `forall`, implication,
  existential, conjunction, and the copied `map_div` proof shape; `CacheFork`
  and the SimpTrace tactic build also passed. Independent trust review found no
  silent depth fallback.
- The authenticated source-application fixture recorded, rendered, and
  replay-compiled `mul_inv_cancel_left₀ ha`, `hf.eq_iff`, and
  `if_neg (not_le.mpr hx)` with their exact source spelling. Removing the proof
  side from a bare `if_neg` trace was rejected. The SimpTrace build and
  independent trust review passed; validator-only evidence does not occur in
  trace JSON.
- The event-snapshot build and focused fixture passed assigned term/universe
  freezing, unassigned child-depth term/universe rejection, valid outer-depth
  retention, LocalContext/LocalInstances preservation, direct `ne_eq`
  validation, and a real nested `div_self` side trace. Independent static
  review passed after finding and correcting two universe-specific liveness
  gaps.
- The class-valued explicit-argument fixture passed `iInf_pos`, direct
  fail-closed validation of an ordinary `Nat` binder, and the corresponding
  `explicit_rw` negative. The SimpTrace build and the source-application and
  exact-binder-spine regressions also passed.
- The opaque-simproc attribution fixture passed the real `cmpLE_swap` shape:
  the genuine nested rewrite by local `yx` remains in the trace, while the
  distinct enclosing match change is not mislabelled as `yx`. The fixture also
  verifies that attribution probes cannot leak metavariable assignments,
  `usedTheorems`, or side evidence into the next recorded event. The opaque
  wrapper remains an explicitly classified blocker pending a sound operational
  replay model.
- Named zeta-delta replay passed 122 renderer assertions and 16 focused
  renderer regressions. The trace contract and a recorder-shaped
  zeta-then-beta fixture now require the recorded `after` expression and render
  it as `change`; independent trust review passed. The added Lean fixture was
  statically reviewed but has not yet been compiled in the live checkout while
  the shared worker artifacts are in use.
- The congruence/root fix passed a private isolated build and real
  `CondDistrib` replay fixture, including memoized and nonmemoized duplicate
  `Nat.add_zero` controls. Independent trust review passed.
- The projection-WHNF fix passed the ExplicitRw build, definitional and
  negative fixtures, and compiled the exact historical
  `Mathlib.Algebra.Category.ModuleCat.Subobject` staged candidate. Independent
  static review passed.
- T9 trace identity tests and T22 source-argument tests.
- 316 pipeline checks excluding the unavailable historical T1/T2
  worktree-dependent site-count and end-to-end checks.
- `py_compile` and `git diff --check` passed for the changed implementation.
- Independent trust review passed the final database, manifest, transactional,
  source-provenance, and renderer boundaries.

## Real smoke evidence

The disposable database
`.lake/private/T77-error-fix-20260923/post-review-smoke/mathlib-db.sqlite3`
was copied from the stopped-run baseline. Four commands in
`Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne` were recorded
per site and stock-compiled as full-command replacements:

- ordinal 35: `compiled_success`, 519-byte replacement;
- ordinal 36: `compiled_success`, 463-byte replacement.
- ordinals 37 and 69: one authenticated two-site bulk recording and one
  combined candidate compile produced two further `compiled_success` rows.

All replacements are nonblank ordinary `explicit_rw`, contain no executable
`simp`/`simpa`/`dsimp`, and contain no `sorry`/`admit`. Database integrity is
`ok`. This is stock isolated compilation, not simp-disabled certification.

The disposable close smoke at
`.lake/private/T77-error-fix-20260923/close-smoke2/mathlib-db.sqlite3` also has
integrity `ok`; ordinal 63 of `Mathlib.Algebra.GroupWithZero.Basic` is a compiled
success with no executable simp-family or proof-hole token. Five separate
fresh-recording pp-all/change smokes reached independent recorder blockers
(`not_isEmpty_of_nonempty`, `Fin.succAbove_ne`, or `Std.le_refl`) and therefore
correctly persisted no replacement. They are not counted as successes.

The disposable validator-parity rerun at
`.lake/private/T77-error-fix-20260923/quantified-prop-smoke` freshly recorded
`exists_apply_eq_apply` without the former `unapplied_quantified_prop`
classification. The module advanced to independent explicit-argument and
position-validation blockers; it is not counted as a compiled success.
Database integrity is `ok`.

The previously failing staged
`Mathlib.Probability.Distributions.Exponential.hasDerivAt_neg_exp_mul_exp`
candidate was copied to the disposable `close-boundary-smoke` directory. With
only its three generated `then exact True.intro` closers changed to
`then close [True.intro]`, the full staged module compiled successfully. This
is focused parser-boundary evidence, not a newly persisted database success.

## Active pending run

Run root:
`.lake/private/T77-error-fix-20260923/pending-run-20260923`.

The four manifests are pairwise disjoint and cover 1,662 modules / 13,102
baseline-pending rows. Each worker has its own one-link database copy. Workers
000 through 003 are active in detached screen sessions, with no additional
shards permitted and a hard ceiling of six concurrent campaign workers.

Workers 000 and 001 were interrupted with targeted `SIGINT` after the fast path
passed review. Their SQLite transactions remained consistent; pre-restart
logs/completion/exit markers are preserved under `prebatch-79b2f6a` names.
Both resumed from their existing databases at the fast-path commit, reusing
already authenticated site traces and completed command results.

The `monitor-isolated-trace-compile` heartbeat now monitors both runs, validates
and merges into new copies, and then retries audited failures using only the
reviewed implementation.
It is forbidden from provisioning cloud resources or mutating any original,
baseline, or frozen database.

Whole-tree coverage and simp-disabled certification remain unclaimed.

## Named-zeta retry run

Run root:
`.lake/private/T77-error-fix-20260923/named-zeta-retry-20260923`.

Two additional local workers are active in `explicit-lean-zeta-000` and
`explicit-lean-zeta-001`. Their manifests are pairwise disjoint and their
union is exactly the 303 modules containing the 388 T76 rows classified as
`render_failed:reduction_has_name: zeta step`. Both writable databases are
copies of the validated T76 merged output and passed `PRAGMA integrity_check`.
The retry driver processes every `render_failed` row in each owned module so
that command compilation remains module-consistent. It selected 269 modules
with usable stopped artifacts; 34 manifest modules currently have no selected
artifact and must remain explicitly unprocessed unless a valid source bundle
is located. This brings the campaign to its hard maximum of six concurrent
local workers; no further shard may start while these are active.
