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
- `5439b11` / `3438e2a`: schema-scoped current step-level unresolved
  classifications.
- `43b953d` / `03190f9`: Lean-syntax-authenticated apply-all expansion with
  exact continuation semantics.
- `851dc5d`: two-premise nested-discharge queue-ownership regression.
- `b25c513` / `e106938`: named zeta replay by exact indexed local identity,
  including malformed-evidence rejection.
- `87adf90` / `014156a`: source-application binder inspection through
  definitional wrappers, with validator metavariable state isolated.
- `ad2ff5a` / `dcd2031` / `f183fdf`: self-delimiting ordinary Lean terms in
  `explicit_rw`, preserving exact source spelling and rewrite direction.
- `02125c2`: parsed-AST gates for generated-term elaboration extensions and
  executable proof-hole syntax.
- `306505e`: explicit regression for the historical module-to-command
  `sourceArgs` coordinate mismatch.
- `3c77e1f`: fail-closed ownership regression for sequential
  `all_goals simp` without authenticated `<;>` ancestry.

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
- Current step-level `unresolved` classifications are honored only while
  traversing the defined trace grammar. They keep the original call visibly
  unresolved instead of attempting an operational rewrite with no derivation;
  unrelated envelope/site metadata cannot suppress renderable work.
- Multi-invocation `<;>` sites are expanded from authenticated Lean syntax
  ancestry rather than line/text patterns. The site must have a unique
  right-operand owner, nested ranges and child roles must agree, overlapping
  simp sites are refused, and suffix tactics run under ordinary `all_goals`
  to preserve apply-all behavior even when a translated branch closes or
  creates goals.
- Named zeta-delta steps now carry the exact `LocalDecl.index` of the
  let-bound free variable and render as
  `zeta_local local_ref <index> at <position>`. Replay requires that exact
  free variable at the selected position, requires a let value, and verifies
  the replacement by definitional equality. Large, proof-bearing, multiline,
  or elided pretty-printed let bodies are diagnostic only and no longer become
  generated source. Malformed or contextual local evidence fails closed.
- Source-application binder inspection now WHNFs inferred function types at
  ordinary transparency, so definitions and projections expose their real
  telescope. Validation runs under `withoutModifyingMCtx`; explicit source
  holes and opaque or unresolved function types still fail closed.
- Generated complete terms are wrapped in the `lean_term(...)` parser so
  notation, arrows, joins, complements, `let`, and other ordinary Lean syntax
  cannot consume the surrounding `explicit_rw` grammar. Exact source terms
  are not globally normalized, including inside strings and comments.
- Modules used to elaborate generated `lean_term` syntax are inspected by
  Lean's parsed command AST first. Term syntax, term macros/elaborators,
  notation, extension-capable initializers, `run_cmd`, and parser recovery
  fail closed. Retry and isolated compilation also audit executable `sorry`
  and `admit` in the AST while ignoring documentation, comments, and strings.

## Verified checks

- 20 isolated-compile focused tests.
- 25 per-site/batch retry focused tests.
- 31 per-site/batch/audited-refresh focused tests after the refresh extensions.
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
- The apply-all implementation passed 8 syntax-extractor checks, 25 invocation
  checks, 14 focused renderer regressions, and the private Lean
  `ApplyAllExpansion` fixture. Independent review found and fixed both
  continuation-on-closed-goal behavior and the left-associated nested-`<;>`
  ancestry case.
- The unresolved-marker change passed 167 render/identity assertions and
  independent review. The review rejected and fixed an earlier overbroad
  recursive JSON search that could have treated decoy metadata as a step.
- Indexed-local zeta replay passed the private ExplicitRw build, positive and
  negative definitional fixtures, a fresh trace showing exact local index 4
  followed by beta, 126 renderer assertions, nested side/congruence rendering,
  and the no-simp-family audit. Independent trust review found and fixed a
  malformed-`local` legacy-fallback gap.
- A real `Finsupp.sum_sum_index` regression now records four rewrites with
  both ordered premise traces. This confirms current `82c33bf` suffix-owned
  side queues; historical T65/T76 side-mismatch JSON genuinely omitted the
  first premise and must be re-recorded rather than relaxed in the renderer.
- T9 trace identity tests and T22 source-argument tests.
- 316 pipeline checks excluding the unavailable historical T1/T2
  worktree-dependent site-count and end-to-end checks.
- `py_compile` and `git diff --check` passed for the changed implementation.
- Independent trust review passed the final database, manifest, transactional,
  source-provenance, and renderer boundaries.
- The term-boundary review passed 12 syntax-AST checks, 31 retry checks, 20
  isolated-compile checks, the grammar fixture, 17 explicit-rw fixtures, and
  the 156-theorem axiom audit. Its later escape sweep was interrupted and is
  explicitly not claimed.
- The historical `bad_source_span` control reproduces the T76 renderer bug:
  module-relative Unicode scalar offsets were applied to a sliced command.
  Current code performs canonical whole-source validation and a checked
  copy-only rebase; the focused controls and 30 retry checks passed.
- Historical binary `<;>` failures predate the reviewed parsed-AST path:
  current `cases l <;> simp` exposes exact left/right ownership and renders two
  leaves. In contrast, `ext; all_goals simp` has no `tactic_<;>` node, so the
  renderer still refuses rather than inferring goal ownership from record
  count. The private 29 invocation checks, 12 AST checks, and apply-all Lean
  fixture passed.

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

The authenticated proposition-source correction is integrated as `3fa2568`
with independent-review fix `654e660`. Fresh record/render/replay covers
`NeZero.ne _` and `Nat.zero_le _`; ordinary undetermined explicit binders,
mismatched propositions, and both declaration/source-value attempts to use
`True.intro` as false-proposition evidence fail closed. A fresh isolated build
of the integrated main passed both target builds and the focused source and
quantified-proposition checks.

The apparent `EventMVarSnapshot` regression was a stale fixture rather than a
recorder defect: identical definitional before/after expressions are
intentionally elided before the depth gate. Commit `00b83af` uses
definitionally equal but structurally distinct controls and directly verifies
MetaM term/universe assignability at enclosing and child depths. The private
SimpTrace build, direct fixture, and checker pass.

`Mathlib.Order.Copy` ordinal 11 establishes one genuine blocker. Its dependent
proof argument changes from `eq_le : le = LE.le` to the transported
`eq_le ▸ eq_le : LE.le = LE.le`; the old JSON pretty-printer elides that
`Eq.ndrec` cast. Ignoring proof terms would not prove the enclosing
propositions equal. No relaxation was integrated: this class needs fresh
in-process typed dependent-congruence evidence and an independently reviewed
replay design. The reproduction is documented at `d7bf031`.

A second genuine blocker remains for a bare local `Function.LeftInverse`
hypothesis. Ordinary `explicit_rw [h]` compiles, but the safe recorder checker
rejects an unassigned explicit binder. Trusting only the typed local snapshot
would be unsound: an unrelated quantified local can present the same shallow
application shape. No bypass was integrated; the fix requires sharing the
replayer's exact matching and metavariable-closing semantics.

Sequential `all_goals simp` without `<;>` ancestry is also a genuine source
ownership blocker. Existing invocation records do not authenticate which
generated proof belongs to which goal; matching the number of records to the
number of goals would be a heuristic and remains rejected.

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

The old whole-file proof-hole regex has produced four known module-level
false positives in this run: `Mathlib.Order.Grade` and
`Mathlib.RingTheory.Extension.Presentation.Submersive` use the English word
`admit` in documentation, while
`Mathlib.Probability.Independence.Integration` has explanatory `sorry` tokens
inside a fenced documentation example. `Mathlib.Tactic.ComputeDegree` says
that its tactics "admit a `!` modifier" in module documentation. Their owned pending rows remain
unprocessed and will be retried after merge under the reviewed executable-AST
audit; they are not Lean failures.

The `monitor-isolated-trace-compile` heartbeat now monitors both runs, validates
and merges into new copies, and then retries audited failures using only the
reviewed implementation.
It is forbidden from provisioning cloud resources or mutating any original,
baseline, or frozen database.

Whole-tree coverage and simp-disabled certification remain unclaimed.

## Reviewed exact-source and success-postcondition extensions

The exact-source replay path is now integrated through `f008408` after an
independent review found that the first shared-matcher implementation could
accept a bare local rule whose explicit proof argument had not been persisted.
The reviewed mechanism snapshots the exact parser-term elaboration with its
term and universe metavariables abstracted, reopens that closed snapshot only
inside validation, and uses the same matcher and closer as ordinary
`explicit_rw`. Source-backed trace JSON contains neither reconstructed
arguments nor validator-only terms. A bare local rule requiring a proof now
replays only with its ordered typed side evidence; missing, reversed, reused,
or wrongly typed evidence fails closed, and validation cannot assign caller
metavariables. The private SimpTrace build and focused local/global/method/
implicit application record-to-render-to-compile fixtures passed. The NeZero
fixture remains unrun because its pinned Cyclotomic dependency olean is absent;
no broad dependency build was started.

Successful replacement persistence is guarded through `756e105`. Lean's AST
must show that every owned successful command has no executable direct
`Lean.Parser.Tactic.simp` node. Original database command kinds and byte ranges
must exactly match the parsed original module, the candidate source must be
exactly reconstructed from the authenticated replacement map plus recorder
import, and batched parser responses are bound to request IDs. Aesop `simp`
configuration is not misclassified as a direct tactic. Parser recovery and
unclassified extension contexts fail closed. Six parser-free identity attacks
and all 31 retry tests pass; 15 job tests pass with a synthetic in-memory
inventory. A real-parser jobs sweep was stopped after two tests because its
large `lean --run` processes competed with the six live corpus workers; it is
not claimed complete.

The validated named-zeta database contains 37 success rows with 40 textual
simp-family findings. Lean AST classification identifies 26 rows / 28 direct
`simp` sites, 9 rows / 10 Aesop-configuration-only findings, and 2 rows whose
module parser context refuses recovery. No row was mutated. The reviewed
new-copy retry path is integrated through `429982c`: it AST-selects only owned
direct `simp` nodes, is capped at eight modules / 32 rows, reauthenticates
source and candidate identities before and after copying, archives prior
success evidence transactionally, and makes terminal failures visible. An
independent review found and fixed a provenance gap where SQLite WAL state
could have escaped the pinned main-file hash; the source is now immutable
read-only and any WAL, SHM, or journal sidecar refuses the copy. The residual
retry is ready but has not launched because all six campaign process slots are
occupied.

The module-risk gate is hardened through `7f96f6f`. Review reproduced a real
bypass: a command-category elaborator could call `Lean.Meta.simp` during
candidate compilation while the older term-only classifier returned `ok`.
The reviewed gate now refuses executable command/tactic/term/macro/do-element
macro and elaborator registrations, parser registration attributes, and the
specialized registered callback attributes exercised by Lean. Passive syntax
declarations and passive quoted attribute syntax remain allowed. Independent
review found and fixed missed parser and inductive-elaborator attributes plus
two false-positive name matches. The focused seven-test extension suite passes
on main. The full extractor suite, whose setup imports all Mathlib, was
interrupted rather than competing with the six corpus workers and is not
claimed.

A read-only structured-evidence sweep identified two source-application retry
classes likely unlocked by `f008408`: 83 current failed site records with
exact `missing_source_application` classification and manifest/source-argument
alignment, plus 22 `unassigned_explicit_argument` command rows whose raw step
is tied to the exact simp-lemma `argId`. Twenty-five looser records were
excluded, and no `missing_local_evidence` target was established. These counts
are only a moving snapshot; the selector and six-way success anti-join must be
rerun against each terminal owner database before dispatch, so no manifest or
coverage claim is frozen from this snapshot.

At `2026-09-23T15:03:13Z`, the still-running pending shards had moved 3,635
owned rows to success, 651 to noop, 2,225 to record failure, 418 to render
failure, and 696 to compile failure. The two broad failure-retry shards had
added 563 successes: 217 from compile failure, 58 from record failure, and 288
from render failure. These are nonterminal snapshots, not merged results. The
current max-retry module errors are
`Mathlib.Algebra.Group.UniqueProds.Basic`,
`Mathlib.Algebra.Homology.Factorizations.CM5a`, and
`Mathlib.Algebra.Module.Injective`; their full-module parser reports recovery,
so they remain deliberately unprocessed rather than weakening the AST gate.

## Named-zeta retry run

Run root:
`.lake/private/T77-error-fix-20260923/named-zeta-retry-20260923`.

The two historical workers are terminal. Their manifests are pairwise
disjoint and their
union is exactly the 303 modules containing the 388 T76 rows classified as
`render_failed:reduction_has_name: zeta step`. Both writable databases are
copies of the validated T76 merged output and passed `PRAGMA integrity_check`.
The retry driver selected 269 modules with usable stopped artifacts; 34
manifest modules had no selected artifact. It produced 652 new stock-compiling
successes in 192 modules and 1,391 changed rows overall. Job 001 exited 1 only
because the historical whole-module regex interpreted the English word
`admit` in three documentation comments as a proof hole; this was not a Lean
failure and is corrected by the reviewed AST audit.

The validated merge is
`.lake/private/T77-error-fix-20260923/named-zeta-retry-20260923/mathlib-db-named-zeta-merged.sqlite3`
with SHA256
`e2ee5cc13e5073e8f96c3c2a086e0f3c57aec556bd8e97d9c15ba623d2c54312`.
It was made from a new copy; all input databases and the T76 source remain
preserved.

## Fresh all-failure retry run

Two fresh workers run from the isolated checkout
`.lake/private/T77-max-retry-20260923/worktree` at reviewed HEAD
`02125c24dd29ba9a02169be62aa78a27c5347ad1`. Their disjoint manifests cover
all 3,553 modules containing 20,123 `record_failed`, `render_failed`, or
`compile_failed` rows in the validated named-zeta merge. Audit gating selected
1,362 modules / 9,094 rows for worker 000 and 1,388 modules / 9,145 rows for
worker 001.

Both workers use `--refresh-recorded --retry-failed`: every selected source
site is freshly recorded before rendering, rather than reclassifying stale T76
JSON. This exercises the reviewed source-span rebase, ordinary-term printer,
indexed-local zeta evidence, binder inspection, AST term-elaboration gate, and
executable proof-hole audit. Together with the four pending workers, this is
the hard ceiling of six concurrent campaign workers; no additional worker may
start.

The first launch was stopped before useful progress when staged recorder files
reported that the isolated build lacked the `ExplicitLean.SimpTrace` umbrella
olean. It persisted no replacement successes and both databases retained
integrity `ok`; the exact failed-attempt logs are preserved as
`prebuild-missing-simptrace.log`. After building the missing umbrella module,
one preserved staged recorder file compiled successfully. Both workers then
restarted on the same databases with `--retry-failed`; a live module has since
freshly recorded seven sites and stock-compiled one command successfully.
