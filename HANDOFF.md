# Start here: search-free Mathlib

Handoff updated September 10, 2026. Working branch:
`codex/search-free-mathlib-2026-08-31`. Reviewed implementation: `ee30955`;
later documentation commits do not constitute new translation evidence.

## Objective and what works

Replace every executable source `simp` / `simp only` in pinned Mathlib with
search-free explicit applications. Preserve each original call as a comment,
public theorem statements and computational semantics. First achieve complete
coverage, then improve readability. `simpa`, `simp_all`, `simp_rw` and other
tactics' internal simplifier calls are outside this first milestone.

The active boundary translator records the stock call's result, emits checked
expression DAGs and explicit state changes, then independently compares replay
and completed declarations. Generated output uses `simp_engine_boundary_select`.
The tactic named `simp_engine_apply` elsewhere in the repository is the older
schema-27 operational replay engine; do not use it as the active product.

Current evidence: **83,627 calls inventoried; 529 successful module reports
covering 2,063 calls; 62 cached failures; no accepted complete translated tree.**
These are September 8 Mac results, rechecked at the report/hash level for this
handoff. A prior cold-certified cone covers just 39 modules and two calls.

The user merged all five supervisor commits from
`codex/v10-allocator-pressure-relief` into this branch. There is no remaining
merge needed for that supervisor. Its old `.lake` loader scripts are historical.

## First ten minutes

1. Read this file and [AGENTS.md](AGENTS.md). Read
   [tracking/STATUS.md](tracking/STATUS.md) if you need the detailed counts.
   You do not need the 700-line historical roadmap to begin.
2. Confirm the checkout and preserve unrelated changes:

   ```sh
   git status --short --branch
   git log -1 --oneline
   cat lean-toolchain
   ```

3. Run the inexpensive isolated Python checks from the repository root:

   ```sh
   python3 -B Experiment/check_campaign_supervisor_v10.py
   python3 -B Experiment/check_campaign_worker.py
   python3 -B Experiment/check_translation_index.py
   ```

   Latest results: 22 + 33 + 13 tests passed. These tests use temporary fixtures;
   they do not launch a corpus translation or establish Lean correctness.
4. Read `pilotCandidates` and `failures` in
   [tracking/handoff-snapshot.json](tracking/handoff-snapshot.json). It contains
   15 proposed pilot modules: five prior successes, five memory stops, and five
   foundational semantic/unsupported failures. Reproduction of a known semantic
   failure is a useful baseline, not a successful translation.
5. Prepare the bounded Linux pilot described below. Do not restart the old
   six-hour supervisor or September 8 automation as a startup step.

## Next deliverable: a reproducible bounded Linux pilot

The user authorized one AWS pilot in account `538639825139`, region `us-west-1`,
with a **$20 all-in ceiling**. The selected bounds are one single-purpose,
default-tenancy `r7i.4xlarge`-class **128 GiB Linux machine**, a 12-hour instance lifetime, a
10-hour worker, one worker total, and the 15-module sample. No resources are
currently provisioned. A fail-closed policy and repeatable procedure
are now in [tracking/aws-linux-pilot-policy.json](tracking/aws-linux-pilot-policy.json)
and [tracking/AWS-LINUX-PILOT.md](tracking/AWS-LINUX-PILOT.md), with a Linux
process sampler for separate Python and Lean RSS measurements. The controller's
mock checks, generated shell syntax, live read-only AWS gates, AWS template
validation and Amazon Linux systemd calendar parsing pass; full Linux
integration remains a host preflight. A
dedicated `explicit-lean-operator` IAM user has a console login, temporary
`AdministratorAccess` and no access keys. Its password
was changed, the invalid temporary password was removed from Keychain, and the
user explicitly chose to proceed without MFA. `explicit-lean-pilot` resolves to
this non-root user; `default` and `softmax` remain root sessions and must not be
used. AWS closed quota case `178915936800175` and raised the region's On-Demand
Standard quota to 32 vCPUs, above the 16 required. The replacement exact cutoff
is `2026-09-12T11:25:00Z`. The first CloudFormation request failed regional
schedule-property validation and created no resources. A second bounded stack
exposed a rejected guest timer timestamp and a false transport-success auth
proof; it was deleted before worker dispatch. A third bounded stack then booted
successfully and completed device login, but the hardened remote gate emitted
no proof because Amazon Linux Python rejected the valid trailing-`Z` campaign
deadline. No worker was dispatched; the stack was deleted after about fourteen
minutes and the instance and volume are gone. A narrow portable timestamp
parser fix passes focused local review. The user authorized autonomous bounded
retries without further per-revision confirmation. The pilot report remains
required before a long campaign or additional machines.

Before launch, close the publication gate. The exact one-pilot continuation is
recorded in both top-level tracker boundaries and remains fail-closed at its
absolute cutoff. Do not work around the guard or extend that time. The original
campaign-specific 25%/22% usage policy is obsolete by explicit user direction.
Fresh telemetry must still show ordinary account availability; unknown or
actually rate-limited availability stops dispatch, and credits must never be
bought or redeemed. The user's autonomous-run instruction removes the prior
per-revision confirmation step but does not relax any technical, cost or runtime
gate. Preparing and reviewing the pilot can proceed without paid resources. Do
not use the older `explicit-lean-cloud` host.
The Codex usage allowance and the AWS spending limit are separate budgets.

On the selected Linux host, recreate the pinned dependencies and native tools.
Do not copy Mac runtime artifacts or relabel Mac receipts as Linux evidence.
The controller pauses after provisioning for a Session Manager device-code
login and creates only a nonsecret, run-bound proof after `codex login status`
and the remote budget check pass. Do not copy `auth.json`, tokens, or Mac runtime
state to the host. The Mac index also
contains absolute paths, so plan a fresh Linux index/output namespace.
Inspect path/platform assumptions, generate/authenticate fresh invocation
inputs, and use a fresh output directory and nonce for each run. Start from the
small Python checks and focused Lean gates before attempting the pilot. Record
peak memory for Python and Lean processes separately, elapsed time, remaining
calls, and whether each failure is resource-related or semantic.

If the pilot is stable, fix the foundational failures and certify a translated
dependency slice before expanding. First targets:

| Module | Recorded diagnostic | Transitive importers |
| --- | --- | ---: |
| `Mathlib.Logic.Relation` | `activation_nonempty_aux_cache` | 7,700 |
| `Mathlib.Data.Nat.Init` | `boundary_forward_post_generator_mismatch` | 7,605 |
| `Mathlib.Logic.IsEmpty.Basic` | `boundary_sequence_multiple_helpers_unsupported` | 7,534 |

Importer sets overlap; one fix does not prove that all importers translate.
Keep the strict declaration/state checks. A small explicit proof override is
an option when it passes the same acceptance checks; do not weaken validation
to make a failure disappear.

## Memory decision already made

The override file is only 10.3 KiB. Its full supervisor overlay unnecessarily
retains all modules; sparse loading retained 1.21 MiB of Python objects versus
480 MiB. In isolated processes it saved about **559 MiB steady-state RSS**, but
both had a **1.42 GiB initial parsing peak**. No cleanup has been implemented.
This is an optional small follow-up, not a reason to delay the larger-machine
pilot or begin a broad memory rewrite. The actual peak memory of difficult
Lean compilations remains unmeasured. See the portable
[measurement](tracking/measurements/overlay-memory-2026-09-10.json).

## Code map: read only the part you need

| Work area | Entry points |
| --- | --- |
| Scheduling, admission, resumption | `Experiment/campaign_supervisor_v10.py`, `campaign_worker.py`, `campaign_budget.py`, `process_runner.py` |
| Inventory, identity and cache | `Experiment/simp_engine_boundary_corpus.py`, `translation_index.py` |
| Generate and validate one module | `Experiment/boundary_materialize_shard.py` |
| Record stock/applied boundary | `ExplicitLean/SimpEngine/Boundary.lean` |
| Generated replay and search barrier | `ExplicitLean/SimpEngine/Boundary/Tactic.lean`, `Apply.lean`, `NoSynthesis.lean` |
| Helper/state failure families | `ExplicitLean/SimpEngine/Boundary/RealizationCodec.lean`, `SequenceCodec.lean` and neighboring codecs |
| Independent semantic comparison | `Experiment/SimpEngineDeclarationOracle.lean` |
| Complete translated dependency validation | `Experiment/cold_certified_tree.py`, `cold_certified_module.py`, `translated_imports.py` |
| Manual proofs and overlay | `Experiment/simp_manual_overrides.json`, `manual_overlay.py` |

Lean is `leanprover/lean4:v4.32.2`, commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`. Mathlib is
`905b95818eb32af7874a58b427f50c1711a5e96c` (see `lake-manifest.json`). Current
formats are manifest schema 2, result artifact schema 5, selector schema 2,
module report schema 13. **v10** labels a campaign manifest/run generation, not
one of those schema versions.

For focused Lean work, begin with `Experiment/check_simp_engine_boundary.py`
and the relevant `check_simp_engine_*` fixture. Source and nested gates are
`check_simp_engine_boundary_source.py` and `check_simp_engine_boundary_nested.py`.
Those may build native tools and consume substantial resources; choose them
for a specific change after admission. Avoid a full rebuild just to orient.

## Evidence, portability and traps

On the original Mac, the checkout is `/Users/ptsier/projects/explicit-lean`.
Paths below are relative to that root:

- Database: `.lake/search-free-mathlib/translation-index.sqlite3`.
- v10 manifest: `.lake/week-2026-08-31/schema13-isolated-closed-manifest-v10.json`.
- September 8 handoff: `.lake/week-2026-08-31/schema13-v10-handoff-scope-20260908T0640Z.json`.
- Dependency map: `.lake/week-2026-08-31/index-header-dependency-map.json`.

The portable [snapshot](tracking/handoff-snapshot.json) records receipt/manifest
hashes, all 62 failure diagnostics and their local log hashes. `.lake` is
ignored by Git. **A fresh clone does not contain the underlying evidence.**
Use the summary to plan; obtain and verify selected source evidence when
reproducing a case, or produce fresh evidence. Missing files are not passing
checks. Do not copy the entire `.lake` tree or alter frozen evidence to make
paths work. [REPORTS.md](REPORTS.md) describes a historical S3 archive; current
v10 uploads and access were not verified during this handoff.

Two reporting traps matter:

- `campaign_failures.py` filters queue state `failed`, so it shows two historical
  reusable failures. The **62 v10 failures are cached on queued rows**. Use the
  supplied implementation-aware catalog until the reporting query is fixed.
- `campaign_status.py` can perform substantial manifest/evidence validation and
  computes identity from its current inputs. A different revision may invalidate
  historical cache counts. It is not the cheap startup status command.

No active attempts were present in the index at handoff. This is a dated
observation, not ownership of a live producer. Preserve existing locks and
lease checks. Keep local 12 GiB disk and memory reserves; separate resource
stops from semantic failures. Frozen reports are immutable, never reusable as
fresh invocations.

The 71 reusable calls in 40 modules remain a separate closure requirement.
Local macro lowering covers 22 definitions and 88 same-module invocations in
bounded work; canonical provenance and generated-source validation are pending.
The future behavior of exported tactics is still an open scope question: finite
recorded callers do not justify a claim of unrestricted equivalence. Do not
silently narrow the public API.

## Completion and document authority

A successful pilot removes uncertainty about execution resources; it does not
complete the project. Whole-Mathlib acceptance requires translated dependency
closure, zero remaining executable calls, preserved original comments,
statement/computational equivalence and final trust checks. Read the acceptance
list in [WEEKLY.md](WEEKLY.md) before asserting closure.

Use current user instructions, [AGENTS.md](AGENTS.md), this handoff and
[tracking/campaign.json](tracking/campaign.json) for active work. The old tracker
is archived byte-for-byte under `tracking/archive/`; its owners, next actions
and pending blockers are historical. `PLAN.md`, `simprocs.md` and the previous
README provide background, not a new batch assignment. Keep the concise
status, tracker and portable snapshot synchronized when new evidence arrives.
