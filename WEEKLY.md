# Search-free Mathlib: August 31–September 8, 2026

> Historical campaign brief. The deadline has passed and the goal is incomplete.
> Start with [HANDOFF.md](HANDOFF.md) for September 10 status and next work.
> The acceptance criteria below remain applicable. The original launch sequence,
> local-only campaign scheduling and ownership statements describe that earlier
> run; current AWS preparation and unresolved launch limits are recorded in the
> handoff and [campaign tracker](tracking/campaign.json).

## User objective and authority

By the user's return on September 8, deliver a buildable version of pinned
Mathlib in which every executable source `simp` / `simp only` occurrence is
replaced by a deterministic, search-free explicit alternative. Preserve the
original call as a comment. First achieve complete explicit coverage; then
find shared patterns and normal forms that make the output maximally readable.
If finished early, extend the same approach to other common search-based tactics.

This objective supersedes earlier implementation choices in `PLAN.md`.
The user grants broad implementation latitude, parallel delegation, and routine
reviewed commits. Work only on this Mac; explicitly ignore explicit-lean-cloud.
Do not purchase compute, API credits, or usage resets. The Mac and app will stay
running. The deadline is conservatively treated as September 8 at 00:00 Pacific
until a more precise return time is supplied; final verification should finish
on September 7.

## Acceptance

1. Account for every source occurrence in the pinned corpus. Executable and
   reusable executable calls are candidates; genuine syntax data remains data.
   Keep source ownership distinct from execution-module identity.
2. Retain original calls as comments adjacent to replacements, including nested
   calls consumed by an outer replacement. Preserve source provenance.
3. Generated alternatives do not invoke the simplifier, simprocs, dischargers,
   or tactic search. Kernel checking, deterministic reductions, and checked
   transports are permitted. Never introduce sorry/admit or new axioms.
4. Preserve public theorem statements and computational meaning. Validate the
   translated dependency tree, not only isolated files against stock imports.
   Explicitly justify any special equivalence policy for rewritten metaprograms.
5. A final complete build, remaining-call audit, and semantic/trust checks must
   agree with the durable occurrence index and immutable report manifest.
6. After complete explicit coverage, improve readability using measured common
   patterns and canonical forms. Do not conceal unsupported calls behind wrappers.

## Execution and budget

- Coordinator: this local task, with Luna subagents for bounded independent work.
- Branch: `codex/search-free-mathlib-2026-08-31`, based on `ad107b0`.
- Use fix-review cycles and escalate unexpected complexity; coordinator integrates.
- Use the entire remaining current weekly Codex allowance if useful.
- User-stated reset: September 7. Maximum usage from the next allowance: 25%.
  Use account rate-limit telemetry, not raw token counts, as the budget unit.
  Stop new dispatch at 22% in the new window, leaving headroom for running work
  and final reporting; tighten concurrency/batch size near the threshold.
  If fresh telemetry is unavailable after September 7, stop costly work.
- Keep recurring wakeups small when a batch is already running. Avoid repeated
  expensive polling, duplicate work, and starting work that cannot finish within
  the remaining usage margin. Pause the campaign when its allowance is exhausted.
- Checkpoints and pending work live in `tracking/campaign.json`; the SQLite index
  and generated artifacts live under `.lake/search-free-mathlib`.
- Pause recurring continuation after the September 8 handoff. Do not claim the
  goal complete unless acceptance is actually satisfied.

## Work sequence

1. Establish durable tracking, fresh usage checks, and recurring continuation.
2. Fix the two review findings: input-manifest cleanup and antiquotation scope.
3. Build a SQLite occurrence/result index, stable dependency hashes, incremental
   scheduling, and compiled Lean tooling to reduce repeated frontend startup.
4. Preserve originals as comments, then run expanding deterministic module shards.
5. Resolve source/execution identities and reusable metaprogram semantics; expand
   coverage without silently exempting hard cases.
6. Assemble and validate the complete translated tree. Fix every remaining case.
7. Mine common explicit forms and simplify presentation without adding search.
8. If complete early, inventory and prioritize other common search-based tactics.

## Starting evidence

The prior review found two reproduced P2 bugs and no failures in the build,
focused boundary/source/nested gates, or protocol validators. The full regression
and corpus suites were not rerun. The old 83,425-occurrence diagnostic manifest
is obsolete under the current execution-role contract and must not be counted
as current closure. See `.lake/project-review-20260831/review.md` for reproductions.

The implementation has five representative Mathlib modules in its documented
boundary gate (66 occurrences) plus the verified nested Action module (10).
These bounded results do not establish corpus completion.
