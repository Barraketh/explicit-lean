# Local verifier resumption plan

This plan covers the current bounded local batch and the separately recorded
AWS preparation below. The local phases do not authorize
`explicit-lean-cloud`, dispatch past an applicable absolute cutoff, or reuse
an AWS/campaign invocation nonce. A fresh nonce and output directory are
allowed for a future admitted local fixture or replay check after resource
gates pass.

## Phase 1: validate and publish the protocol fix

The changes in `Experiment/verify_simp_boundary_manifest.py`,
`Experiment/test_verify_simp_boundary_manifest.py`, and
`tracking/campaign.json` replay the producer's aggregate
`--defer-full-fallback` pass followed by one isolated
`--full-fallback-only` child per deferred source. They retain exact fallback
set equality, source and dependency-map identity checks, freshness/TOCTOU
checks, and fail-closed malformed, duplicate, unresolved, extra, and
unrequested marker handling.

Commit `5968c71` contains the reviewed verifier fix and tracker update; the
independent code review is complete and the commit is local and not pushed.
Completed validation: 39 verifier tests; 9 inventory-header controls passed on
2026-09-16 in the earlier producer probe before the final Python-only channel
change (they were not rerun); campaign status 9, supervisor 22, worker 33, and
translation-index 13 tests; Python compilation; and `git diff --check`. The
coordinator should include this plan as the remaining tracked Batch 1 file;
the `.lake` resume summary is ignored generated output and is not a commit
target.

## Phase 2: assess a full fresh local verifier replay

Before starting, re-authenticate the immutable input identities and confirm
that no producer or worker owns the output namespace. Use a fresh output
directory and fresh local nonce; never reuse an AWS/campaign nonce. The
preserved inputs currently hash as:

| Input | SHA-256 |
| --- | --- |
| `schema13-isolated-closed-manifest-v10.json` | `6d33d5eae0abdf7203040dcf24fccbbf5b9d8b999fe028841cb31c50a07b4dd3` |
| `index-header-dependency-map.json` | `eba4654477f16d81f870bf3b2cd15d0d9fe886357384d10f5e8a5f374ab95448` |
| `schema13-v10-handoff-scope-20260908T0640Z.json` | `ef724074c7ea36f1774ef56d13b1f2cff71ce827811810c1588a62b9df8bb2bf` |

The filesystem has roughly 101,481,976 KiB free, above the 12 GiB disk
reserve, but fresh available memory is 1,598,865,408 bytes, below the strict
12,884,901,888-byte verifier reserve. Do not launch the replay under this
telemetry; no complete local verification is claimed. Recheck resources before
any later attempt and stop closed if the reserve is unavailable.

The preserved historical manifest is immutable evidence. An offline structural
inspection against the current checkout correctly rejected its old
`implementationHashes` because the pending verifier source differs; this is a
stale-input identity mismatch, not evidence that the historical manifest was
repaired or accepted against the new code. A fresh manifest must be generated
and authenticated after publication before replay.

## Phase 3: bounded foundational proof preparation

This preparation can proceed independently of a full corpus verifier replay.
The first active target is the source-pinned `Mathlib.Data.Nat.Init`
`Nat.leRec_self` manual override in `Experiment/simp_manual_overrides.json`.
`Mathlib.Logic.IsEmpty.Basic` is a possible later target if its evidence stays
narrow; defer `Mathlib.Logic.Relation` because its runtime schema and replay
complexity need a separate design decision. Preserve kernel-checked
declarations, computational semantics, original tactic comments, and all
independent acceptance checks. Acceptance remains gated by the full verifier
checks and unchanged disk/memory reserves. Record each result as resource,
semantic, unsupported, or successful before considering importer expansion.

The Nat override and checker are committed together with this plan/tracker
update, with independent reviewer approval complete; remote publication is
still unpushed and runtime admission remains pending. It adds occurrence
`7063e52927a3778e` for the pinned Nat
source hash `6eac43b5c217af7e02be819026cdbba38b24810659d1fc1dc7d90d6f78c7d3e3`;
the override database has 17 entries across 15 modules and hash
`03cca0e6e35be3da7110855269767808f7b877f4eeb32ba142a80a836655e349`.
Lightweight AST/cardinality/source-range/hash/render/duplicate/missing/path
checks passed, and a corrected exact-theorem stdin Lean probe passed. An
earlier focused composition was launched before fresh resource admission and
failed because its initial replacement re-cased `n`; the replacement was then
corrected. Corrected composition, declaration-oracle, cold-dependency, and
full-checker Lean phases remain unrun because fresh memory is below reserve.
This is no module or tree acceptance, and coverage counts remain unchanged.

## Approved AWS run preparation

The user has now approved one fresh bounded AWS run: account `538639825139`,
`us-west-1`, one default-tenancy `r7i.4xlarge`-class Linux host with at least
128 GiB, one worker for at most 10 hours, a 12-hour host lifetime, and a $20
all-in cap. The final absolute cutoff is `2026-09-16T13:30:00Z`, materialized
from the fresh `2026-09-16T01:38:54Z` UTC clock with a small dispatch buffer
inside the 12-hour host bound. The prior September 13 authorization remains
closed and is retained as historical policy data. Do not provision until the
coordinator approves and publishes a clean full commit; do not reuse an old
AWS/campaign nonce or dispatch beyond the cutoff. Fresh local fixture nonces
remain permitted after resource admission.

The candidate checkout used by the worker is the clean published ref
`5145cfbff9ba1b2e99648c04691f8b92265f41a3`; the prepublication shared
checkout was HEAD `fed986f781b2d60da3c200fbe95b6a51503b33fa`.
The only permitted profile is the non-root `explicit-lean-pilot`; fresh STS
identity and all read-only AWS gates passed at 01:38:54Z. Live pricing is
EC2 $1.176/hour, gp3 $0.096/GB-month, public IPv4 $0.005/hour, subtotal
$14.492 and headroom $5.508. The controller template and live policy gates
pass. The sole worker was dispatched at `2026-09-16T01:48:02Z` as command
`64b1d21b-111f-4231-938f-0ed933663d58` on instance
`i-05bfce721923eb190` for run
`20260916T014201Z-a38ca0ed7740f01e72adebc45720898a`. State receipt:
`.lake/search-free-mathlib/aws-linux-pilot/runs/20260916T014201Z-a38ca0ed7740f01e72adebc45720898a.json`.
No translation, verifier result, coverage advancement, or terminal outcome is
claimed. Heartbeat `monitor-bounded-mathlib-linux-experiment` checks every 15
minutes and remains quiet unless the exact run changes; no redispatch, second
host, or cutoff extension is permitted.
