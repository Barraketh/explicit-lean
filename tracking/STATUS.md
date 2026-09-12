# Search-free Mathlib status

Reviewed September 10, 2026, at code commit `ee30955`. Start with
[HANDOFF.md](../HANDOFF.md) for the next agent's first steps.

| Measure | Latest reviewed evidence |
| --- | ---: |
| Inventoried modules / source calls | 8,264 / 83,627 |
| Direct / reusable calls | 83,556 / 71 |
| Unresolved classifications | 0 |
| Direct-only / reusable-containing / no-call modules | 6,280 / 40 / 1,944 |
| Successful v10 module reports | 529 |
| Calls / variants in those reports | 2,063 / 2,227 |
| Direct-only modules without successful reports | 5,751 |
| Cached semantic or unsupported failures under the v10 identity | 62 |
| Accepted whole-tree modules / calls | 0 / 0 |

All 529 report hashes and summary flags were rechecked for this handoff. This
does not rerun Lean or all underlying evidence validation. The reports belong
to the September 8 Mac run; they are not fresh Linux or complete-tree evidence.
A historical cold-certified 39-module cone covers only two replaced calls.

The user merged the complete `codex/v10-allocator-pressure-relief` branch into
`codex/search-free-mathlib-2026-08-31`; the supervisor is now in this checkout.
The old loader scripts and separate supervisor worktree are historical evidence.
Fresh September 10 Python checks passed: supervisor 22, worker 33, index 13.

The last 90-minute production run produced zero successes and 19 memory stops.
The manual-overlay cleanup remains unimplemented; a controlled measurement
found about 559 MiB less steady-state RSS, with the same 1.42 GiB initial
parsing peak. It is optional cleanup, not a prerequisite for the next milestone.

## Next milestone

The bounded AWS/Linux pilot is authorized for account `538639825139` in
`us-west-1` with a $20 all-in ceiling. It remains exactly one 128 GiB
`r7i.4xlarge`-class machine, one worker and 15 modules spanning successes,
resource stops and semantic failures. The chosen bounds are a 10-hour worker
and a 12-hour instance lifetime; the estimated bounded subtotal is $14.492.
No AWS compute resources are currently provisioned. A dedicated
`explicit-lean-operator` IAM user has console login, temporary
`AdministratorAccess` and no access keys. Its password was changed, the invalid
temporary password was removed from Keychain, and the user explicitly chose to
proceed without MFA. `explicit-lean-pilot` resolves to this non-root user;
`default` and `softmax` remain root sessions and must not be used. AWS closed
quota case `178915936800175` and raised the On-Demand Standard quota to 32
vCPUs, above the 16 required. The replacement one-pilot continuation has the
exact `2026-09-12T11:25:00Z` cutoff. The first CloudFormation request failed
regional schedule-property validation and auto-deleted before creating any
resource;
fresh EC2 and volume queries confirmed nothing remains. Its exact authorization
hash is superseded. A second bounded stack exposed a rejected guest timer
timestamp and a false transport-success auth proof; it was deleted before
worker dispatch. A third stack booted cleanly and completed device login, but
the independent remote gate correctly emitted no proof because Amazon Linux
Python rejected the tracker's valid trailing-`Z` deadline. No worker was
dispatched. The third stack was deleted after about fourteen minutes; the
instance is terminated and its volume is gone. A fourth stack passed boot,
device login and every dispatch gate, but its sole worker command failed before
cloning because Amazon Linux's preinstalled `curl-minimal` conflicts with full
`curl`. A fifth stack passed package setup and cloned the exact revision, then
failed before toolchain setup because Session Manager supplied no `HOME` under
strict shell checking. Both stacks were deleted and their instances and volumes
are gone. A sixth stack pinned to `e4e55a5` passed boot, device login, all
dispatch gates, dependency installation, exact cloning, Lean 4.32.2
installation, the Mathlib cache fetch and the focused Python suites. It then
failed closed before corpus translation: the strict apply-only import-isolation
gate found a transitive path through `ModuleDataObservation` and Mathlib's
library-suggestion machinery to `Lean.Meta.Tactic.Simp.Rewrite`. Evidence upload
succeeded. The sixth stack was deleted, instance `i-0d38e287a8657a472` is
terminated, its volume is gone, and no AWS compute resources are currently
provisioned. The architectural fix is published at `96af00e`: the metadata
observer now reproduces the pinned suggestion calculations without importing
their broad Grind/simplifier closure, while exact extension identity, full
metadata comparison and cache-purity checks remain fail-closed. The unchanged
strict boundary probe, shared build, pinned differential probe and 41-case
declaration oracle pass locally. A seventh stack at exact authorization
`72ea005224408d2677818e722774909183c1bcca` is active as run
`20260912T011632Z-7bacaae91f731d6284e3a7a5d879481c` on
`i-0e82b3e083e49db5e`. Device login, the independent auth proof and every
dispatch gate passed. Sole worker `dcf05b97-f81d-4f98-972f-ade0afebd3c1`
passed Linux dependency/cache setup, the focused Python suites and the repaired
strict boundary gate. It generated the fresh 216,029,345-byte manifest with
SHA-256 `d09cd2daf8b7f11e61f96a6d2bd9c85e3268b0421a3b576ccdc352d3ed29473f`,
then failed closed with `ExecutionTimedOut`/137 exactly 3,600 seconds after SSM
execution began: the `AWS-RunShellScript` document retained its default one-hour
execution timeout. The independent verifier was killed with an empty output and
corpus translation never began. Recovery command
`1af740a7-1604-4706-91fb-0796cb35e42e` uploaded and independently hash-checked
the 10,871,427-byte AES256 evidence archive, hash, timeout record and run exit.
The exact stack was deleted; the instance is terminated, its volume is gone and
no AWS compute resources remain. The `2026-09-12T11:25:00Z` cutoff is unchanged.
Fix `d7f89c4` explicitly sets the document execution timeout to the lesser of the
12-hour host lifetime and remaining cutoff window, while preserving the nested
10-hour worker cap. The 11 controller mocks, generated shell syntax, Python
compilation, live document-schema check and diff validation pass. Eighth run
`20260912T023459Z-fe6336ea78d3eb918011662c49e8d838` is active at exact published
authorization `83e01f8ceba26e271fe96d1524755b5ff7d35dfb` on instance
`i-0f897f7d7146d9acf`. Device login and independent auth probe passed; sole
worker `d354a0e4-8709-4ccc-97b1-b37b4dafedae` is running with the document
execution timeout set to the 31,435 seconds remaining to the unchanged cutoff.
The nested worker caps remain unchanged. No translation result is claimed. The user
authorized autonomous bounded retries without further per-revision
confirmation. Fresh September 12 telemetry reported ordinary Codex work
available at 38%.
The user retired the former campaign-specific 25%/22% policy; unknown
availability or an actual rate-limit/spend stop still halts dispatch.

After the pilot, prioritize `Mathlib.Logic.Relation`, `Mathlib.Data.Nat.Init`
and `Mathlib.Logic.IsEmpty.Basic`, then cold-certify their translated dependency
slice. Reusable-call provenance and whole-tree acceptance remain separate gates.
Readability work follows complete explicit coverage.

## Evidence and reporting caveats

[handoff-snapshot.json](handoff-snapshot.json) contains portable counts, the
62-failure catalog, proposed pilot modules and hashes locating local evidence.
It is a review summary, not an acceptance certificate. `.lake` is git-ignored;
a fresh clone will not contain the database, manifests or report files.

Queue states are `succeeded=529`, `queued=5751`, `stale=5`, `failed=2`; no active
attempts were present when read. The seven stale/failed rows are historical
reusable cases. The 62 current v10 failures are **queued** and cached, so
`campaign_failures.py` reports only two old failures. The supplied catalog
queries by implementation identity as well as cache result. Importer counts
overlap and are prioritization hints, not counts of automatically unlocked work.

The old tracker is preserved byte-for-byte in
[archive/campaign-2026-09-02.json](archive/campaign-2026-09-02.json).
Use [campaign.json](campaign.json) for current state and
[REVIEW-2026-09-09.md](REVIEW-2026-09-09.md) for the full review and measurements.
