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
No AWS compute resources have been provisioned. A dedicated
`explicit-lean-operator` IAM user has console login, temporary
`AdministratorAccess` and no access keys. Its password was changed, the invalid
temporary password was removed from Keychain, and the user explicitly chose to
proceed without MFA. `explicit-lean-pilot` resolves to this non-root user;
`default` and `softmax` remain root sessions and must not be used. AWS closed
quota case `178915936800175` and raised the On-Demand Standard quota to 32
vCPUs, above the 16 required. The one-pilot continuation now has the exact
`2026-09-12T11:00:00Z` cutoff. The first CloudFormation request failed regional
schedule-property validation and auto-deleted before creating any resource;
fresh EC2 and volume queries confirmed nothing remains. Its exact authorization
hash is superseded. A clean published fix, explicitly identified by its new full
hash, remains the final pre-provisioning gate. Fresh September 11 telemetry
reported ordinary Codex work available at 23%.
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
