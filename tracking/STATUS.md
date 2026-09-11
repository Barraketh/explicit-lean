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

Prepare a bounded AWS/Linux pilot with one 128 GiB machine, one worker and a
15-module sample spanning successes, resource stops and semantic failures.
No AWS resources have been provisioned. Account/region, spending/runtime limits
and the replacement for the expired scheduling policy remain to be specified.
The current `campaign_budget.py` still rejects dispatch after September 8.

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
