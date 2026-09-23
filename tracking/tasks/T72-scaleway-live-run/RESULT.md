# T72 live Scaleway replacement run

Status at 2026-09-23T03:41:06Z: **STOPPED, COLLECTED, AND CLEANED UP** at the
user's request after the interim failure distribution showed that continuing
the same all-at-once recorder strategy was not useful. This is a partial-corpus
diagnostic result, not a whole-tree acceptance claim.

The user authorized a full run on Scaleway under a $20 total cap and left the
worker count and machine choice to the coordinator. The first preferred GP1-L
preflight found account quota 0/0 and created no resource. The launched
fallback uses exactly one `POP2-HM-16C-128G` x86-64 host in `nl-ams-1`, one
120 GB `sbs_15k` root volume, one flexible IPv4, and exactly two workers. No
second host is authorized or present.

## Cost and lifetime envelope

- Live provider compute price: EUR 0.824/hour.
- Twelve-hour estimate: EUR 9.89 compute, EUR 0.05 IPv4, EUR 0.25 storage,
  and EUR 2.00 contingency/other, for EUR 12.19 estimated all-in.
- Policy ceiling: EUR 17.00 and USD 20.00. At the pinned ECB rate of 1.1490
  USD/EUR, the EUR ceiling is USD 19.533.
- Instance lifetime is at most 43,200 seconds and worker runtime at most
  36,000 seconds. The immutable cutoff is 2026-09-23T09:50:00Z.
- A persistent guest systemd shutdown timer is active at the exact cutoff. A
  separate local deletion watchdog retries exact resource cleanup and confirms
  absence of the server, root volume, IPv4, and security group.

Pricing and lifecycle references: [Scaleway Instances pricing](https://www.scaleway.com/en/pricing/virtual-instances/),
[Instance pricing behavior](https://www.scaleway.com/en/docs/instances/reference-content/understanding-instance-pricing/),
[flexible IPv4 FAQ](https://www.scaleway.com/en/docs/instances/faq/), and
[ECB euro reference rates](https://www.ecb.europa.eu/stats/policy_and_exchange_rates/euro_reference_exchange_rates/html/eurofxref-graph-usd.en.html).

## Pinned inputs and launch state

- Source/worker commit: `1953b0721faf53b6a40adf8fadbd13bec20cfc7f`.
- Both independent database copies began at SHA-256
  `411d08771291e901988e5b9afd41a0fcc70d5d8d864e0843ce2b4a24808589f9`.
- Job 000: 2,978 modules; manifest SHA-256
  `1f02a8f4e7b1393ca17e8f202b553f3deeca437d2b5e63185cd7460b3daf1023`.
- Job 001: 2,979 modules; manifest SHA-256
  `6305e7c1dbc92671fa8239bb2f3691cb37cb4de1304f2f3104de92975c4ff823`.
- The two manifests are disjoint and cover the complete 51,322-row pending
  queue. Upload hashes were rechecked before dispatch.
- At 2026-09-22T22:43:48Z both authenticated worker processes were recorded
  running with distinct launch tokens and PIDs. Early read-only inspection
  showed each process actively compiling a module and committing per-module
  status rows.

The local supervisor and independent deletion watchdog have both been stopped.

## Live bootstrap findings

Before dispatch, live provider shapes exposed three fail-closed bootstrap
issues: an interrupted root-owned checkout directory, human-formatted systemd
timer output, and redirects/Lake barrel fetching during toolchain/cache setup.
Each stopped before job dispatch, received a focused regression fix, passed an
independent trust-boundary review, and was published before retry. The final
bootstrap verified the pinned Elan archive checksum, retrieved the pinned
Mathlib cache, and built `ExplicitLean.SimpTrace` plus
`ExplicitLean.ExplicitRw` successfully on the host.

## Stopped result and verified merge

The workers were stopped through their dedicated process groups after acquiring
an SQLite `BEGIN IMMEDIATE` writer barrier. Their intentional exit code was 143.
Both result archives, completion markers, database hashes, and SQLite integrity
checks validated locally before any provider resource was removed.

- Job 000 database SHA-256:
  `daf9d9d9047181f5ced9a63374fd450e82ce86449b1c1d101547d6a91fcfb0e2`.
- Job 001 database SHA-256:
  `63989bea4e0a47ee70fd06de2cfb575b1ab2b9e7cde4fef51d16c8f07b3a1b73`.
- Job 000 archive SHA-256:
  `df3ef4ba3fa371817812ff242c66d6ee99435d9401667a356872717087dab901`.
- Job 001 archive SHA-256:
  `9fd1722b5787bf078be3ee31111baaec2841acf26e6af9ec12d36b65b85bd96b`.
- The disjoint results merged 38,220 rows into a copy of the original database.
  The merged copy has SHA-256
  `6956d43570b0d16ce8a4c4a0dedcc8595a741c2d79c2cd862b6e8256c545b01d`
  and passes `PRAGMA integrity_check`.
- The original `mathlib-db.sqlite3` was not overwritten. Its SHA-256 remains
  `e573cd5b99fd901863bf4b31e4d6e52c4618ca40c48a5acab1d2aa55d9dc03ad`.

Merged row counts are: 2,661 `success`, 3,956 `noop`, 1,116
`render_failed`, 430 `compile_failed`, 30,057 `record_failed`, and 13,102
`pending`.

## `record_failed` diagnosis

The 30,057 count is command-row fanout, not 30,057 independent recorder
failures. A module is instrumented and compiled once with every selected source
`simp` call. Any exception from that compilation is copied to every selected
command in the module. The stopped corpus contains 2,867 such modules and 2,866
distinct stored error strings. Those 30,057 commands contain 44,865 source
`simp`/`simp only` sites.

The stored diagnostics are truncated, so category counts are lower bounds and
overlap. Unsupported replay classifications occur in 2,462 modules / 27,347
rows; validator or metavariable-state failures in 959 / 11,164; instrumented
source compile failures in 140 / 1,569; deterministic Lean heartbeat timeouts
in 169 / 1,357; and finalization identity mismatches in 4 / 10. The largest
specific classes are `unapplied_quantified_prop` (1,388 modules / 16,678 rows),
`unreplayable_rw` (1,091 / 13,475), `unassigned_explicit_argument` (755 / 9,851),
validator failures (582 / 7,064), and unknown metavariables (437 / 4,770).

The collected partial trace data makes the fanout especially wasteful. For
2,858 located failed-module manifests, 40,679 of 44,809 selected sites (90.8%)
already emitted raw JSON. Of these, 30,520 sites (68.1%) have no classified
`unresolved` marker. At command granularity, 19,061 of 30,013 mapped failed
commands (63.5%) have raw output for every contained site with no unresolved
marker. These are salvage candidates, not accepted successes: they still need
subset finalization, rendering, and stock compilation.

The next run should therefore not repeat module-wide all-or-nothing recording.
Finalize and render whatever per-site traces were emitted, assign failures only
to the affected sites/commands, and retry missing sites by recursive bisection
or per-command batches. Fix the high-frequency quantified-proposition,
rewrite-replay, explicit-argument, validation, and metavariable mechanisms
before resuming the 13,102 pending rows.

## Cleanup

The controller's first cleanup attempt failed closed before deletion because its
SBS verification helper received a policy fragment without `cli_profile` and
therefore attempted the disallowed/default CLI profile. The exact server was
then stopped and the four recorded resources were deleted through the dedicated
`newprofile` profile; no broad or inferred target was used. This controller bug
must be fixed and reviewed before another Scaleway run.

At 2026-09-23T03:41:06Z the exact Scaleway server
`490405d4-7393-4627-9e62-ad7ce964bd0d`, SBS volume
`e14abef1-b306-4d05-9bec-cad1036ca33a`, flexible IP
`d30663db-1d40-4308-9717-da89e6ad7c41`, and dedicated security group
`cc8e01ca-0ffc-4165-aac0-0ee028fcb89a` were each independently listed as
absent in project `c64a1b10-82b6-4587-803c-9e2702b6476e`, zone `nl-ams-1`.
No worker or watchdog screen session remains.
