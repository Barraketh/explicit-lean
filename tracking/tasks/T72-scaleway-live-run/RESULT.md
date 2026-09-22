# T72 live Scaleway replacement run

Status at 2026-09-22T22:44:16Z: **RUNNING**. This is an operational launch
record, not a result or whole-tree acceptance claim.

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

The local supervisor remains attached as `explicit-lean-scaleway-supervisor`.
The independent deletion watchdog is `explicit-lean-scaleway-watchdog`, and
the quiet 15-minute heartbeat is `monitor-scaleway-simp-replacement-run`.

## Live bootstrap findings

Before dispatch, live provider shapes exposed three fail-closed bootstrap
issues: an interrupted root-owned checkout directory, human-formatted systemd
timer output, and redirects/Lake barrel fetching during toolchain/cache setup.
Each stopped before job dispatch, received a focused regression fix, passed an
independent trust-boundary review, and was published before retry. The final
bootstrap verified the pinned Elan archive checksum, retrieved the pinned
Mathlib cache, and built `ExplicitLean.SimpTrace` plus
`ExplicitLean.ExplicitRw` successfully on the host.

No completion counts, collected result hashes, cleanup success, or whole-tree
acceptance are claimed here. Those fields must be added only after both workers
finish, the archives validate locally, and provider resource absence is
confirmed.
