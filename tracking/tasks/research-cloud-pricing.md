# Cloud pricing research: Lean 4 + Mathlib build machines

Date: 2026-09-16. Read-only research (listing/search/describe/pricing only; nothing created, started, or modified).

Requirements: Linux x86_64, >= 8 vCPU (16 preferred), ~128 GB or ~256 GB RAM, >= 200 GB disk, sessions persist for days.

**Source key:** `[CLI]` = from the provider CLI. `[WEB]` = from a public web page / public pricing endpoint, NOT the CLI. `not obtained` = could not be retrieved; never guessed.

EUR->USD conversion uses 1 EUR = 1.1537 USD (frankfurter.dev, 2026-09-16) `[WEB]`. Scaleway list prices are quoted in EUR by the CLI; USD columns are converted and so carry FX risk.

$/day = $/hr x 24. $/30 days = $/hr x 720.

---

## Tier 1: ~128 GB RAM

| Provider | Instance type | vCPU | RAM | Disk included | $/hr | $/day | $/30d | Storage cost note | Availability observed | Expiry / persistence |
|---|---|---|---|---|---|---|---|---|---|---|
| Vast.ai | offer 50282163, 1x GTX 1070 Ti, Xeon E5-2650 v2 | 32 host / **16 effective** | 128 GB | 537 GB | **$0.0671** | $1.61 | $48 | $0.06/GB-mo `[CLI]`, incl. in dph_total | yes — Quebec, CA; rentable, on-demand (`is_bid=false`), reliability 0.9969 | On-demand, no fixed expiry; host can still stop/retire the machine. Not an SLA-backed cloud. |
| Vast.ai | offer 29431161, 1x RTX A2000, EPYC 7282 | 32 host / 16 effective | 128 GB | 1508 GB | $0.0690 | $1.66 | $50 | $0.333/GB-mo `[CLI]` | yes — Norway, NO; on-demand, reliability 0.9974 | same as above; modern EPYC cores |
| Scaleway | **GP1-L** | 32 | 128 GiB | 559 GB local NVMe | $0.8932 (€0.7742) `[CLI]` | $21.44 | $643 | Local volume included; no extra block storage needed | yes — available in fr-par-1/2/3, nl-ams-1/2, pl-waw-1/2 `[CLI]` | No expiry; runs until deleted. Stopped instances still bill for storage. |
| Scaleway | POP2-HM-16C-128G | 16 | 128 GiB | 0 (block only) | $0.9506 (€0.8240) `[CLI]` | $22.82 | $684 | + block storage: €0.000130/GB/hr 5K IOPS ≈ €0.0949/GB-mo; 15K ≈ €0.1292/GB-mo `[WEB]`. 200 GB 5K ≈ €19/mo (~$22) | yes — fr-par-1/3, nl-ams-1/2/3, pl-waw-2/3; scarce in fr-par-2 `[CLI]` | No expiry; runs until deleted |
| Scaleway | PRO2-L | 32 | 128 GiB | 0 (block only) | $1.0320 (€0.8945) `[CLI]` | $24.77 | $743 | as above | yes — fr-par-2/3, nl-ams-2/3, pl-waw-1/2/3; shortage in fr-par-1, nl-ams-1 `[CLI]` | No expiry |
| AWS | r6i.4xlarge (us-west-1) | 16 | 128 GiB | 0 (EBS only) | $1.1200 `[WEB]` | $26.88 | $806 | gp3 $0.096/GB-mo us-west-1 `[WEB]`; 200 GB = $19.20/mo | not obtained (no live API access — see note) | No expiry; EBS persists across stop/start. Stopped instance bills EBS only. |
| AWS | r7i.4xlarge (us-west-1) | 16 | 128 GiB | 0 (EBS only) | $1.1760 `[WEB]` | $28.22 | $847 | gp3 $0.096/GB-mo `[WEB]` | not obtained | No expiry. Matches the known prior data point of $1.176/hr exactly. |
| AWS | r6i.4xlarge (us-west-2) | 16 | 128 GiB | 0 (EBS only) | $1.0080 `[WEB]` | $24.19 | $726 | gp3 $0.080/GB-mo us-west-2 `[WEB]`; 200 GB = $16.00/mo | not obtained | No expiry |
| AWS | r7i.4xlarge (us-west-2) | 16 | 128 GiB | 0 (EBS only) | $1.0584 `[WEB]` | $25.40 | $762 | gp3 $0.080/GB-mo `[WEB]` | not obtained | No expiry |

## Tier 2: ~256 GB RAM

| Provider | Instance type | vCPU | RAM | Disk included | $/hr | $/day | $/30d | Storage cost note | Availability observed | Expiry / persistence |
|---|---|---|---|---|---|---|---|---|---|---|
| Vast.ai | offer 50175814, 2x Quadro P4000, Xeon E5-2690 | 32 host / **16 effective** | 258 GB | 1378 GB | **$0.1339** | $3.21 | $96 | $0.08/GB-mo `[CLI]` | yes — Quebec, CA; on-demand, reliability 0.9950 | On-demand, no fixed expiry; host can stop/retire |
| Vast.ai | offer 33925788, 1x RTX 5060 Ti | 192 host / **96 effective** | 258 GB | 3297 GB | $0.3342 | $8.02 | $241 | $0.12/GB-mo `[CLI]` | yes — Norway, NO; on-demand, reliability 0.9973 | same; far more cores if parallel build matters |
| Scaleway | **POP2-HM-32C-256G** | 32 | 256 GiB | 0 (block only) | $1.9013 (€1.6480) `[CLI]` | $45.63 | $1369 | + block storage ≈ €0.0949/GB-mo (5K) `[WEB]` | yes — fr-par-3, nl-ams-1/2/3, pl-waw-2/3; scarce fr-par-1/2 `[CLI]` | No expiry; runs until deleted |
| Scaleway | GP1-XL | 48 | 256 GiB | 559 GB local NVMe | $1.9311 (€1.6738) `[CLI]` | $46.35 | $1390 | Local volume included | yes — fr-par-1, nl-ams-1/2, pl-waw-1/2; scarce fr-par-2 `[CLI]` | No expiry |
| Scaleway | MEMORY3-X32C-256G | 32 | 256 GiB | 0 (block only) | $2.0914 (€1.8128) `[CLI]` | $50.19 | $1506 | as above | yes — fr-par-1/2, nl-ams-2; shortage nl-ams-1 `[CLI]` | No expiry |
| AWS | r6i.8xlarge (us-west-2) | 32 | 256 GiB | 0 (EBS only) | $2.0160 `[WEB]` | $48.38 | $1452 | gp3 $0.080/GB-mo `[WEB]` | not obtained | No expiry |
| AWS | r7i.8xlarge (us-west-2) | 32 | 256 GiB | 0 (EBS only) | $2.1168 `[WEB]` | $50.80 | $1524 | gp3 $0.080/GB-mo `[WEB]` | not obtained | No expiry |
| AWS | r6i.8xlarge (us-west-1) | 32 | 256 GiB | 0 (EBS only) | $2.2400 `[WEB]` | $53.76 | $1613 | gp3 $0.096/GB-mo `[WEB]` | not obtained | No expiry |
| AWS | r7i.8xlarge (us-west-1) | 32 | 256 GiB | 0 (EBS only) | $2.3520 `[WEB]` | $56.45 | $1693 | gp3 $0.096/GB-mo `[WEB]` | not obtained | **Uses the entire 32-vCPU On-Demand Standard quota in us-west-1.** No headroom for any other running instance. |

### Caveats that matter more than the headline price

- **AWS numbers are all `[WEB]`, not CLI.** The `explicit-lean-pilot` profile's SSO session has expired (`aws sts get-caller-identity` -> "Your session has expired. Please reauthenticate using 'aws login'"). I did not reauthenticate, as that needs your credentials. Prices came instead from AWS's own public, unauthenticated bulk pricing JSON (`pricing.us-east-1.amazonaws.com/offers/v1.0/aws/AmazonEC2/current/<region>/index.json`), which is the same list-price data the pricing API serves. The r7i.4xlarge us-west-1 figure of $1.1760/hr matches your known prior data point exactly, which is a good sanity check on the source. **Live availability and a live quota check were not obtained for AWS.**
- **Vast.ai `cpu_cores_effective` is the number that counts**, not `cpu_cores`. The cheapest 128 GB offer exposes 32 host cores but only 16 effective; the cheapest 256 GB offer likewise 16 effective. Both still meet the >= 8 (16 preferred) requirement, but they are not 32-core machines.
- **Vast.ai cheap offers are old Xeons** (E5-2650 v2, E5-2690 are Ivy/Sandy Bridge era, ~2012-2013). Per-core Lean compile throughput will be substantially below a modern r7i (Sapphire Rapids) or EPYC core. The dollar gap is so large it very likely still wins, but wall-clock build time will be noticeably worse. Offer 29431161 (EPYC 7282, $0.0690) is a better-balanced pick for only $0.002/hr more.
- **Vast.ai persistence is the real risk.** Offers are on-demand (`is_bid=false`), so not preemptible in the spot sense and they have no fixed expiry. But these are consumer/prosumer hosts, not a managed cloud: a host can take a machine down for maintenance or retire it, and reliability scores (0.99+) are precisely an admission that this happens. For a multi-day Mathlib build, keep the build resumable and back up results off-box.
- **Scaleway availability is live and genuinely mixed** — several high-memory types show `scarce` or `shortage` in the Paris zones. If you go Scaleway, prefer nl-ams or pl-waw, or fr-par-3.
- Scaleway block-storage price is `[WEB]` (hourly per-GB rate from the pricing page, converted at ~730 h/month); it was not exposed by the instance CLI commands I ran.
- I did not find ENT1-L/XL or PRO2-XXL in any zone's `server-type list` output; those names appear to be retired or not offered in the zones checked. PRO2-L is present.

---

## Recommendation

1. **Cheapest persistent 128 GB: Vast.ai offer 50282163 at $0.0671/hr (~$48/30d)** — 16 effective cores, 537 GB disk, on-demand with no expiry; prefer offer 29431161 (EPYC, $0.0690/hr) for much better per-core speed at ~the same price.
2. **Cheapest persistent 256 GB: Vast.ai offer 50175814 at $0.1339/hr (~$96/30d)** — 16 effective cores, 1378 GB disk, on-demand, no expiry.
3. **Cheapest *managed-cloud* option** (if Vast's host-reclaim risk is unacceptable): 128 GB -> Scaleway GP1-L at $0.8932/hr (~$643/30d, 32 vCPU + 559 GB local NVMe, no separate storage bill); 256 GB -> Scaleway POP2-HM-32C-256G at $1.9013/hr (~$1369/30d) plus block storage.
4. **AWS is NOT significantly cheaper — it is significantly more expensive.** At 128 GB the best AWS price ($1.0080/hr, r6i.4xlarge us-west-2) is ~15x the cheapest Vast option and ~13% *above* Scaleway GP1-L; at 256 GB ($2.0160/hr) it is ~15x Vast and ~6% above Scaleway POP2-HM. Under the >30% test, AWS fails in both tiers in both directions.
5. **Practical pick:** run on Vast (EPYC offer) if the build is checkpointable, since the 13-15x saving dwarfs the reliability risk; otherwise Scaleway GP1-L, whose bundled 559 GB NVMe removes the separate storage bill. Avoid r7i.8xlarge in us-west-1 — it consumes the full 32-vCPU quota and is the most expensive row in the table.

---

## Commands run (all read-only)

```sh
which scw vastai aws
scw version
mkdir -p /Users/ptsier/projects/explicit-lean/tracking/tasks

# Scaleway: server types + live availability, 9 zones
for z in fr-par-1 fr-par-2 fr-par-3 nl-ams-1 nl-ams-2 nl-ams-3 pl-waw-1 pl-waw-2 pl-waw-3; do
  scw instance server-type list zone=$z -o json
done

# Vast.ai: on-demand, verified, rentable offers (note: cpu_ram filter is in GB here)
vastai search offers 'cpu_ram>=128 disk_space>=200 cpu_cores>=8 rentable=true verified=true' -o dph_total --raw
vastai search offers 'cpu_ram>=256 disk_space>=200 cpu_cores>=8 rentable=true verified=true' -o dph_total --raw

# AWS: attempted via the pricing API with the explicit-lean-pilot profile (FAILED - session expired)
aws pricing get-products --profile explicit-lean-pilot --region us-east-1 --service-code AmazonEC2 \
  --filters "Type=TERM_MATCH,Field=instanceType,Value=r7i.4xlarge" \
            "Type=TERM_MATCH,Field=location,Value=US West (N. California)" \
            "Type=TERM_MATCH,Field=operatingSystem,Value=Linux" \
            "Type=TERM_MATCH,Field=tenancy,Value=Shared" \
            "Type=TERM_MATCH,Field=preInstalledSw,Value=NA" \
            "Type=TERM_MATCH,Field=capacitystatus,Value=Used" --output json
# (repeated for r7i.8xlarge, r6i.4xlarge, r6i.8xlarge x us-west-1/us-west-2 - all returned the same expiry error)
aws sts get-caller-identity --profile explicit-lean-pilot --region us-west-1   # -> session expired
aws configure list-profiles                                                    # profile discovery only

# AWS fallback: public unauthenticated bulk pricing JSON (no credentials, read-only GET)
curl -s https://pricing.us-east-1.amazonaws.com/offers/v1.0/aws/AmazonEC2/current/us-west-1/index.json -o ec2-us-west-1.json
curl -s https://pricing.us-east-1.amazonaws.com/offers/v1.0/aws/AmazonEC2/current/us-west-2/index.json -o ec2-us-west-2.json
# then parsed locally with python3 for the 4 instance types + gp3, OnDemand/Shared/Linux/NA/Used

# FX rate
curl -sL 'https://api.frankfurter.dev/v1/latest?base=EUR&symbols=USD'
```

WebFetch (read-only page reads): `instances.vantage.sh/aws/ec2/r7i.4xlarge` (returned only the us-east-1 base price, so unused), `aws.amazon.com/ec2/pricing/on-demand/` (JS-rendered, no data), `scaleway.com/en/pricing/block-storage/` (404), `scaleway.com/en/pricing/storage/` (block-storage per-GB price used above).

No instance was created, started, rented, reserved, or modified. No local config or credential file was written. The only files created are this report and the two pricing JSON downloads plus parsing scratch, all under the session scratchpad directory.
