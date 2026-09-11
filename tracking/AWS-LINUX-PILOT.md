# Bounded AWS/Linux pilot

The user authorized a single bounded pilot in AWS account `538639825139`, region
`us-west-1`, with a $20 all-in ceiling and delegated the runtime choice. The
selected bounds are a 10-hour worker and a 12-hour absolute instance lifetime.
The exact absolute cutoff is `2026-09-12T11:00:00Z`. The first launch request
failed CloudFormation's regional early validation and auto-deleted before any
resource was created. Its authorization ref
`e5c86887d311853eb4013d1582e79c68f4d47535` is superseded and must not be
reused. `explicit-lean-pilot` still resolves to the dedicated non-root operator,
AWS raised the On-Demand Standard quota to 32 vCPUs, and the user explicitly
waived the MFA recommendation. The clean schedule-validation fix is published;
explicitly identify its replacement HEAD by full hash before retrying.

The pilot is exactly one single-purpose, default-tenancy Linux x86-64 host with
at least 128 GiB of RAM, one worker, one attempt for each of the 15 recorded
candidates, and no automatic continuation. AWS Dedicated Tenancy is not
authorized because its surcharge is outside the recorded cost bound.
`explicit-lean-cloud` is not part of this procedure.

## Authorization and cost gate

The approved envelope and exact cutoff are recorded in the policy. After that
change is committed and published, the user must identify that full commit as
the authorization ref. The full hash is supplied as a launch argument
rather than written into its own commit, which would be a circular reference.
The controller verifies that it is the clean local `HEAD` and is reachable from
the exact public HTTPS origin before any mutation, then records it in AWS tags,
the fresh manifest and run receipts. Query the selected region's
current on-demand instance and storage prices again, and refuse the launch
unless the worst-case instance lifetime plus storage and data charges fit below
the approved ceiling. AWS budget alarms are advisory and do not replace this
precomputed bound or the host shutdown deadline.

The September 11 price check found `r7i.4xlarge` at $1.176/hour and gp3 at
$0.096/GB-month in Northern California. Twelve compute hours cost $14.112;
200 GiB of gp3 for twelve hours is approximately $0.32, and one public IPv4
address is approximately $0.06. The $14.492 subtotal leaves $5.508 of the $20
ceiling for small ancillary charges. Do not add a second host, extend the
deadline, or convert the remaining headroom into extra scope.

The original campaign deadline is historical. The matching top-level tracker
`deadline` and `notAfter` now define only this one-pilot continuation. The
former campaign-specific 25%/22% usage policy is obsolete.
`python3 Experiment/campaign_budget.py check`
must return `canDispatch: true` immediately before the worker starts and is
checked again before every module. Unknown availability or an actual account
rate-limit/spend stop halts the run; never buy or redeem credits.

## Controller sequence and remote authorization

Use the checked-in controller from a clean authorization checkout. Its launch
phase creates only the single CloudFormation stack and then stops before worker
dispatch:

```sh
python3 Experiment/aws_linux_pilot.py launch \
  --repo-url https://github.com/Barraketh/explicit-lean.git \
  --authorization-ref "${PILOT_AUTHORIZATION_REF:?full published commit}" \
  --confirm-launch
```

Retain the returned run ID. Open the controller's interactive Session Manager
phase and complete the device-code prompt in a browser:

```sh
python3 Experiment/aws_linux_pilot.py auth \
  --run-id "${PILOT_RUN_ID:?returned run ID}" --confirm-auth
```

The remote command runs the pinned Codex CLI as root, verifies `codex login
status`, runs the campaign budget guard in the pinned checkout, and produces a
local nonsecret proof bound to the run and instance. Do not copy `auth.json`, an
access token, API key, or Mac runtime state. Only after that phase succeeds may
the controller send the one worker command:

```sh
python3 Experiment/aws_linux_pilot.py start-worker \
  --run-id "${PILOT_RUN_ID}" \
  --remote-auth-proof "${PILOT_REMOTE_AUTH_PROOF:?returned proof path}" \
  --confirm-start-worker
```

The worker repeats the login-status and budget checks before preparing inputs.
An ambiguous dispatch is not retried; inspect status and rely on the absolute
stack termination schedule while preserving evidence.

## Fresh Linux checkout and tools

On the newly authorized host, save `/etc/os-release`, `uname -a`, instance
metadata, the AWS identity/region, block-device description and package
versions in the run directory. Install Git, curl, a C/C++ toolchain, GMP,
libffi, zstd, SQLite, jq, Python 3 and the controller-pinned Codex CLI from the
chosen Linux image. The device-auth sequence above is the required end-to-end
authorization proof. Install `elan`, then:

```sh
git clone <authorized-explicit-lean-remote> explicit-lean
cd explicit-lean
git checkout --detach "${PILOT_AUTHORIZATION_REF:?user-approved full commit}"
PILOT_COMMIT=$(git rev-parse HEAD)
test "${PILOT_COMMIT}" = "${PILOT_AUTHORIZATION_REF}"
git ls-remote origin | grep -q "^${PILOT_COMMIT}[[:space:]]"
test -z "$(git status --porcelain)"
test "$(cat lean-toolchain)" = "leanprover/lean4:v4.32.2"
test "$(jq -r '.packages[] | select(.name=="mathlib") | .rev' lake-manifest.json)" = \
  "905b95818eb32af7874a58b427f50c1711a5e96c"
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
```

Do not copy Mac build products, databases, manifests, receipts or output trees.
Downloading the pinned Mathlib Linux cache is allowed; it is platform-specific
build input, not pilot evidence.

## Preflight gates

Before provisioning, the controller verifies through AWS instance-type metadata
that `r7i.4xlarge` provides at least 131072 MiB nominal memory and supports
x86-64. Inside Linux, verify at least 120 GiB remains guest-visible after
firmware/kernel reservations, plus at least 12 GiB of available memory and free
disk. Run the inexpensive checks first, then the focused Lean boundary gate:

```sh
test "$(uname -s)" = Linux
test "$(uname -m)" = x86_64
test "$(awk '/^MemTotal:/ {printf "%.0f", $2 * 1024}' /proc/meminfo)" -ge 128849018880
test "$(awk '/^MemAvailable:/ {printf "%.0f", $2 * 1024}' /proc/meminfo)" -ge 12884901888
test "$(df --output=avail -B1 . | tail -1)" -ge 12884901888
test -z "$(git status --porcelain)"
python3 -B Experiment/check_campaign_supervisor_v10.py
python3 -B Experiment/check_campaign_worker.py
python3 -B Experiment/check_translation_index.py
python3 -B Experiment/check_linux_process_sampler.py
python3 -B Experiment/check_simp_engine_boundary.py
python3 Experiment/campaign_budget.py check
```

Expected isolated Python counts are 22, 33 and 13. Record actual results; a
failed or unrun check is not a pass. The focused Lean gate may build native
Linux tools and must complete before the pilot.

## Fresh inputs and index

Create a new run ID and never reuse it. Keep inputs/index outside the worker's
cleanup root and worker output beneath `.lake/boundary-materialization`:

```sh
pilot_started=$(date -u +%Y%m%dT%H%M%SZ)
pilot_nonce=$(python3 -c 'import secrets; print(secrets.token_hex(16))')
pilot_run="${pilot_started}-${pilot_nonce}"
input_root=".lake/search-free-mathlib/aws-linux-pilot/${pilot_run}"
output_root=".lake/boundary-materialization/aws-linux-pilot/${pilot_run}"
mkdir -m 700 -p "${input_root}" "${output_root}"

manifest="${input_root}/schema13-isolated-closed-manifest-v10.json"
depmap="${input_root}/index-header-dependency-map.json"
database="${input_root}/translation-index.sqlite3"

python3 -B Experiment/simp_engine_boundary_corpus.py manifest \
  --output "${manifest}" --commit "${PILOT_COMMIT}" \
  --checkpoint-root "${input_root}/manifest-checkpoints"
python3 -B Experiment/lean_import_index.py \
  --manifest "${manifest}" --source-root .lake/packages/mathlib \
  --output "${depmap}"
python3 -B Experiment/translation_index.py init "${database}"
sha256sum "${manifest}" "${depmap}" >"${input_root}/input-sha256.txt"
```

Strictly verify the exact manifest bytes and Linux executables before dispatch.
Supply the computed lowercase hashes to `verify` and retain its JSON receipt:

```sh
manifest_sha=$(sha256sum "${manifest}" | cut -d' ' -f1)
toolchain_prefix=$(lake env lean --print-prefix)
lake_path="${toolchain_prefix}/bin/lake"
lean_path="${toolchain_prefix}/bin/lean"
export PATH="${toolchain_prefix}/bin:${PATH}"
lake_sha=$(sha256sum "${lake_path}" | cut -d' ' -f1)
lean_sha=$(sha256sum "${lean_path}" | cut -d' ' -f1)
python3 -B Experiment/verify_simp_boundary_manifest.py verify "${manifest}" \
  --repository-root . --mathlib-root .lake/packages/mathlib \
  --expected-repository-commit "${PILOT_COMMIT}" \
  --expected-sha256 "${manifest_sha}" --dependency-map "${depmap}" \
  --lake-path "${lake_path}" --expected-lake-sha256 "${lake_sha}" \
  --lean-path "${lean_path}" --expected-lean-sha256 "${lean_sha}" \
  >"${input_root}/manifest-verification.json"
```

## One-worker pilot

Set `PILOT_MAX_SECONDS` to the approved runtime ceiling. The sampler timeout is
two minutes longer only to let the worker perform its own bounded shutdown; the
instance shutdown deadline remains absolute. Expand the following module list
from the policy file without changing its order or contents:

```sh
: "${PILOT_MAX_SECONDS:?set to the approved maximumRuntimeSeconds}"
test "${PILOT_MAX_SECONDS}" = "$(jq -r '.authorization.maximumRuntimeSeconds' \
  tracking/aws-linux-pilot-policy.json)"
module_args=()
while IFS= read -r module; do module_args+=(--module "$module"); done < <(
  jq -r '.modules[]' tracking/aws-linux-pilot-policy.json
)
worker_id="aws-linux-pilot-${pilot_run}"

python3 -B Experiment/linux_process_sampler.py \
  --metrics "${output_root}/process-metrics.json" \
  --log "${output_root}/worker.log" \
  --timeout "$((PILOT_MAX_SECONDS + 120))" -- \
  python3 -B Experiment/campaign_worker.py \
    --database "${database}" --manifest "${manifest}" \
    --dependency-map "${depmap}" --output-root "${output_root}/attempts" \
    --worker "${worker_id}" --max-modules 15 \
    --module-timeout 1800 --max-seconds "${PILOT_MAX_SECONDS}" \
    --minimum-free-bytes 12884901888 "${module_args[@]}"
```

Do not pass `--retry-failed`; the fresh index and one-attempt policy make each
candidate a single observation. Preserve every generated nonce and receipt.

## Stops and report

Stop without another module when any of these occurs: Codex availability is
unknown or actually rate-limited, the approved not-after time or runtime is reached, the
cost bound would be exceeded, available memory or disk falls below 12 GiB, an
input hash changes, the checkout becomes dirty, a lease remains live after a
worker failure, or the host is interrupted. Terminate the instance at the
absolute deadline even if report collection fails.

For every module, report elapsed time, terminal class (`verified_success`,
`resource_stop`, `semantic_or_unsupported_failure`, `timeout`, or
`infrastructure_failure`), remaining executable calls, and evidence/log hashes.
The sampler report supplies separately observed Python and Lean peak RSS plus
the whole launched process-tree peak. Record host configuration and total
elapsed/cost alongside those values. A reproduced semantic failure is a valid
pilot observation, never a translated success. Do not grant whole-tree coverage
from this pilot.
