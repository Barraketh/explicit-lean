# Durable report storage

> Archive conventions and historical S3 setup. Start with [HANDOFF.md](HANDOFF.md)
> for current evidence locations. The latest v10 reports and memory measurements
> are local under `.lake`; this document does not establish that they were
> uploaded. Bucket configuration and access have not been rechecked for the
> September 10 handoff. Do not run the upload procedure merely to get started.

The shared archive for Explicit Lean validation reports is the private S3
bucket:

```text
s3://explicit-lean-reports-538639825139-us-east-1/
```

The bucket is in `us-east-1`. It has S3-managed AES-256 encryption, versioning,
bucket-owner-enforced object ownership, and all public access blocked. Access is
through the project's authorized AWS identities; do not add public bucket or
object policies.

## Object layout

Store one immutable report snapshot under:

```text
reports/<UTC-date>/<full-explicit-lean-git-commit>/<run-id>/<local-path-below-.lake>
```

Use the full Git commit, not a branch name or abbreviated commit. A report is
evidence for one repository revision, translator/artifact schema, Lean pin, and
Mathlib pin; moving names would make that provenance ambiguous. The run ID is a
UTC start timestamp plus a short run kind. Create a new prefix for every run
rather than treating S3 versioning as the run identifier.

The initial archive snapshot is:

```text
reports/2026-08-28/6f331f7a3ba81e5e9563466a29c1b6e2c2400e47/
```

It contains the 17 `final` and `normal-final` JSON/Markdown reports that were
present locally when schema 27 was published (278,710 bytes total). It does not
claim to be a full-Mathlib schema-27 closure, and the active roadmap does not
require such a legacy run. This initial snapshot predates the run-ID component;
do not use its shorter layout for new uploads.

## What to archive

Archive the reduced, durable outputs needed to review a run:

- `final/` and `normal-final/` JSON and Markdown reports;
- any inventory or reduced summary that is not already represented in the
  final report; and
- small diagnostic artifacts only when they are needed to explain a terminal
  classification or failed production run.

A boundary-state prototype or corpus run must additionally retain:

- a manifest containing the full repository, Lean, and Mathlib commits; the
  artifact/comparator version; commands executed; and SHA-256 checksums of every
  other archived file;
- the syntax inventory and per-occurrence terminal classifications;
- selector ambiguity/missing-variant and external-effect summaries;
- unchanged-continuation compilation results;
- declaration type, unresolved-metavariable, `sorryAx`, and transitive axiom-set
  comparisons; and
- the syntax-aware remaining-call count.

Historical schema-27 runs keep their existing report formats. They must be
labelled as legacy and must not be cited as boundary-state closure evidence.
The boundary reducer should place all required durable outputs beneath its
run-specific `final/` directory so the standard upload filter includes them.

Do not upload Lake build products, copied Mathlib trees, certificate scratch
directories, raw worker caches, credentials, SSH material, or the entire
`.lake/` directory. Large raw shard workspaces should be retained only under an
explicit incident or research-retention decision.

## Upload procedure

Run uploads only from the clean, published commit that produced the reports.
Existing schema-27 production tooling enforces the same clean/published
boundary; future boundary tooling must preserve that guard. Do not hardcode a
personal AWS profile in the repository; use the active authorized identity or
pass `--profile` explicitly when required. Run `aws sts get-caller-identity`
before uploading. If the shell inherited an obsolete `AWS_PROFILE`, unset it
and repeat the identity check rather than encoding that profile in project
files.

```sh
set -eu

report_bucket=explicit-lean-reports-538639825139-us-east-1
report_commit=$(git rev-parse HEAD)
report_started=$(date -u +%Y-%m-%dT%H%M%SZ)
report_date=${report_started%%T*}
report_kind=${REPORT_KIND:?set REPORT_KIND to a short value such as boundary-prototype}
case "${report_kind}" in
  *[!A-Za-z0-9._-]*|'') echo "invalid REPORT_KIND" >&2; exit 2 ;;
esac
report_run="${report_started}-${report_kind}"
report_prefix="reports/${report_date}/${report_commit}/${report_run}"

test -z "$(git status --porcelain)"
git ls-remote origin | rg -q "^${report_commit}[[:space:]]"
aws sts get-caller-identity >/dev/null
test "$(aws s3api list-objects-v2 \
  --bucket "${report_bucket}" \
  --prefix "${report_prefix}/" \
  --max-keys 1 \
  --query KeyCount \
  --output text)" = 0

aws s3 sync .lake "s3://${report_bucket}/${report_prefix}/" \
  --exclude "*" \
  --include "*/final/*" \
  --include "*/normal-final/*" \
  --exclude "report-archive/*" \
  --sse AES256 \
  --metadata "project=explicit-lean,git-commit=${report_commit},run-id=${report_run},source=local-final-report"
```

If a run has additional inventory or summary files, upload them beneath the
same prefix with paths that describe their role, such as `inputs/` or
`summaries/`.

## Verification and retrieval

List one snapshot and check its object count and total bytes:

```sh
aws s3api list-objects-v2 \
  --bucket "${report_bucket}" \
  --prefix "${report_prefix}/" \
  --query '{Count:length(Contents),Bytes:sum(Contents[].Size),Objects:Contents[].{Key:Key,Size:Size}}'
```

For a production closure, compare the manifest's local SHA-256 checksums with
freshly downloaded objects and retain the final reducer's success status in the
handoff. Do not use an S3 ETag as a content checksum. Download a snapshot
without mixing it into an active run directory:

```sh
aws s3 sync \
  "s3://${report_bucket}/${report_prefix}/" \
  ".lake/report-archive/${report_date}-${report_commit}-${report_run}/"
```

S3 is durable storage, not correctness authority. A boundary-state claim rests
on the pinned source and toolchain, the reviewed boundary contract and artifact
version, successful unchanged-continuation compilation, declaration type/axiom
checks, and the archived inventory and closure results. The schema-27 engine
identity and legacy source-review lock authenticate only historical replay
reports; they do not validate the active translator.
