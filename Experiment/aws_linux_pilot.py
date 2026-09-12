#!/usr/bin/env python3
"""Read-only-by-default controller for one bounded AWS Linux pilot.

``launch --confirm-launch`` creates one CloudFormation stack and stops at
``awaiting-codex-auth``.  ``auth --confirm-auth`` opens the Session Manager
device-login flow.  ``start-worker --confirm-start-worker`` rechecks local and
on-host gates and sends at most one SSM command.  create-stack, send-command,
and cleanup delete-stack are the only AWS mutations in this controller.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation, ROUND_UP
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import shlex
import subprocess
import sys
import time
from typing import Any, Callable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = ROOT / "tracking/aws-linux-pilot-policy.json"
TEMPLATE_PATH = ROOT / "Experiment/aws_linux_pilot_stack.yaml"
STATE_ROOT = ROOT / ".lake/search-free-mathlib/aws-linux-pilot/runs"
PROFILE, ACCOUNT_ID, REGION = "explicit-lean-pilot", "538639825139", "us-west-1"
INSTANCE_TYPE, VOLUME_TYPE, VOLUME_SIZE_GIB = "r7i.4xlarge", "gp3", 200
MAX_SPEND_USD, MAX_WORKER_SECONDS = Decimal("20"), 36_000
WORKER_SAMPLER_GRACE_SECONDS = 120
WORKER_SAMPLER_TIMEOUT_SECONDS = MAX_WORKER_SECONDS + WORKER_SAMPLER_GRACE_SECONDS
MAX_INSTANCE_LIFETIME_SECONDS = 43_200
REQUIRED_MEMORY_BYTES = 128 * 1024**3
MINIMUM_GUEST_MEMORY_BYTES = 120 * 1024**3
MINIMUM_FREE_BYTES = 12 * 1024**3
MINIMUM_AVAILABLE_MEMORY_BYTES = 12 * 1024**3
AMI_PARAMETER = "/aws/service/ami-amazon-linux-latest/al2023-ami-kernel-default-x86_64"
EVIDENCE_BUCKET, EVIDENCE_REGION = "explicit-lean-reports-538639825139-us-east-1", "us-east-1"
STACK_PREFIX = "explicit-lean-pilot-"
CANONICAL_REPO_URL = "https://github.com/Barraketh/explicit-lean.git"
ELAN_URL = "https://github.com/leanprover/elan/releases/download/v4.2.3/elan-x86_64-unknown-linux-gnu.tar.gz"
ELAN_SHA256 = "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2"
CODEX_URL = "https://registry.npmjs.org/@openai/codex/-/codex-0.154.0-linux-x64.tgz"
CODEX_SHA512_HEX = "6b8148dc0f2c1adc06aceaa5b6b3dbad2da16a3ac7406e7dd44c2645f891a0b31bd74571741b54196e20bba20955810d898180ee4dcfe239511c4a02654fecf5"
REMOTE_AUTH_STRATEGY, REMOTE_AUTH_MAX_AGE_SECONDS = "ssm-device-auth", 15 * 60
RUN_ID_RE = re.compile(r"^[0-9]{8}T[0-9]{6}Z-[0-9a-f]{32}$")
AUTHORIZATION_REF_RE = re.compile(r"^[0-9a-f]{40}$")
AMI_ID_RE, INSTANCE_ID_RE = re.compile(r"^ami-[0-9a-f]+$"), re.compile(r"^i-[0-9a-f]+$")
EXPECTED_LEAN_TOOLCHAIN = "leanprover/lean4:v4.32.2"
EXPECTED_LEAN_COMMIT = "f3b06c705e6c85f5314019d5d3baab0fec5b580c"
EXPECTED_MATHLIB_COMMIT = "905b95818eb32af7874a58b427f50c1711a5e96c"
EXPECTED_REVIEWED_COMMIT = "ee30955a34331c6508cd510b02a2e66ae559bb9a"
PILOT_MODULES = (
    "Mathlib/Algebra/Homology/CommSq.lean",
    "Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean",
    "Mathlib/Algebra/Ring/GeomSum.lean",
    "Mathlib/CategoryTheory/Monoidal/Cartesian/Over.lean",
    "Mathlib/Control/Applicative.lean",
    "Mathlib/Topology/QuasiSeparated.lean",
    "Mathlib/Topology/Convenient/OpenClosed.lean",
    "Mathlib/CategoryTheory/Sites/Precoverage/Generates.lean",
    "Mathlib/CategoryTheory/Sites/Hypercover/SheafOfTypes.lean",
    "Mathlib/Topology/NoetherianSpace.lean",
    "Mathlib/Logic/Relation.lean",
    "Mathlib/Data/Nat/Init.lean",
    "Mathlib/Logic/IsEmpty/Basic.lean",
    "Mathlib/Order/Compare.lean",
    "Mathlib/Data/Set/Restrict.lean",
)


class PilotError(RuntimeError):
    """Invalid input, unavailable gate, or failed safety invariant."""


class GateBlocked(PilotError):
    """A known unmet launch gate."""


def _obj(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise PilotError(f"{label} must be a JSON object")
    return value


def _read_json(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, json.JSONDecodeError) as error:
        raise PilotError(f"cannot read {label} {path}: {error}") from error
    return _obj(value, label), raw


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _dec(value: object, label: str) -> Decimal:
    if isinstance(value, bool) or value is None:
        raise PilotError(f"{label} must be finite and non-negative")
    try:
        result = Decimal(str(value))
    except (InvalidOperation, ValueError) as error:
        raise PilotError(f"{label} is not numeric") from error
    if not result.is_finite() or result < 0:
        raise PilotError(f"{label} must be finite and non-negative")
    return result


def _dt(value: object, label: str, *, whole_seconds: bool = True) -> datetime:
    if type(value) is not str or not value.strip():
        raise PilotError(f"{label} must be a non-null ISO-8601 timestamp")
    try:
        parsed = datetime.fromisoformat(value.strip().replace("Z", "+00:00"))
    except ValueError as error:
        raise PilotError(f"{label} is not a valid ISO-8601 timestamp") from error
    if parsed.tzinfo is None or parsed.utcoffset() is None or (whole_seconds and parsed.microsecond):
        raise PilotError(f"{label} must include a timezone and whole-second precision")
    return parsed.astimezone(timezone.utc)


def _utc(value: datetime) -> str:
    if value.tzinfo is None or value.utcoffset() is None:
        raise PilotError("timestamp must include an explicit timezone")
    return value.astimezone(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def worker_execution_timeout_seconds(*, not_after: datetime, now: datetime) -> int:
    """Bound the outer SSM plugin to the host lifetime and exact run cutoff."""
    if not_after.tzinfo is None or not_after.utcoffset() is None:
        raise GateBlocked("worker execution cutoff must include an explicit timezone")
    if now.tzinfo is None or now.utcoffset() is None:
        raise GateBlocked("worker dispatch clock must include an explicit timezone")
    remaining = (not_after.astimezone(timezone.utc) - now.astimezone(timezone.utc)).total_seconds()
    timeout = min(MAX_INSTANCE_LIFETIME_SECONDS, int(remaining))
    if timeout <= 0:
        raise GateBlocked("worker execution cutoff leaves no positive SSM timeout")
    return timeout


def load_policy(path: Path = POLICY_PATH) -> tuple[dict[str, Any], bytes]:
    policy, raw = _read_json(path, "pilot policy")
    if type(policy.get("schema")) is not int or policy.get("schema") != 1:
        raise PilotError("pilot policy schema must be 1")
    auth = _obj(policy.get("authorization"), "authorization")
    for key, expected in {"awsAccountId": ACCOUNT_ID, "region": REGION, "maximumSpendUsd": 20,
                          "maximumRuntimeSeconds": MAX_WORKER_SECONDS,
                          "maximumInstanceLifetimeSeconds": MAX_INSTANCE_LIFETIME_SECONDS,
                          "paidResourcesAuthorized": True}.items():
        if type(auth.get(key)) is not type(expected) or auth.get(key) != expected:
            raise PilotError(f"authorization.{key} does not match the approved envelope")
    machine = _obj(policy.get("machine"), "machine")
    for key, expected in {"provider": "aws", "operatingSystem": "linux", "architecture": "x86_64",
                          "minimumMemoryBytes": REQUIRED_MEMORY_BYTES, "instanceType": INSTANCE_TYPE,
                          "rootVolumeType": VOLUME_TYPE, "rootVolumeSizeGiB": VOLUME_SIZE_GIB,
                          "workers": 1, "tenancy": "default"}.items():
        if type(machine.get(key)) is not type(expected) or machine.get(key) != expected:
            raise PilotError(f"machine.{key} does not match the approved envelope")
    limits = _obj(policy.get("limits"), "limits")
    for key, expected in {"moduleTimeoutSeconds": 1800, "maximumAttemptsPerModule": 1,
                          "minimumFreeDiskBytes": MINIMUM_FREE_BYTES,
                          "minimumAvailableMemoryBytes": MINIMUM_AVAILABLE_MEMORY_BYTES}.items():
        if type(limits.get(key)) is not type(expected) or limits.get(key) != expected:
            raise PilotError(f"limits.{key} does not match the approved envelope")
    if tuple(policy.get("modules", ())) != PILOT_MODULES:
        raise PilotError("pilot module list/order does not match the approved scope")
    pins = _obj(policy.get("pins"), "pins")
    for key, expected in {"reviewedCodeCommit": EXPECTED_REVIEWED_COMMIT, "leanToolchain": EXPECTED_LEAN_TOOLCHAIN,
                          "leanCommit": EXPECTED_LEAN_COMMIT, "mathlibCommit": EXPECTED_MATHLIB_COMMIT}.items():
        if pins.get(key) != expected:
            raise PilotError(f"pins.{key} does not match the approved pin")
    output = _obj(policy.get("output"), "output")
    if output.get("databaseName") != "translation-index.sqlite3" or output.get("freshRunIdRequired") is not True:
        raise PilotError("output policy does not require a fresh run")
    return policy, raw


def parse_not_after(policy: Mapping[str, Any], now: datetime) -> datetime:
    if now.tzinfo is None or now.utcoffset() is None:
        raise PilotError("launch clock must be timezone-aware")
    deadline = _dt(_obj(policy.get("authorization"), "authorization").get("notAfter"), "authorization.notAfter")
    current = now.astimezone(timezone.utc)
    if deadline <= current:
        raise GateBlocked("authorization.notAfter has already passed")
    if deadline > current + timedelta(seconds=MAX_INSTANCE_LIFETIME_SECONDS):
        raise GateBlocked("authorization.notAfter exceeds the 12-hour instance lifetime")
    return deadline


def validate_cost(policy: Mapping[str, Any], now: datetime, current_pricing: Mapping[str, Any] | None = None,
                  *, maximum_age_seconds: int = 24 * 3600) -> dict[str, Any]:
    source = current_pricing if current_pricing is not None else _obj(policy.get("costEstimate"), "costEstimate")
    checked = _dt(source.get("checkedAt"), "costEstimate.checkedAt", whole_seconds=False)
    age = (now.astimezone(timezone.utc) - checked).total_seconds()
    if age < 0 or age > maximum_age_seconds:
        raise GateBlocked("current AWS price snapshot is missing or stale")
    hourly, storage, ipv4 = (_dec(source.get(key), label) for key, label in (
        ("ec2OnDemandUsdPerHour", "EC2 on-demand hourly price"),
        ("gp3UsdPerGbMonth", "gp3 monthly price"), ("publicIpv4UsdPerHour", "public IPv4 hourly price")))
    reported = _dec(source.get("estimatedBoundedSubtotalUsd"), "reported bounded subtotal")
    headroom = _dec(source.get("unallocatedSpendHeadroomUsd"), "unallocated spend headroom")
    if str(source.get("tenancy", "default")).lower() != "default" or source.get("spot") not in (None, False):
        raise GateBlocked("only default-tenancy on-demand pricing is authorized")
    hours = Decimal(MAX_INSTANCE_LIFETIME_SECONDS) / Decimal(3600)
    computed = hourly * hours + storage * Decimal(VOLUME_SIZE_GIB) * hours / Decimal(30 * 24) + ipv4 * hours
    if reported < computed or reported >= MAX_SPEND_USD or headroom < MAX_SPEND_USD - reported:
        raise GateBlocked("current default-tenancy cost bound exceeds the approved $20 ceiling")
    return {"checkedAt": _utc(checked), "ageSeconds": age, "ec2OnDemandUsdPerHour": str(hourly),
            "computedBoundUsd": str(computed.quantize(Decimal("0.001"))), "reportedBoundUsd": str(reported),
            "headroomUsd": str(headroom), "ceilingUsd": str(MAX_SPEND_USD), "tenancy": "default", "spot": False,
            "source": "live-adapter" if current_pricing is not None else "policy-price-snapshot"}


def validate_repo_url(repo_url: str) -> str:
    if type(repo_url) is not str or repo_url.strip().removesuffix("/") != CANONICAL_REPO_URL:
        raise GateBlocked(f"repository URL must be exactly {CANONICAL_REPO_URL}")
    return CANONICAL_REPO_URL


def _git_run(repo_root: Path, args: Sequence[str]) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(["git", *args], cwd=repo_root, text=True, capture_output=True, timeout=30, check=False)
    except (OSError, subprocess.SubprocessError) as error:
        raise GateBlocked(f"git command failed to start: {error}") from error


def validate_authorization(policy: Mapping[str, Any], repo_root: Path = ROOT, authorization_ref: str | None = None,
                           *, git_runner: Callable[[Path, Sequence[str]], subprocess.CompletedProcess[str]] | None = None) -> dict[str, Any]:
    if type(authorization_ref) is not str or not AUTHORIZATION_REF_RE.fullmatch(authorization_ref):
        raise GateBlocked("launch requires a full 40-hex authorization ref")
    stated = _obj(policy.get("launchGate"), "launchGate").get("authorizationRef")
    if stated is not None and stated != authorization_ref:
        raise GateBlocked("launch authorizationRef disagrees with the policy")
    if not repo_root.is_dir():
        raise GateBlocked(f"authorization checkout does not exist: {repo_root}")
    run_git = git_runner or _git_run

    def checked(args: Sequence[str], label: str) -> str:
        result = run_git(repo_root, args)
        if result.returncode != 0:
            raise GateBlocked(f"{label} failed: {(result.stderr or result.stdout or '').strip()[:300]}")
        return result.stdout.strip()

    if checked(["rev-parse", "--verify", "HEAD"], "checkout identity") != authorization_ref:
        raise GateBlocked("checkout HEAD does not equal authorizationRef")
    if checked(["status", "--porcelain=v1", "--untracked-files=all"], "checkout cleanliness"):
        raise GateBlocked("authorization checkout is dirty")
    published = checked(["ls-remote", CANONICAL_REPO_URL], "published authorization lookup")
    if not any(line.split()[:1] == [authorization_ref] for line in published.splitlines()):
        raise GateBlocked("authorization commit is not present on the published origin")
    pins = _obj(policy.get("pins"), "pins"); reviewed = pins.get("reviewedCodeCommit")
    if type(reviewed) is not str or not re.fullmatch(r"[0-9a-f]{40}", reviewed):
        raise GateBlocked("reviewedCodeCommit is not a full pinned commit")
    if reviewed != authorization_ref:
        checked(["merge-base", "--is-ancestor", reviewed, authorization_ref], "reviewed commit pin")
    try:
        toolchain = (repo_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        manifest, _ = _read_json(repo_root / "lake-manifest.json", "lake-manifest")
    except OSError as error:
        raise GateBlocked(f"pinned checkout files cannot be read: {error}") from error
    if toolchain != EXPECTED_LEAN_TOOLCHAIN:
        raise GateBlocked("lean-toolchain does not match the approved pin")
    mathlib = [x.get("rev") for x in manifest.get("packages", []) if isinstance(x, dict) and x.get("name") == "mathlib"]
    if mathlib != [EXPECTED_MATHLIB_COMMIT]:
        raise GateBlocked("lake-manifest Mathlib revision does not match the approved pin")
    return {"authorizationRef": authorization_ref, "published": True, "clean": True,
            "reviewedCodeCommit": reviewed, "leanToolchain": toolchain, "mathlibCommit": EXPECTED_MATHLIB_COMMIT}


def fresh_run_id(now: datetime | None = None) -> str:
    current = (now or datetime.now(timezone.utc)).astimezone(timezone.utc).replace(microsecond=0)
    return f"{current.strftime('%Y%m%dT%H%M%SZ')}-{secrets.token_hex(16)}"


def validate_run_id(run_id: str, now: datetime | None = None) -> str:
    if type(run_id) is not str or not RUN_ID_RE.fullmatch(run_id):
        raise GateBlocked("run ID must be a UTC timestamp plus a fresh 16-byte nonce encoded as 32 lowercase hex characters")
    if now is not None:
        timestamp = datetime.strptime(run_id[:16], "%Y%m%dT%H%M%SZ").replace(tzinfo=timezone.utc)
        age = (now.astimezone(timezone.utc) - timestamp).total_seconds()
        if age < 0 or age > 300:
            raise GateBlocked("run ID timestamp is stale or in the future; create a fresh nonce")
    return run_id


def evidence_prefix(run_id: str) -> str:
    return f"aws-linux-pilot/{validate_run_id(run_id)}/"


def stack_name(authorization_ref: str) -> str:
    if not AUTHORIZATION_REF_RE.fullmatch(authorization_ref):
        raise PilotError("stack name requires a full authorization ref")
    return STACK_PREFIX + authorization_ref


def client_request_token(authorization_ref: str) -> str:
    return hashlib.sha256(stack_name(authorization_ref).encode()).hexdigest()


ec2_client_token = client_request_token


def _json(value: object) -> str:
    return json.dumps(value, separators=(",", ":"))


def _parameter(key: str, value: object) -> str:
    if type(value) is not str or not value or any(c in value for c in "\x00\r\n"):
        raise PilotError(f"CloudFormation parameter {key} is invalid")
    return f"ParameterKey={key},ParameterValue={value}"


def build_worker_commands(*, repo_url: str, authorization_ref: str, run_id: str, not_after: datetime,
                          input_root: str, output_root: str, worker_id: str) -> list[str]:
    """Build one bounded worker script with conditional, append-only evidence puts."""
    repo_url = validate_repo_url(repo_url)
    if not AUTHORIZATION_REF_RE.fullmatch(authorization_ref):
        raise GateBlocked("worker requires the full authorization ref")
    validate_run_id(run_id)
    for label, value in {"input_root": input_root, "output_root": output_root, "worker_id": worker_id}.items():
        if type(value) is not str or not value or any(c in value for c in "\x00\r\n"):
            raise PilotError(f"{label} must be a nonempty one-line value")
    if input_root != f".lake/search-free-mathlib/aws-linux-pilot/{run_id}" or output_root != f".lake/boundary-materialization/aws-linux-pilot/{run_id}":
        raise PilotError("worker paths must be the exact fresh run paths")
    q = {k: shlex.quote(v) for k, v in {"repo": repo_url, "ref": authorization_ref, "run": run_id,
         "input": input_root, "output": output_root, "worker": worker_id}.items()}
    modules = " ".join(f"--module {shlex.quote(x)}" for x in PILOT_MODULES)
    return [
        "set -Eeuo pipefail",
        "export HOME=/root",
        "dnf install -y git gcc gcc-c++ make gmp-devel libffi-devel zstd libzstd-devel sqlite jq python3 tar gzip openssl-devel awscli-2",
        "test -x \"$(command -v curl)\"",
        "test \"$(uname -s)\" = Linux", "test \"$(uname -m)\" = x86_64",
        f"test \"$(awk '/^MemTotal:/ {{printf \"%.0f\", $2 * 1024}}' /proc/meminfo)\" -ge {MINIMUM_GUEST_MEMORY_BYTES}",
        f"test \"$(awk '/^MemAvailable:/ {{printf \"%.0f\", $2 * 1024}}' /proc/meminfo)\" -ge {MINIMUM_AVAILABLE_MEMORY_BYTES}",
        f"test \"$(df --output=avail -B1 . | tail -1)\" -ge {MINIMUM_FREE_BYTES}",
        "mkdir -p /var/lib/explicit-lean-pilot", "uname -a > /var/lib/explicit-lean-pilot/uname.txt",
        "cat /etc/os-release > /var/lib/explicit-lean-pilot/os-release.txt",
        "metadata_token=$(curl --fail --silent --show-error --connect-timeout 5 --request PUT --header 'X-aws-ec2-metadata-token-ttl-seconds: 21600' http://169.254.169.254/latest/api/token)",
        "test -n \"$metadata_token\"",
        "curl --fail --silent --show-error --connect-timeout 5 --header \"X-aws-ec2-metadata-token: $metadata_token\" http://169.254.169.254/latest/meta-data/instance-id > /var/lib/explicit-lean-pilot/instance-id.txt",
        "aws sts get-caller-identity --output json > /var/lib/explicit-lean-pilot/aws-identity.json",
        f"printf '%s\\n' {shlex.quote(REGION)} > /var/lib/explicit-lean-pilot/aws-region.txt",
        "lsblk -b -o NAME,TYPE,SIZE,FSTYPE,MOUNTPOINT > /var/lib/explicit-lean-pilot/block-devices.txt",
        "rpm -qa --qf '%{NAME}-%{VERSION}-%{RELEASE}.%{ARCH}\\n' | sort > /var/lib/explicit-lean-pilot/package-versions.txt",
        f"printf '%s\\n' {_json(_utc(not_after))} > /var/lib/explicit-lean-pilot/not-after.txt",
        f"git clone --no-checkout {q['repo']} explicit-lean", "cd explicit-lean",
        f"export PILOT_AUTHORIZATION_REF={q['ref']}", "git checkout --detach \"$PILOT_AUTHORIZATION_REF\"",
        "PILOT_COMMIT=$(git rev-parse HEAD)", "test \"$PILOT_COMMIT\" = \"$PILOT_AUTHORIZATION_REF\"",
        "git ls-remote " + q["repo"] + " | awk '$1 == ENVIRON[\"PILOT_AUTHORIZATION_REF\"] {found=1} END {exit found ? 0 : 1}'",
        f"pilot_run={q['run']}", f"input_root={q['input']}", f"output_root={q['output']}",
        "mkdir -m 700 -p \"$input_root\" \"$output_root\"",
        "test ! -e \"$input_root/schema13-isolated-closed-manifest-v10.json\"", "test ! -e \"$output_root/attempts\"", "test ! -e \"$output_root/evidence.tar.gz\"", "test ! -e \"$output_root/worker-started.json\"", "test ! -e \"$output_root/run-exit.json\"",
        "printf '%s\\n' \"$PILOT_AUTHORIZATION_REF\" > \"$output_root/authorization-ref.txt\"", f"printf '%s\\n' {q['repo']} > \"$output_root/repository-url.txt\"", "printf '%s\\n' \"$PILOT_COMMIT\" > \"$output_root/pilot-commit.txt\"",
        f"evidence_bucket={shlex.quote(EVIDENCE_BUCKET)}", f"evidence_prefix={shlex.quote(evidence_prefix(run_id))}",
        "cp /var/lib/explicit-lean-pilot/uname.txt /var/lib/explicit-lean-pilot/os-release.txt /var/lib/explicit-lean-pilot/instance-id.txt /var/lib/explicit-lean-pilot/aws-identity.json /var/lib/explicit-lean-pilot/aws-region.txt /var/lib/explicit-lean-pilot/block-devices.txt /var/lib/explicit-lean-pilot/package-versions.txt /var/lib/explicit-lean-pilot/not-after.txt \"$output_root/\"",
        "upload_pilot_evidence() {", "  original_status=$?; set +e", "  evidence_status=0",
        "  tar -czf \"$output_root/evidence.tar.gz\" --ignore-failed-read \"$input_root/schema13-isolated-closed-manifest-v10.json\" \"$input_root/index-header-dependency-map.json\" \"$input_root/input-sha256.txt\" \"$input_root/manifest-verification.json\" \"$output_root/authorization-ref.txt\" \"$output_root/repository-url.txt\" \"$output_root/pilot-commit.txt\" \"$output_root/uname.txt\" \"$output_root/os-release.txt\" \"$output_root/instance-id.txt\" \"$output_root/aws-identity.json\" \"$output_root/aws-region.txt\" \"$output_root/block-devices.txt\" \"$output_root/package-versions.txt\" \"$output_root/not-after.txt\" \"$output_root/codex-version.txt\" \"$output_root/codex-login-status.txt\" \"$output_root/campaign-budget.json\" \"$output_root/process-metrics.json\" \"$output_root/worker.log\" \"$output_root/attempts\" 2>\"$output_root/evidence-tar.log\" || evidence_status=1",
        "  sha256sum \"$output_root/evidence.tar.gz\" > \"$output_root/evidence-sha256.txt\" || evidence_status=1",
        "  for file in \"$output_root/evidence.tar.gz\" \"$output_root/evidence-sha256.txt\" \"$output_root/process-metrics.json\" \"$output_root/worker.log\"; do",
        "    test -f \"$file\" || continue", "    relative=${file#./}",
        "    aws s3api put-object --bucket \"$evidence_bucket\" --key \"${evidence_prefix}$relative\" --body \"$file\" --if-none-match '*' --server-side-encryption AES256 --region " + EVIDENCE_REGION + " >/dev/null || evidence_status=1",
        "  done",
        "  printf '{\"runId\":\"%s\",\"originalExitCode\":%s,\"evidenceUploadFailed\":%s,\"uploadedAt\":\"%s\"}\\n' \"$pilot_run\" \"$original_status\" \"$([ \"$evidence_status\" -ne 0 ] && echo true || echo false)\" \"$(date -u +%FT%TZ)\" > \"$output_root/run-exit.json\"",
        "  aws s3api put-object --bucket \"$evidence_bucket\" --key \"${evidence_prefix}${output_root}/run-exit.json\" --body \"$output_root/run-exit.json\" --if-none-match '*' --server-side-encryption AES256 --region " + EVIDENCE_REGION + " >/dev/null || evidence_status=1",
        "  sync", "  if [ \"$evidence_status\" -ne 0 ] && [ \"$original_status\" -eq 0 ]; then original_status=125; fi",
        "  if [ \"$original_status\" -eq 0 ] && [ \"$evidence_status\" -eq 0 ]; then /usr/bin/systemctl poweroff; fi", "  exit \"$original_status\"", "}",
        "trap upload_pilot_evidence EXIT",
        "test -z \"$(git status --porcelain)\"", f"test \"$(cat lean-toolchain)\" = {shlex.quote(EXPECTED_LEAN_TOOLCHAIN)}",
        f"test \"$(jq -r '.packages[] | select(.name==\"mathlib\") | .rev' lake-manifest.json)\" = {shlex.quote(EXPECTED_MATHLIB_COMMIT)}",
        "if ! command -v elan >/dev/null 2>&1; then curl --fail --silent --show-error --location --proto '=https' --tlsv1.2 " + ELAN_URL + " -o /tmp/elan.tar.gz && printf '%s  %s\\n' " + ELAN_SHA256 + " /tmp/elan.tar.gz | sha256sum -c - && tar -xOzf /tmp/elan.tar.gz elan-init > /tmp/elan-init && chmod 0755 /tmp/elan-init && /tmp/elan-init -y --default-toolchain none; fi",
        'export PATH="$HOME/.elan/bin:$PATH"', "command -v elan", "elan toolchain install \"$(cat lean-toolchain)\"", "lake exe cache get",
        "command -v /usr/local/bin/codex", "codex --version > \"$output_root/codex-version.txt\"", "sudo -H codex login status > \"$output_root/codex-login-status.txt\"",
        "python3 -B Experiment/campaign_budget.py check > \"$output_root/campaign-budget.json\"", "jq -e '.canDispatch == true' \"$output_root/campaign-budget.json\" >/dev/null",
        "python3 -B Experiment/check_campaign_supervisor_v10.py", "python3 -B Experiment/check_campaign_worker.py", "python3 -B Experiment/check_translation_index.py", "python3 -B Experiment/check_linux_process_sampler.py", "python3 -B Experiment/check_simp_engine_boundary.py", "python3 -B Experiment/campaign_budget.py check",
        "manifest=\"$input_root/schema13-isolated-closed-manifest-v10.json\"", "depmap=\"$input_root/index-header-dependency-map.json\"", "database=\"$input_root/translation-index.sqlite3\"",
        "python3 -B Experiment/simp_engine_boundary_corpus.py manifest --output \"$manifest\" --commit \"$PILOT_COMMIT\" --checkpoint-root \"$input_root/manifest-checkpoints\"", "python3 -B Experiment/lean_import_index.py --manifest \"$manifest\" --source-root .lake/packages/mathlib --output \"$depmap\"", "python3 -B Experiment/translation_index.py init \"$database\"", "sha256sum \"$manifest\" \"$depmap\" > \"$input_root/input-sha256.txt\"",
        "manifest_sha=$(sha256sum \"$manifest\" | cut -d' ' -f1)", "toolchain_prefix=$(lake env lean --print-prefix)", 'lake_path="$toolchain_prefix/bin/lake"', 'lean_path="$toolchain_prefix/bin/lean"', 'export PATH="$toolchain_prefix/bin:$PATH"', 'lake_sha=$(sha256sum "$lake_path" | cut -d\' \' -f1)', 'lean_sha=$(sha256sum "$lean_path" | cut -d\' \' -f1)',
        "python3 -B Experiment/verify_simp_boundary_manifest.py verify \"$manifest\" --repository-root . --mathlib-root .lake/packages/mathlib --expected-repository-commit \"$PILOT_COMMIT\" --expected-sha256 \"$manifest_sha\" --dependency-map \"$depmap\" --lake-path \"$lake_path\" --expected-lake-sha256 \"$lake_sha\" --lean-path \"$lean_path\" --expected-lean-sha256 \"$lean_sha\" > \"$input_root/manifest-verification.json\"",
        "printf '{\"runId\":\"%s\",\"startedAt\":\"%s\"}\\n' \"$pilot_run\" \"$(date -u +%FT%TZ)\" > \"$output_root/worker-started.json\"",
        "aws s3api put-object --bucket \"$evidence_bucket\" --key \"${evidence_prefix}worker-started.json\" --body \"$output_root/worker-started.json\" --if-none-match '*' --server-side-encryption AES256 --region " + EVIDENCE_REGION,
        f"python3 -B Experiment/linux_process_sampler.py --metrics \"$output_root/process-metrics.json\" --log \"$output_root/worker.log\" --timeout {WORKER_SAMPLER_TIMEOUT_SECONDS} -- python3 -B Experiment/campaign_worker.py --database \"$database\" --manifest \"$manifest\" --dependency-map \"$depmap\" --output-root \"$output_root/attempts\" " + f"--worker {q['worker']} --max-modules {len(PILOT_MODULES)} --module-timeout 1800 --max-seconds {MAX_WORKER_SECONDS} --minimum-free-bytes {MINIMUM_FREE_BYTES} {modules}",
    ]


def build_auth_probe_commands(*, repo_url: str, authorization_ref: str, run_id: str,
                              not_after: datetime) -> list[str]:
    """Build a root-only, non-worker SSM proof probe for the same run."""
    repo_url = validate_repo_url(repo_url)
    if not AUTHORIZATION_REF_RE.fullmatch(authorization_ref):
        raise GateBlocked("auth probe requires the full authorization ref")
    validate_run_id(run_id)
    q = {k: shlex.quote(v) for k, v in {"repo": repo_url, "ref": authorization_ref, "run": run_id,
         "deadline": _utc(not_after)}.items()}
    checkout = "/var/lib/explicit-lean-pilot/auth-checkout"
    return [
        "set -Eeuo pipefail",
        "cloud-init status --wait",
        "test -f /var/lib/explicit-lean-pilot/shutdown-installed",
        "test \"$(cat /var/lib/explicit-lean-pilot/shutdown-run-id)\" = " + q["run"],
        "test \"$(cat /var/lib/explicit-lean-pilot/shutdown-deadline)\" = " + q["deadline"],
        "systemctl is-enabled --quiet explicit-lean-pilot-shutdown.timer",
        "systemctl is-active --quiet explicit-lean-pilot-shutdown.timer",
        "test -x /usr/local/bin/codex",
        "/usr/local/bin/codex login status >/dev/null",
        "test -d " + checkout,
        "test \"$(git -C " + checkout + " rev-parse HEAD)\" = " + q["ref"],
        "test \"$(git -C " + checkout + " remote get-url origin)\" = " + q["repo"],
        "test -z \"$(git -C " + checkout + " status --porcelain --untracked-files=all)\"",
        "cd " + checkout,
        "python3 -B Experiment/campaign_budget.py check > /var/lib/explicit-lean-pilot/auth-budget.json",
        "jq -e '.canDispatch == true' /var/lib/explicit-lean-pilot/auth-budget.json >/dev/null",
    ]


def load_template(path: Path = TEMPLATE_PATH) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as error:
        raise PilotError(f"cannot read CloudFormation template {path}: {error}") from error


def validate_template_invariants(template: str | None = None) -> dict[str, Any]:
    text = load_template() if template is None else template
    required = {"AWS::EC2::SecurityGroup", "AWS::EC2::Instance", "AWS::IAM::Role", "AWS::IAM::InstanceProfile", "AWS::Scheduler::Schedule", "TerminationRole", "Tenancy: default", "VolumeType: gp3", "VolumeSize: 200", "DeleteOnTermination: true", "Encrypted: true", "MaximumRetryAttempts: 0", "AmazonSSMManagedInstanceCore", "HttpTokens: required", "Ref: RootDeviceName", "FlexibleTimeWindow", "ScheduleExpressionTimezone: UTC", "at(${NotAfter})", "OnCalendar=$(printf '%s\\n' '${NotAfter}' | tr 'T' ' ') UTC", CODEX_URL, CODEX_SHA512_HEX, "auth-checkout", "git clone --no-checkout"}
    forbidden = {"SecurityGroupIngress", "KeyName", "InstanceMarketOptions", "SpotOptions", "Dedicated", "ec2:RunInstances", "s3:DeleteObject", "s3:PutObjectAcl", "ActionAfterCompletion", "OnCalendar=${NotAfter} UTC"}
    missing, present = sorted(x for x in required if x not in text), sorted(x for x in forbidden if x in text)
    if not re.search(r"(?m)^\s+Mode:\s*'OFF'\s*$", text): present.append("scheduler Mode must be quoted 'OFF'")
    if not re.search(r"(?m)^\s+MaximumRetryAttempts:\s*0\s*$", text): present.append("scheduler MaximumRetryAttempts must be numeric zero")
    if missing or present:
        detail = (["missing " + ", ".join(missing)] if missing else []) + (["forbidden " + ", ".join(present)] if present else [])
        raise GateBlocked("CloudFormation invariant failure: " + "; ".join(detail))
    return {"ok": True, "resources": 6, "noIngress": True, "defaultTenancy": True, "oneTimeTtl": True, "schedulerMode": "OFF", "schedulerActionAfterCompletion": False, "managedSsmPolicy": True, "imdsV2": True, "rootDeviceParameterized": True, "pinnedCodex": True}


@dataclass(frozen=True)
class AwsResponse:
    command: tuple[str, ...]
    payload: dict[str, Any]
    stdout: str = ""
    stderr: str = ""
    returncode: int = 0


Runner = Callable[[Sequence[str]], object]


class AwsClient:
    def __init__(self, *, runner: Runner | None = None, allow_mutations: bool = False, profile: str = PROFILE, region: str = REGION, timeout_seconds: int = 60) -> None:
        if profile != PROFILE or region != REGION: raise PilotError("AWS profile/region are fixed to explicit-lean-pilot/us-west-1")
        self.runner, self.allow_mutations, self.profile, self.region = runner or self._run, allow_mutations, profile, region
        self.timeout_seconds, self.calls = timeout_seconds, []

    def _run(self, command: Sequence[str]) -> subprocess.CompletedProcess[str]:
        return subprocess.run(list(command), cwd=ROOT, text=True, capture_output=True, timeout=self.timeout_seconds, check=False)

    def call(self, service: str, operation: str, arguments: Sequence[str] = (), *, mutation: bool = False, service_region: str | None = None) -> dict[str, Any]:
        if mutation and not self.allow_mutations: raise PilotError(f"mutation {service} {operation} is disabled outside explicit confirmation")
        effective = self.region if service_region is None else service_region
        if service_region is not None and (service, service_region) != ("pricing", "us-east-1"): raise PilotError("only the pricing read may use the us-east-1 API endpoint")
        command = ("aws", "--profile", self.profile, "--region", effective, service, operation, *map(str, arguments), "--output", "json"); self.calls.append((command, mutation))
        try: result = self.runner(command)
        except (OSError, subprocess.SubprocessError) as error: raise PilotError(f"AWS CLI failed to start: {error}") from error
        if isinstance(result, AwsResponse): return result.payload
        if isinstance(result, Mapping): return _obj(dict(result), "AWS response")
        code, stdout, stderr = getattr(result, "returncode", None), getattr(result, "stdout", ""), getattr(result, "stderr", "")
        if code != 0: raise PilotError(f"AWS CLI failed ({code}): {(stderr or stdout).strip()[:400]}")
        try: return _obj(json.loads(stdout or "{}"), "AWS response")
        except json.JSONDecodeError as error: raise PilotError("AWS CLI returned invalid JSON") from error


def _price(response: Mapping[str, Any], label: str) -> Decimal:
    if response.get("pricePerUnitUsd") is not None: return _dec(response["pricePerUnitUsd"], label)
    values: list[Decimal] = []
    for product in response.get("PriceList", []) if isinstance(response.get("PriceList"), list) else []:
        if isinstance(product, str):
            try: product = json.loads(product)
            except json.JSONDecodeError: continue
        if not isinstance(product, dict): continue
        terms = product.get("terms", {}).get("OnDemand", {}) if isinstance(product.get("terms"), dict) else {}
        for term in terms.values() if isinstance(terms, dict) else ():
            for dim in (term.get("priceDimensions", {}) if isinstance(term, dict) else {}).values():
                unit = dim.get("pricePerUnit", {}) if isinstance(dim, dict) else {}
                if isinstance(unit, dict) and unit.get("USD") is not None: values.append(_dec(unit["USD"], label))
    if len(values) != 1: raise GateBlocked(f"live {label} price did not resolve exactly one value")
    return values[0]


def _live_pricing(client: AwsClient, now: datetime, policy: Mapping[str, Any]) -> dict[str, Any]:
    location = "US West (N. California)"
    def read(service: str, filters: list[str]) -> Decimal:
        return _price(client.call("pricing", "get-products", ["--service-code", service, "--filters", *filters, "--max-results", "1"], service_region="us-east-1"), service)
    ec2 = read("AmazonEC2", ["Type=TERM_MATCH,Field=instanceType,Value=r7i.4xlarge", f"Type=TERM_MATCH,Field=location,Value={location}", "Type=TERM_MATCH,Field=operatingSystem,Value=Linux", "Type=TERM_MATCH,Field=tenancy,Value=Shared", "Type=TERM_MATCH,Field=preInstalledSw,Value=NA", "Type=TERM_MATCH,Field=capacitystatus,Value=Used"])
    gp3 = read("AmazonEC2", ["Type=TERM_MATCH,Field=productFamily,Value=Storage", f"Type=TERM_MATCH,Field=location,Value={location}", "Type=TERM_MATCH,Field=volumeApiName,Value=gp3"])
    ipv4 = read("AmazonVPC", [f"Type=TERM_MATCH,Field=location,Value={location}",
                              "Type=TERM_MATCH,Field=usagetype,Value=USW1-PublicIPv4:InUseAddress"])
    hours = Decimal(MAX_INSTANCE_LIFETIME_SECONDS) / Decimal(3600); total = ec2 * hours + gp3 * Decimal(VOLUME_SIZE_GIB) * hours / Decimal(30 * 24) + ipv4 * hours
    return {"checkedAt": _utc(now), "ec2OnDemandUsdPerHour": str(ec2), "gp3UsdPerGbMonth": str(gp3), "publicIpv4UsdPerHour": str(ipv4), "estimatedBoundedSubtotalUsd": str(total.quantize(Decimal("0.001"), rounding=ROUND_UP)), "unallocatedSpendHeadroomUsd": str(MAX_SPEND_USD - total), "tenancy": "default"}


def _identity(client: AwsClient) -> dict[str, Any]:
    value = client.call("sts", "get-caller-identity"); arn = value.get("Arn")
    if value.get("Account") != ACCOUNT_ID: raise GateBlocked(f"AWS account {value.get('Account')!r} is not {ACCOUNT_ID}")
    if type(arn) is not str or not arn or arn.endswith(":root"): raise GateBlocked("root or missing AWS principal is forbidden")
    return {"account": value["Account"], "arn": arn, "userId": value.get("UserId")}


def _instance_type(client: AwsClient) -> dict[str, Any]:
    rows = client.call("ec2", "describe-instance-types", ["--instance-types", INSTANCE_TYPE]).get("InstanceTypes")
    if not isinstance(rows, list) or len(rows) != 1 or not isinstance(rows[0], dict):
        raise GateBlocked("instance-type lookup was not exactly one response")
    row = rows[0]; memory = row.get("MemoryInfo"); processor = row.get("ProcessorInfo")
    size = memory.get("SizeInMiB") if isinstance(memory, dict) else None
    architectures = processor.get("SupportedArchitectures") if isinstance(processor, dict) else None
    if row.get("InstanceType") != INSTANCE_TYPE or type(size) is not int or size < 131072 or not isinstance(architectures, list) or "x86_64" not in architectures:
        raise GateBlocked("r7i.4xlarge must report at least 128 GiB and x86_64 support")
    return {"instanceType": INSTANCE_TYPE, "nominalMemoryBytes": size * 1024**2, "memorySizeMiB": size,
            "supportedArchitectures": architectures, "guestMemorySanityBytes": MINIMUM_GUEST_MEMORY_BYTES}


def _quota(client: AwsClient) -> dict[str, Any]:
    value = _dec(_obj(client.call("service-quotas", "get-service-quota", ["--service-code", "ec2", "--quota-code", "L-1216C47A"]).get("Quota"), "service quota").get("Value"), "On-Demand Standard vCPU quota")
    if value < 16: raise GateBlocked(f"On-Demand Standard vCPU quota is {value}, below required 16")
    return {"quotaCode": "L-1216C47A", "value": str(value), "required": 16}


def _fresh_ami(client: AwsClient) -> dict[str, Any]:
    value = _obj(client.call("ssm", "get-parameter", ["--name", AMI_PARAMETER]).get("Parameter"), "AMI parameter"); image_id = value.get("Value")
    if type(image_id) is not str or not AMI_ID_RE.fullmatch(image_id): raise GateBlocked("latest AMI parameter did not return an AMI ID")
    images = client.call("ec2", "describe-images", ["--image-ids", image_id, "--owners", "amazon"]).get("Images")
    if not isinstance(images, list) or len(images) != 1 or not isinstance(images[0], dict): raise GateBlocked("latest AMI lookup was not unique")
    image = images[0]
    if image.get("ImageId") != image_id or image.get("State") != "available" or image.get("Architecture") != "x86_64" or image.get("VirtualizationType") != "hvm" or image.get("RootDeviceType") != "ebs": raise GateBlocked("latest AMI is not available x86-64 EBS HVM")
    root = image.get("RootDeviceName")
    if type(root) is not str or not re.fullmatch(r"/dev/[A-Za-z0-9]+", root): raise GateBlocked("latest AMI omitted a valid root device")
    return {"imageId": image_id, "rootDeviceName": root, "name": image.get("Name")}


def _network(client: AwsClient) -> dict[str, str]:
    vpcs = client.call("ec2", "describe-vpcs", ["--filters", "Name=isDefault,Values=true"]).get("Vpcs")
    if not isinstance(vpcs, list) or len(vpcs) != 1 or not isinstance(vpcs[0], dict): raise GateBlocked("region must have exactly one default VPC")
    vpc, cidr = vpcs[0].get("VpcId"), vpcs[0].get("CidrBlock")
    subnets = client.call("ec2", "describe-subnets", ["--filters", f"Name=vpc-id,Values={vpc}", "Name=state,Values=available"]).get("Subnets")
    offerings = client.call("ec2", "describe-instance-type-offerings", ["--location-type", "availability-zone", "--filters", f"Name=instance-type,Values={INSTANCE_TYPE}"]).get("InstanceTypeOfferings")
    offered = {x.get("Location") for x in offerings or [] if isinstance(x, dict)}; choices = sorted((x for x in subnets or [] if isinstance(x, dict) and isinstance(x.get("SubnetId"), str) and x.get("AvailabilityZone") in offered), key=lambda x: (x["AvailabilityZone"], x["SubnetId"]))
    if type(vpc) is not str or type(cidr) is not str or not choices: raise GateBlocked("no usable default-VPC subnet offers the pilot instance")
    return {"vpcId": vpc, "cidr": cidr, "subnetId": choices[0]["SubnetId"], "availabilityZone": choices[0]["AvailabilityZone"]}


def _verify_bucket(client: AwsClient) -> dict[str, Any]:
    if client.call("s3api", "get-bucket-location", ["--bucket", EVIDENCE_BUCKET]).get("LocationConstraint") not in {None, EVIDENCE_REGION}: raise GateBlocked("evidence bucket is in the wrong region")
    if client.call("s3api", "get-bucket-versioning", ["--bucket", EVIDENCE_BUCKET]).get("Status") != "Enabled": raise GateBlocked("evidence bucket versioning is not enabled")
    public = _obj(client.call("s3api", "get-public-access-block", ["--bucket", EVIDENCE_BUCKET]).get("PublicAccessBlockConfiguration"), "public access block")
    if any(public.get(x) is not True for x in ("BlockPublicAcls", "IgnorePublicAcls", "BlockPublicPolicy", "RestrictPublicBuckets")): raise GateBlocked("evidence bucket does not block all public access")
    try:
        policy_status = client.call("s3api", "get-bucket-policy-status", ["--bucket", EVIDENCE_BUCKET])
    except PilotError as error:
        if "NoSuchBucketPolicy" not in str(error):
            raise
        policy_status = None
    if policy_status is not None and _obj(policy_status.get("PolicyStatus"), "bucket policy status").get("IsPublic") is not False:
        raise GateBlocked("evidence bucket policy is public or indeterminate")
    encryption = _obj(client.call("s3api", "get-bucket-encryption", ["--bucket", EVIDENCE_BUCKET]).get("ServerSideEncryptionConfiguration"), "bucket encryption")
    if not any(isinstance(x, dict) and isinstance(x.get("ApplyServerSideEncryptionByDefault"), dict) and x["ApplyServerSideEncryptionByDefault"].get("SSEAlgorithm") == "AES256" for x in encryption.get("Rules", [])): raise GateBlocked("evidence bucket has no SSE-S3 default encryption")
    ownership = _obj(client.call("s3api", "get-bucket-ownership-controls", ["--bucket", EVIDENCE_BUCKET]).get("OwnershipControls"), "ownership controls")
    if not any(isinstance(x, dict) and x.get("ObjectOwnership") == "BucketOwnerEnforced" for x in ownership.get("Rules", [])): raise GateBlocked("evidence bucket does not enforce bucket-owner ownership")
    return {"bucket": EVIDENCE_BUCKET, "region": EVIDENCE_REGION, "versioning": "Enabled", "publicAccessBlocked": True, "defaultEncryption": "AES256", "bucketOwnerEnforced": True, "uniquePrefix": True, "conditionalPut": True, "deletePermission": False}


def _instances(client: AwsClient, instance_id: str | None = None) -> list[dict[str, Any]]:
    response = client.call("ec2", "describe-instances", ["--instance-ids", instance_id] if instance_id else ["--filters", "Name=tag:Project,Values=explicit-lean"])
    return [x for reservation in response.get("Reservations", []) if isinstance(reservation, dict) for x in reservation.get("Instances", []) if isinstance(x, dict)]


def _verify_instance(instance: Mapping[str, Any], client: AwsClient | None = None, *, expected_root_device: str | None = None) -> dict[str, Any]:
    iid, root = instance.get("InstanceId"), instance.get("RootDeviceName")
    if type(iid) is not str or not INSTANCE_ID_RE.fullmatch(iid): raise PilotError("invalid instance ID")
    if instance.get("InstanceType") != INSTANCE_TYPE or (instance.get("Placement") or {}).get("Tenancy") != "default": raise GateBlocked("returned instance is not the default-tenancy r7i.4xlarge")
    if type(root) is not str or not re.fullmatch(r"/dev/[A-Za-z0-9]+", root) or (expected_root_device is not None and root != expected_root_device): raise GateBlocked("returned instance root device is invalid or unexpected")
    mapping = next((x for x in instance.get("BlockDeviceMappings", []) if isinstance(x, dict) and x.get("DeviceName") == root), None); ebs = mapping.get("Ebs") if isinstance(mapping, dict) else None
    if not isinstance(ebs, dict) or ebs.get("DeleteOnTermination") is not True: raise GateBlocked("returned root volume is not DeleteOnTermination")
    if client is not None:
        volume_id = ebs.get("VolumeId"); volumes = client.call("ec2", "describe-volumes", ["--volume-ids", volume_id]).get("Volumes") if isinstance(volume_id, str) and volume_id.startswith("vol-") else []
        if not isinstance(volumes, list) or len(volumes) != 1 or not isinstance(volumes[0], dict) or volumes[0].get("VolumeType") != VOLUME_TYPE or volumes[0].get("Size") != VOLUME_SIZE_GIB or volumes[0].get("Encrypted") is not True: raise GateBlocked("returned root volume is not encrypted 200-GiB gp3")
    return {"instanceId": iid, "instanceType": INSTANCE_TYPE, "tenancy": "default", "rootDeviceName": root, "volume": {"type": VOLUME_TYPE, "sizeGiB": VOLUME_SIZE_GIB, "encrypted": True, "deleteOnTermination": True}}


def _state_path(run_id: str, root: Path) -> Path:
    return root / f"{validate_run_id(run_id)}.json"


def _write_state(path: Path, value: Mapping[str, Any], *, exclusive: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if exclusive and path.exists(): raise PilotError(f"run state already exists: {path}")
    temporary = path.with_name(f".{path.name}.{secrets.token_hex(6)}.tmp")
    try:
        temporary.write_text(json.dumps(dict(value), indent=2, sort_keys=True) + "\n", encoding="utf-8"); os.chmod(temporary, 0o600); temporary.replace(path)
    finally: temporary.unlink(missing_ok=True)


def _read_state(path: Path) -> dict[str, Any]:
    return _read_json(path, "run state")[0]


def _budget() -> Mapping[str, Any]:
    try:
        result = subprocess.run([sys.executable, "-B", str(ROOT / "Experiment/campaign_budget.py"), "check"], cwd=ROOT, text=True, capture_output=True, timeout=35, check=False); value = json.loads(result.stdout)
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError) as error: raise GateBlocked(f"campaign budget check unavailable: {error}") from error
    if not isinstance(value, dict) or value.get("canDispatch") is not True: raise GateBlocked(f"campaign budget gate denied dispatch: {value.get('decision', 'unknown') if isinstance(value, dict) else 'invalid'}")
    return value


def _describe_stack(client: AwsClient, name: str) -> dict[str, Any] | None:
    try: response = client.call("cloudformation", "describe-stacks", ["--stack-name", name])
    except PilotError as error:
        if any(x in str(error).lower() for x in ("does not exist", "doesn't exist", "not exist")): return None
        raise
    stacks = response.get("Stacks")
    if not isinstance(stacks, list) or not stacks: return None
    if not isinstance(stacks[0], dict): raise PilotError("CloudFormation stack response is malformed")
    return stacks[0]


def _outputs(stack: Mapping[str, Any]) -> dict[str, str]:
    return {x["OutputKey"]: x["OutputValue"] for x in stack.get("Outputs", []) if isinstance(x, dict) and isinstance(x.get("OutputKey"), str) and isinstance(x.get("OutputValue"), str)}


def _pairs(stack: Mapping[str, Any], field: str, key: str, value: str) -> dict[str, str]:
    items = stack.get(field)
    if not isinstance(items, list) or not items: raise GateBlocked(f"CloudFormation stack omitted its {field.lower()}")
    result: dict[str, str] = {}
    for item in items:
        if not isinstance(item, dict) or type(item.get(key)) is not str or type(item.get(value)) is not str or item[key] in result: raise GateBlocked(f"CloudFormation stack {field.lower()} are malformed")
        result[item[key]] = item[value]
    return result


def _verify_stack(stack: Mapping[str, Any], *, name: str, authorization_ref: str, expected_deadline: datetime | None = None) -> dict[str, Any]:
    if stack.get("StackName") != name: raise GateBlocked("CloudFormation returned an unexpected stack name")
    status = stack.get("StackStatus")
    if status not in {"CREATE_IN_PROGRESS", "CREATE_COMPLETE"}: raise GateBlocked(f"deterministic stack is not usable: {status!r}")
    params, tags = _pairs(stack, "Parameters", "ParameterKey", "ParameterValue"), _pairs(stack, "Tags", "Key", "Value")
    if params.get("AuthorizationRef") != authorization_ref or tags.get("AuthorizationRef") != authorization_ref: raise GateBlocked("stack authorizationRef does not match")
    if tags.get("Project") != "explicit-lean" or tags.get("Pilot") != "aws-linux-pilot": raise GateBlocked("stack ownership tags do not identify this pilot")
    run = params.get("RunId")
    if type(run) is not str or tags.get("RunId") != run: raise GateBlocked("stack RunId parameter/tag disagree")
    validate_run_id(run)
    if params.get("RepoUrl") != CANONICAL_REPO_URL: raise GateBlocked("stack repository is not canonical")
    not_after = params.get("NotAfter")
    if type(not_after) is not str:
        raise GateBlocked("stack NotAfter parameter is malformed")
    deadline = _dt(not_after + "Z", "stack NotAfter")
    if expected_deadline is not None and deadline != expected_deadline.astimezone(timezone.utc).replace(microsecond=0): raise GateBlocked("stack deadline differs from authorization")
    if tags.get("NotAfter") != _utc(deadline): raise GateBlocked("stack NotAfter tag disagrees with parameter")
    root = params.get("RootDeviceName")
    image = params.get("ImageId")
    if type(root) is not str or not re.fullmatch(r"/dev/[A-Za-z0-9]+", root) or type(image) is not str or not AMI_ID_RE.fullmatch(image): raise GateBlocked("stack AMI/root parameters are invalid")
    outputs = _outputs(stack)
    if status == "CREATE_COMPLETE" and (not INSTANCE_ID_RE.fullmatch(outputs.get("InstanceId", "")) or outputs.get("EvidencePrefix") != evidence_prefix(run) or outputs.get("NotAfter") != _utc(deadline)): raise GateBlocked("complete stack outputs are inconsistent")
    return {"stackName": name, "status": status, "parameters": params, "tags": tags, "runId": run, "authorizationRef": authorization_ref, "notAfter": _utc(deadline), "outputs": outputs, "evidencePrefix": evidence_prefix(run)}


def validate_remote_auth_proof(path: Path | str | None, *, instance_id: str, now: datetime,
                               run_id: str | None = None) -> dict[str, Any]:
    if path is None: raise GateBlocked("start-worker requires a fresh --remote-auth-proof")
    proof, raw = _read_json(Path(path), "remote Codex auth proof")
    if proof.get("schema") != 1 or proof.get("strategy") != REMOTE_AUTH_STRATEGY: raise GateBlocked("remote auth proof must use the ssm-device-auth strategy")
    checked = _dt(proof.get("checkedAt"), "remote auth proof checkedAt", whole_seconds=False); age = (now.astimezone(timezone.utc) - checked).total_seconds()
    if age < 0 or age > REMOTE_AUTH_MAX_AGE_SECONDS: raise GateBlocked("remote auth proof is stale or from the future")
    if proof.get("instanceId") != instance_id: raise GateBlocked("remote auth proof is for a different instance")
    if run_id is not None and proof.get("runId") != run_id: raise GateBlocked("remote auth proof is for a different run")
    login = proof.get("codexLoginStatus"); budget = proof.get("campaignBudget"); logged = (isinstance(login, str) and login in {"logged_in", "authenticated", "ready"}) or (isinstance(login, dict) and login.get("loggedIn") is True)
    if not logged: raise GateBlocked("remote auth proof does not confirm codex login status")
    if not isinstance(budget, dict) or budget.get("canDispatch") is not True: raise GateBlocked("remote auth proof does not confirm an ordinary available budget")
    forbidden = {"auth", "authjson", "apikey", "accesskey", "accesstoken", "refreshtoken", "idtoken", "secret", "password", "token", "credential", "credentials", "cookie", "session"}
    def scan(value: object) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                if str(key).lower().replace("_", "").replace("-", "").replace(" ", "") in forbidden: raise GateBlocked("remote auth proof must not contain credentials or tokens")
                scan(child)
        elif isinstance(value, list):
            for child in value: scan(child)
    scan(proof)
    return {"path": str(path), "sha256": _sha256(raw), "strategy": REMOTE_AUTH_STRATEGY, "instanceId": instance_id, "checkedAt": _utc(checked), "ageSeconds": age, "codexLoginStatus": "verified", "campaignBudget": {"canDispatch": True, "decision": budget.get("decision", "continue")}}


def _active_hosts(client: AwsClient) -> list[dict[str, Any]]:
    response = client.call("ec2", "describe-instances", ["--filters", "Name=tag:Pilot,Values=aws-linux-pilot", "Name=instance-state-name,Values=pending,running,stopping,stopped"])
    return [x for reservation in response.get("Reservations", []) if isinstance(reservation, dict) for x in reservation.get("Instances", []) if isinstance(x, dict)]


@dataclass
class PilotController:
    policy_path: Path = POLICY_PATH
    repo_root: Path = ROOT
    state_root: Path = STATE_ROOT
    runner: Runner | None = None
    git_runner: Callable[[Path, Sequence[str]], subprocess.CompletedProcess[str]] | None = None
    now: Callable[[], datetime] = lambda: datetime.now(timezone.utc)
    sleep: Callable[[float], None] = time.sleep
    budget_check: Callable[[], Mapping[str, Any]] | None = None
    pricing_check: Callable[[], Mapping[str, Any]] | None = None
    session_runner: Callable[[Sequence[str]], subprocess.CompletedProcess[str]] | None = None

    def _policy_time(self) -> tuple[dict[str, Any], bytes, datetime]:
        policy, raw = load_policy(self.policy_path); return policy, raw, self.now()

    def _aws_gates(self, policy: Mapping[str, Any], now: datetime) -> tuple[dict[str, Any], AwsClient]:
        client = AwsClient(runner=self.runner); checks = {"identity": {"ok": True, **_identity(client)}}; deadline = parse_not_after(policy, now); pricing = self.pricing_check() if self.pricing_check else _live_pricing(client, now, policy)
        checks.update({"notAfter": {"ok": True, "value": _utc(deadline)}, "cost": {"ok": True, **validate_cost(policy, now, pricing)}, "quota": {"ok": True, **_quota(client)}, "instanceType": {"ok": True, **_instance_type(client)}, "ami": {"ok": True, **_fresh_ami(client)}, "network": {"ok": True, **_network(client)}, "evidenceBucket": {"ok": True, **_verify_bucket(client)}}); return checks, client

    def plan(self) -> dict[str, Any]:
        result: dict[str, Any] = {"schema": 2, "kind": "aws_linux_pilot_plan", "readOnly": True, "profile": PROFILE, "account": ACCOUNT_ID, "region": REGION, "runScope": {"instanceType": INSTANCE_TYPE, "nominalMemoryBytes": REQUIRED_MEMORY_BYTES, "guestMemorySanityBytes": MINIMUM_GUEST_MEMORY_BYTES, "tenancy": "default", "workers": 1, "modules": len(PILOT_MODULES)}, "checks": {}, "blockers": []}
        try:
            policy, raw, now = self._policy_time(); result["policySha256"] = _sha256(raw); result["checks"]["template"] = {"ok": True, **validate_template_invariants()}; checks, client = self._aws_gates(policy, now); result["checks"].update(checks); active = _active_hosts(client); result["checks"]["activeHosts"] = {"ok": not active, "count": len(active)}
            if active: result["blockers"].append("an active aws-linux-pilot host already exists")
            result["checks"]["authorization"] = {"ok": False, "detail": "full --authorization-ref is required for launch"}; result["blockers"].append("full --authorization-ref is required for launch"); result["awsCalls"] = len(client.calls)
        except PilotError as error: result.update({"error": str(error), "blockers": [str(error)]})
        result["ready"] = not result["blockers"]; return result

    def status(self, run_id: str | None = None) -> dict[str, Any]:
        result: dict[str, Any] = {"schema": 2, "kind": "aws_linux_pilot_status", "readOnly": True, "profile": PROFILE, "account": ACCOUNT_ID, "region": REGION, "checks": {}}; client = AwsClient(runner=self.runner)
        try:
            result["checks"]["identity"] = {"ok": True, **_identity(client)}
            if run_id is not None:
                validate_run_id(run_id); path = _state_path(run_id, self.state_root)
                if path.exists():
                    state = _read_state(path); result["runState"] = state; stack = _describe_stack(client, state.get("stackName", "")); result["checks"]["stack"] = {"ok": stack is not None, "stack": stack}
                    if stack:
                        outputs = _outputs(stack); iid = state.get("instanceId") or outputs.get("InstanceId")
                        if iid: result["checks"]["instance"] = {"ok": True, "instances": _instances(client, iid)}
                        if iid and (state.get("authProbeCommandId") or state.get("workerCommandId")):
                            ssm = {"ok": True}
                            if state.get("authProbeCommandId"): ssm["authProbeInvocation"] = client.call("ssm", "get-command-invocation", ["--command-id", state["authProbeCommandId"], "--instance-id", iid])
                            if state.get("workerCommandId"): ssm["invocation"] = client.call("ssm", "get-command-invocation", ["--command-id", state["workerCommandId"], "--instance-id", iid])
                            result["checks"]["ssm"] = ssm
                        prefix = state.get("evidencePrefix") or outputs.get("EvidencePrefix")
                        if prefix: result["checks"]["evidence"] = {"ok": True, "bucket": EVIDENCE_BUCKET, "prefix": prefix, "listing": client.call("s3api", "list-objects-v2", ["--bucket", EVIDENCE_BUCKET, "--prefix", prefix])}
            result["awsCalls"] = len(client.calls)
        except PilotError as error: result.update({"error": str(error), "awsCalls": len(client.calls)})
        return result

    def _wait_stack(self, client: AwsClient, name: str, timeout: int = 1800) -> dict[str, Any]:
        end = time.monotonic() + timeout
        while True:
            stack = _describe_stack(client, name)
            if stack is None: raise PilotError("CloudFormation stack disappeared during creation")
            status = stack.get("StackStatus")
            if status == "CREATE_COMPLETE": return stack
            if isinstance(status, str) and (status.endswith("_FAILED") or status.startswith("ROLLBACK")): raise PilotError(f"CloudFormation stack creation failed with {status}")
            if time.monotonic() >= end: raise PilotError("CloudFormation stack did not become ready before the bounded wait")
            self.sleep(5)

    def _wait_ssm(self, client: AwsClient, iid: str, timeout: int = 600) -> None:
        end = time.monotonic() + timeout
        while True:
            values = client.call("ssm", "describe-instance-information", ["--filters", f"Key=InstanceIds,Values={iid}"]).get("InstanceInformationList", [])
            if any(isinstance(x, dict) and x.get("InstanceId") == iid and x.get("PingStatus") == "Online" for x in values): return
            if time.monotonic() >= end: raise PilotError("SSM agent did not become online before the bounded wait")
            self.sleep(5)

    def _wait_command(self, client: AwsClient, command_id: str, iid: str, timeout: int = 600) -> dict[str, Any]:
        terminal = {"Success", "Cancelled", "TimedOut", "Failed", "Cancelling", "Undeliverable", "Terminated"}; end = time.monotonic() + timeout
        while True:
            try:
                invocation = _obj(client.call("ssm", "get-command-invocation", ["--command-id", command_id, "--instance-id", iid]), "SSM command invocation")
            except PilotError as error:
                if "InvocationDoesNotExist" not in str(error): raise
                if time.monotonic() >= end: raise PilotError("SSM command invocation did not become visible before the bounded wait") from error
                self.sleep(5); continue
            if invocation.get("Status") in terminal: return invocation
            if time.monotonic() >= end: raise PilotError("SSM command did not reach a terminal state before the bounded wait")
            self.sleep(5)

    def _delete_stack(self, client: AwsClient, name: str) -> dict[str, Any]:
        cleanup = {"attempted": True, "requested": False, "stackName": name}
        try: client.call("cloudformation", "delete-stack", ["--stack-name", name], mutation=True)
        except PilotError as error: cleanup.update({"error": str(error)[:500], "manualAttention": True})
        else: cleanup["requested"] = True
        return cleanup

    def _send(self, client: AwsClient, iid: str, commands: Sequence[str], run_id: str, *, not_after: datetime) -> str:
        execution_timeout = worker_execution_timeout_seconds(not_after=not_after, now=self.now())
        response = client.call("ssm", "send-command", ["--document-name", "AWS-RunShellScript", "--instance-ids", iid, "--comment", f"explicit-lean-pilot {run_id} bounded-worker", "--parameters", _json({"commands": list(commands), "executionTimeout": [str(execution_timeout)]}), "--timeout-seconds", str(WORKER_SAMPLER_TIMEOUT_SECONDS)], mutation=True); command = _obj(response.get("Command"), "SSM command"); value = command.get("CommandId")
        if type(value) is not str or not value: raise PilotError("SSM send-command did not return a command ID")
        return value

    def _send_auth_probe(self, client: AwsClient, iid: str, commands: Sequence[str], run_id: str) -> str:
        response = client.call("ssm", "send-command", ["--document-name", "AWS-RunShellScript", "--instance-ids", iid, "--comment", f"explicit-lean-pilot {run_id} auth-postcheck", "--parameters", _json({"commands": list(commands)}), "--timeout-seconds", "600"], mutation=True); command = _obj(response.get("Command"), "SSM auth probe"); value = command.get("CommandId")
        if type(value) is not str or not value: raise PilotError("SSM auth probe did not return a command ID")
        return value

    def _instance(self, client: AwsClient, identity: Mapping[str, Any]) -> tuple[str, dict[str, Any]]:
        iid = _obj(identity["outputs"], "stack outputs").get("InstanceId"); rows = _instances(client, iid) if isinstance(iid, str) else []
        if len(rows) != 1: raise GateBlocked("stack did not return exactly one instance")
        return iid, _verify_instance(rows[0], client, expected_root_device=identity["parameters"]["RootDeviceName"])

    def _state_for(self, identity: Mapping[str, Any], *, policy_sha: str, token: str, phase: str) -> dict[str, Any]:
        p = identity["parameters"]
        return {"schema": 2, "kind": "aws_linux_pilot_run", "runId": identity["runId"], "stackName": identity["stackName"], "clientRequestToken": token, "profile": PROFILE, "account": ACCOUNT_ID, "region": REGION, "policySha256": policy_sha, "authorizationRef": identity["authorizationRef"], "repoUrl": p["RepoUrl"], "notAfter": identity["notAfter"], "evidencePrefix": identity["evidencePrefix"], "phase": phase, "stackStatus": identity["status"], "outputs": identity["outputs"], "imageId": p["ImageId"], "rootDeviceName": p["RootDeviceName"], "workerCount": 1, "instanceType": INSTANCE_TYPE, "tenancy": "default", "volume": {"type": VOLUME_TYPE, "sizeGiB": VOLUME_SIZE_GIB, "encrypted": True, "deleteOnTermination": True}}

    def _existing(self, client: AwsClient, identity: Mapping[str, Any], requested: str, *, token: str, policy_sha: str) -> dict[str, Any]:
        actual, path = identity["runId"], _state_path(identity["runId"], self.state_root); existed = path.exists(); state = _read_state(path) if existed else self._state_for(identity, policy_sha=policy_sha, token=token, phase="existing-stack")
        if state.get("authorizationRef") != identity["authorizationRef"] or state.get("runId") != actual: raise GateBlocked("local state does not match deterministic stack")
        if identity["status"] == "CREATE_COMPLETE": iid, shape = self._instance(client, identity); state.update({"instanceId": iid, "instanceShape": shape})
        _write_state(path, state, exclusive=not existed)
        return {"schema": 2, "kind": "aws_linux_pilot_launch", "readOnly": True, "idempotent": True, "runId": actual, "requestedRunId": requested, "state": state, "statePath": str(path)}

    def launch(self, *, repo_url: str, authorization_ref: str | None = None, run_id: str | None = None, confirm_launch: bool = False, dry_run: bool = False) -> dict[str, Any]:
        if not confirm_launch and not dry_run: raise PilotError("AWS mutations require --confirm-launch")
        repo_url = validate_repo_url(repo_url)
        if type(authorization_ref) is not str or not AUTHORIZATION_REF_RE.fullmatch(authorization_ref): raise GateBlocked("launch requires --authorization-ref with a full 40-hex commit")
        policy, raw, now = self._policy_time(); chosen = validate_run_id(run_id, now) if run_id else fresh_run_id(now); deadline = parse_not_after(policy, now); authorization = validate_authorization(policy, self.repo_root, authorization_ref, git_runner=self.git_runner)
        build_worker_commands(repo_url=repo_url, authorization_ref=authorization_ref, run_id=chosen, not_after=deadline, input_root=f".lake/search-free-mathlib/aws-linux-pilot/{chosen}", output_root=f".lake/boundary-materialization/aws-linux-pilot/{chosen}", worker_id=f"aws-linux-pilot-{chosen}")
        checks, client = self._aws_gates(policy, now); checks["authorization"] = {"ok": True, **authorization}; checks["campaignBudget"] = dict((self.budget_check or _budget)())
        if checks["campaignBudget"].get("canDispatch") is not True: raise GateBlocked("campaign budget gate denied dispatch")
        checks["template"] = {"ok": True, **validate_template_invariants()}; name, token = stack_name(authorization_ref), client_request_token(authorization_ref); path = _state_path(chosen, self.state_root)
        if path.exists():
            stack = _describe_stack(client, name)
            if stack is None: raise GateBlocked("local run state exists but its deterministic stack is absent")
            identity = _verify_stack(stack, name=name, authorization_ref=authorization_ref, expected_deadline=deadline)
            if identity["runId"] != chosen: raise GateBlocked("local run state nonce differs from deterministic stack")
            return self._existing(client, identity, chosen, token=token, policy_sha=_sha256(raw))
        existing = _describe_stack(client, name)
        if existing is not None: return self._existing(client, _verify_stack(existing, name=name, authorization_ref=authorization_ref, expected_deadline=deadline), chosen, token=token, policy_sha=_sha256(raw))
        active = _active_hosts(client)
        if active: raise GateBlocked(f"an active aws-linux-pilot host already exists: {[x.get('InstanceId') for x in active]}")
        if dry_run: return {"schema": 2, "kind": "aws_linux_pilot_launch", "readOnly": True, "dryRun": True, "runId": chosen, "stackName": name, "checks": checks, "awsCalls": len(client.calls)}
        deadline = parse_not_after(policy, self.now()); network, ami = checks["network"], checks["ami"]
        state: dict[str, Any] = {"schema": 2, "kind": "aws_linux_pilot_run", "runId": chosen, "stackName": name, "clientRequestToken": token, "profile": PROFILE, "account": ACCOUNT_ID, "region": REGION, "policySha256": _sha256(raw), "authorizationRef": authorization_ref, "repoUrl": repo_url, "notAfter": _utc(deadline), "evidencePrefix": evidence_prefix(chosen), "phase": "creating-stack", "workerCount": 1, "instanceType": INSTANCE_TYPE, "tenancy": "default", "imageId": ami["imageId"], "rootDeviceName": ami["rootDeviceName"], "volume": {"type": VOLUME_TYPE, "sizeGiB": VOLUME_SIZE_GIB, "encrypted": True, "deleteOnTermination": True}}; _write_state(path, state, exclusive=True)
        mutating = AwsClient(runner=self.runner, allow_mutations=True); stack_created = False
        try:
            params = [_parameter("ImageId", ami["imageId"]), _parameter("RootDeviceName", ami["rootDeviceName"]), _parameter("VpcId", network["vpcId"]), _parameter("SubnetId", network["subnetId"]), _parameter("RunId", chosen), _parameter("NotAfter", _utc(deadline).removesuffix("Z")), _parameter("RepoUrl", repo_url), _parameter("AuthorizationRef", authorization_ref)]
            args = ["--stack-name", name, "--template-body", f"file://{TEMPLATE_PATH}", "--parameters", *params, "--capabilities", "CAPABILITY_NAMED_IAM", "--on-failure", "DELETE", "--client-request-token", token, "--tags", _json([{"Key": "Project", "Value": "explicit-lean"}, {"Key": "Pilot", "Value": "aws-linux-pilot"}, {"Key": "RunId", "Value": chosen}, {"Key": "AuthorizationRef", "Value": authorization_ref}, {"Key": "NotAfter", "Value": _utc(deadline)}])]
            try:
                response = mutating.call("cloudformation", "create-stack", args, mutation=True)
                if type(response.get("StackId")) is not str or not response["StackId"]: raise PilotError("create-stack response omitted StackId")
            except Exception as create_error:
                try: raced = _describe_stack(mutating, name)
                except Exception as reconcile_error:
                    state.update({"phase": "create-ambiguous", "manualAttention": True, "createError": str(create_error)[:500], "reconciliationError": str(reconcile_error)[:500]}); _write_state(path, state); raise PilotError("create-stack outcome is ambiguous; reconciliation failed") from create_error
                if raced is None:
                    state.update({"phase": "create-ambiguous", "manualAttention": True, "createError": str(create_error)[:500], "reconciliation": "stack-not-visible-after-create-error"}); _write_state(path, state); raise PilotError("create-stack outcome is ambiguous; stack was not visible") from create_error
                try: identity = _verify_stack(raced, name=name, authorization_ref=authorization_ref, expected_deadline=deadline)
                except Exception as reconcile_error:
                    state.update({"phase": "create-ambiguous", "manualAttention": True, "createError": str(create_error)[:500], "reconciliationError": str(reconcile_error)[:500]}); _write_state(path, state); raise PilotError("create-stack outcome is ambiguous; stack failed reconciliation") from reconcile_error
                if identity["runId"] != chosen: state.pop("evidencePrefix", None); state.update({"phase": "create-raced-existing", "manualAttention": True, "originalRunId": identity["runId"]}); _write_state(path, state)
                return self._existing(mutating, identity, chosen, token=token, policy_sha=_sha256(raw))
            stack_created = True; stack = self._wait_stack(mutating, name); identity = _verify_stack(stack, name=name, authorization_ref=authorization_ref, expected_deadline=deadline); iid, shape = self._instance(mutating, identity)
            if identity["runId"] != chosen: raise GateBlocked("created stack RunId differs from the requested fresh run")
            state.update({"stackStatus": identity["status"], "outputs": identity["outputs"], "instanceId": iid, "availabilityZone": network["availabilityZone"], "vpcId": network["vpcId"], "subnetId": network["subnetId"], "instanceShape": shape, "phase": "stack-created"}); _write_state(path, state); self._wait_ssm(mutating, iid); state.update({"phase": "awaiting-codex-auth", "authInstructions": "Run auth --confirm-auth, complete codex login --device-auth in Session Manager, then provide --remote-auth-proof to start-worker."}); _write_state(path, state)
            return {"schema": 2, "kind": "aws_linux_pilot_launch", "readOnly": False, "runId": chosen, "stackName": name, "instanceId": iid, "phase": "awaiting-codex-auth", "checks": checks, "statePath": str(path)}
        except Exception as error:
            state["error"] = str(error)[:500]
            if stack_created:
                cleanup = self._delete_stack(mutating, name); state.update({"phase": "failed-before-worker", "stackCleanup": cleanup});
                if cleanup.get("error"): state["manualAttention"] = True
            elif not state.get("phase", "").startswith("create-"): state["phase"] = "failed-before-stack"
            _write_state(path, state)
            if isinstance(error, PilotError) and isinstance(state.get("stackCleanup"), dict) and state["stackCleanup"].get("error"): raise PilotError(f"{error}; stack cleanup failed: {state['stackCleanup']['error']}") from error
            raise error if isinstance(error, PilotError) else PilotError(str(error))

    def auth(self, *, run_id: str, confirm_auth: bool = False) -> dict[str, Any]:
        if not confirm_auth: raise PilotError("the interactive auth session requires --confirm-auth")
        validate_run_id(run_id); path = _state_path(run_id, self.state_root)
        if not path.exists(): raise GateBlocked("auth requires an existing launched run state")
        state = _read_state(path); ref = state.get("authorizationRef")
        if type(ref) is not str or state.get("runId") != run_id or state.get("stackName") != stack_name(ref) or state.get("phase") not in {"awaiting-codex-auth", "awaiting-codex-auth-proof"}: raise GateBlocked("run state is not ready for device auth")
        current_deadline = parse_not_after(load_policy(self.policy_path)[0], self.now())
        if current_deadline != _dt(state["notAfter"], "run notAfter"): raise GateBlocked("run deadline differs from the authorized deadline")
        client = AwsClient(runner=self.runner); _identity(client); stack = _describe_stack(client, state["stackName"])
        if stack is None: raise GateBlocked("launched stack is absent")
        identity = _verify_stack(stack, name=state["stackName"], authorization_ref=ref, expected_deadline=current_deadline)
        if identity["runId"] != run_id: raise GateBlocked("stack RunId differs from the requested auth run")
        iid, shape = self._instance(client, identity); self._wait_ssm(client, iid)
        session = ("sudo cloud-init status --wait && test -f /var/lib/explicit-lean-pilot/shutdown-installed && "
                   "test -x /usr/local/bin/codex && /usr/local/bin/codex --version >/dev/null && "
                   "sudo -H /usr/local/bin/codex login --device-auth && "
                   "sudo -H /usr/local/bin/codex login status && "
                   "sudo -H bash -ceu 'cd /var/lib/explicit-lean-pilot/auth-checkout && "
                   "python3 -B Experiment/campaign_budget.py check > /var/lib/explicit-lean-pilot/auth-budget.json && "
                   "/usr/bin/jq -e \".canDispatch == true\" /var/lib/explicit-lean-pilot/auth-budget.json >/dev/null'")
        command = ("aws", "--profile", PROFILE, "--region", REGION, "ssm", "start-session", "--target", iid, "--document-name", "AWS-StartInteractiveCommand", "--parameters", _json({"command": [session]})); completed = (self.session_runner or (lambda value: subprocess.run(list(value), cwd=ROOT, text=True, check=False)))(command)
        if getattr(completed, "returncode", None) != 0:
            state.update({"instanceId": iid, "instanceShape": shape, "phase": "awaiting-codex-auth", "authRetryRequired": True, "authFailure": "Session Manager transport or remote command failed"}); _write_state(path, state)
            raise PilotError("Session Manager device-auth session failed")
        probe_commands = build_auth_probe_commands(repo_url=identity["parameters"]["RepoUrl"], authorization_ref=ref, run_id=run_id, not_after=current_deadline)
        state.update({"instanceId": iid, "instanceShape": shape, "authSessionCompletedAt": _utc(self.now()), "remoteAuthStrategy": REMOTE_AUTH_STRATEGY, "authRetryRequired": True, "phase": "auth-probe", "authProbe": {"kind": "auth-postcheck", "runId": run_id, "instanceId": iid, "status": "dispatching"}}); _write_state(path, state)
        mutating = AwsClient(runner=self.runner, allow_mutations=True)
        try:
            probe_id = self._send_auth_probe(mutating, iid, probe_commands, run_id)
            state.update({"authProbeCommandId": probe_id, "authProbe": {"kind": "auth-postcheck", "runId": run_id, "instanceId": iid, "commandId": probe_id, "status": "InProgress", "responseCode": None}}); _write_state(path, state)
            invocation = self._wait_command(mutating, probe_id, iid)
        except Exception as error:
            state.update({"phase": "awaiting-codex-auth", "authRetryRequired": True, "authProbe": {**state.get("authProbe", {}), "status": "ambiguous", "error": str(error)[:500]}}); _write_state(path, state)
            raise error if isinstance(error, PilotError) else PilotError(str(error))
        probe_status, response_code = invocation.get("Status"), invocation.get("ResponseCode")
        probe_info = {**state.get("authProbe", {}), "status": probe_status, "responseCode": response_code}
        if probe_status != "Success" or type(response_code) is not int or response_code != 0:
            state.update({"phase": "awaiting-codex-auth", "authRetryRequired": True, "authProbe": probe_info, "authProbeFailure": "post-check did not return Success with ResponseCode 0"}); _write_state(path, state)
            raise GateBlocked(f"SSM auth post-check failed: status={probe_status!r}, responseCode={response_code!r}")
        checked_at = _utc(self.now()); proof_path = path.with_name(f"{run_id}.remote-auth-proof.json")
        proof = {"schema": 1, "strategy": REMOTE_AUTH_STRATEGY, "checkedAt": checked_at, "instanceId": iid, "runId": run_id, "codexLoginStatus": "logged_in", "campaignBudget": {"canDispatch": True, "decision": "continue"}}
        _write_state(proof_path, proof)
        state.update({"instanceId": iid, "instanceShape": shape, "authSessionCompletedAt": checked_at, "remoteAuthStrategy": REMOTE_AUTH_STRATEGY, "remoteAuthProofPath": str(proof_path), "authRetryRequired": False, "phase": "awaiting-codex-auth-proof", "authProbe": probe_info}); _write_state(path, state)
        return {"schema": 2, "kind": "aws_linux_pilot_auth", "readOnly": False, "runId": run_id, "instanceId": iid, "phase": state["phase"], "authProbeCommandId": probe_id, "authProbeStatus": probe_info, "remoteAuthProof": str(proof_path), "proof": proof}

    def start_worker(self, *, run_id: str, remote_auth_proof: Path | str | None = None, confirm_start_worker: bool = False, dry_run: bool = False) -> dict[str, Any]:
        if not confirm_start_worker and not dry_run: raise PilotError("worker dispatch requires --confirm-start-worker")
        validate_run_id(run_id); path = _state_path(run_id, self.state_root)
        if not path.exists(): raise GateBlocked("start-worker requires an existing launched run state")
        state = _read_state(path); ref = state.get("authorizationRef")
        if type(ref) is not str or state.get("runId") != run_id or state.get("stackName") != stack_name(ref): raise GateBlocked("run state does not match deterministic stack")
        if state.get("phase") in {"dispatching-worker", "dispatch-ambiguous", "worker-started-failed"}: raise GateBlocked("worker dispatch outcome is ambiguous; inspect status and do not retry")
        policy, raw, now = self._policy_time(); deadline = _dt(state.get("notAfter"), "run notAfter")
        if deadline != parse_not_after(policy, now): raise GateBlocked("run deadline differs from the authorized deadline")
        client = AwsClient(runner=self.runner); _identity(client); stack = _describe_stack(client, state["stackName"])
        if stack is None: raise GateBlocked("launched stack is absent")
        identity = _verify_stack(stack, name=state["stackName"], authorization_ref=ref, expected_deadline=deadline)
        if identity["runId"] != run_id or identity["status"] != "CREATE_COMPLETE": raise GateBlocked("launched stack is not the complete requested run")
        iid, shape = self._instance(client, identity)
        if state.get("instanceId") not in {None, iid}: raise GateBlocked("run state instance differs from the stack")
        if state.get("workerCommandId") and state.get("phase") in {"worker-started", "worker-dispatched"}: return {"schema": 2, "kind": "aws_linux_pilot_start_worker", "readOnly": True, "idempotent": True, "runId": run_id, "workerCommandId": state["workerCommandId"], "state": state, "statePath": str(path)}
        if state.get("phase") not in {"awaiting-codex-auth", "awaiting-codex-auth-proof"}: raise GateBlocked(f"start-worker is not available in run phase {state.get('phase')!r}")
        if state.get("authRetryRequired") is True: raise GateBlocked("auth post-check failed; rerun auth before worker dispatch")
        remote = validate_remote_auth_proof(remote_auth_proof, instance_id=iid, now=now, run_id=run_id); authorization = validate_authorization(policy, self.repo_root, ref, git_runner=self.git_runner); checks, gate_client = self._aws_gates(policy, now); active = _active_hosts(gate_client)
        if len(active) != 1 or active[0].get("InstanceId") != iid: raise GateBlocked("requested run is not the only active pilot host")
        repo_url = validate_repo_url(state.get("repoUrl", identity["parameters"]["RepoUrl"])); commands = build_worker_commands(repo_url=repo_url, authorization_ref=ref, run_id=run_id, not_after=deadline, input_root=f".lake/search-free-mathlib/aws-linux-pilot/{run_id}", output_root=f".lake/boundary-materialization/aws-linux-pilot/{run_id}", worker_id=f"aws-linux-pilot-{run_id}"); checks.update({"authorization": {"ok": True, **authorization}, "remoteAuth": {"ok": True, **remote}, "campaignBudget": dict((self.budget_check or _budget)()), "template": {"ok": True, **validate_template_invariants()}})
        if checks["campaignBudget"].get("canDispatch") is not True: raise GateBlocked("campaign budget gate denied dispatch")
        if dry_run: return {"schema": 2, "kind": "aws_linux_pilot_start_worker", "readOnly": True, "dryRun": True, "runId": run_id, "instanceId": iid, "checks": checks, "awsCalls": len(client.calls) + len(gate_client.calls)}
        if parse_not_after(policy, self.now()) != deadline: raise GateBlocked("run deadline changed before worker dispatch")
        state.update({"instanceId": iid, "instanceShape": shape, "remoteAuth": remote, "phase": "dispatching-worker", "dispatchAttempted": True}); _write_state(path, state); mutating = AwsClient(runner=self.runner, allow_mutations=True)
        try:
            command_id = self._send(mutating, iid, commands, run_id, not_after=deadline); state.update({"workerCommandId": command_id, "phase": "worker-started", "workerDispatchedAt": _utc(self.now())}); _write_state(path, state); return {"schema": 2, "kind": "aws_linux_pilot_start_worker", "readOnly": False, "runId": run_id, "instanceId": iid, "workerCommandId": command_id, "phase": "worker-started", "checks": checks, "statePath": str(path)}
        except Exception as error:
            state.update({"phase": "dispatch-ambiguous", "manualAttention": True, "error": str(error)[:500], "stackCleanup": {"attempted": False, "retained": True, "reason": "SSM dispatch was attempted; retain Scheduler TTL and evidence"}}); _write_state(path, state); raise error if isinstance(error, PilotError) else PilotError(str(error))


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument("--policy", type=Path, default=POLICY_PATH, help=argparse.SUPPRESS); parser.add_argument("--repo-root", type=Path, default=ROOT, help=argparse.SUPPRESS); parser.add_argument("--state-root", type=Path, default=STATE_ROOT, help=argparse.SUPPRESS); sub = parser.add_subparsers(dest="command"); sub.add_parser("plan", help="read-only launch plan"); status = sub.add_parser("status", help="read-only run status"); status.add_argument("--run-id"); launch = sub.add_parser("launch", help="create the bounded stack"); launch.add_argument("--repo-url", required=True); launch.add_argument("--authorization-ref", required=True); launch.add_argument("--run-id"); launch.add_argument("--confirm-launch", action="store_true"); launch.add_argument("--dry-run", action="store_true"); auth = sub.add_parser("auth", help="open the device-auth session"); auth.add_argument("--run-id", required=True); auth.add_argument("--confirm-auth", action="store_true"); worker = sub.add_parser("start-worker", help="dispatch the one worker"); worker.add_argument("--run-id", required=True); worker.add_argument("--remote-auth-proof", type=Path, required=True); worker.add_argument("--confirm-start-worker", action="store_true"); worker.add_argument("--dry-run", action="store_true"); return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv); controller = PilotController(policy_path=args.policy, repo_root=args.repo_root, state_root=args.state_root)
    try:
        command = args.command or "plan"
        if command == "plan": result = controller.plan()
        elif command == "status": result = controller.status(args.run_id)
        elif command == "launch": result = controller.launch(repo_url=args.repo_url, authorization_ref=args.authorization_ref, run_id=args.run_id, confirm_launch=args.confirm_launch, dry_run=args.dry_run)
        elif command == "auth": result = controller.auth(run_id=args.run_id, confirm_auth=args.confirm_auth)
        elif command == "start-worker": result = controller.start_worker(run_id=args.run_id, remote_auth_proof=args.remote_auth_proof, confirm_start_worker=args.confirm_start_worker, dry_run=args.dry_run)
        else: raise PilotError(f"unknown command {command}")
        print(json.dumps(result, indent=2, sort_keys=True)); return 0 if result.get("ready", True) and "error" not in result else 3
    except (PilotError, OSError, ValueError, TypeError) as error:
        print(json.dumps({"ok": False, "error": str(error)[:500]}, indent=2, sort_keys=True), file=sys.stderr); return 3


if __name__ == "__main__": raise SystemExit(main())
