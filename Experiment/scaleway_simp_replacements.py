#!/usr/bin/env python3
"""Fail-closed controller for one explicitly bounded Scaleway worker.

The default policy is planning-only.  No paid resource can be created until a
coordinator fills every authorization field, publishes the exact clean source
commit, and the operator passes ``--confirm-create``.  The command runner is
injectable so the lifecycle can be exercised without contacting Scaleway.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timedelta, timezone
import fcntl
import hashlib
import ipaddress
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
from typing import Any, Callable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = ROOT / "tracking/tasks/T64-scaleway-runner/pilot-policy.json"
CANONICAL_REPO = "https://github.com/Barraketh/explicit-lean.git"
EXPECTED_TYPE = "GP1-L"
HARD_MAX_LIFETIME_SECONDS = 12 * 60 * 60
HARD_MAX_WORKER_SECONDS = 10 * 60 * 60
NAME_PREFIX = "explicit-lean-simp-"
ELAN_URL = "https://github.com/leanprover/elan/releases/download/v4.2.3/elan-x86_64-unknown-linux-gnu.tar.gz"
ELAN_SHA256 = "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2"
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
ID_RE = re.compile(r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$")
SHA_RE = re.compile(r"^[0-9a-f]{64}$")
MODULE_RE = re.compile(r"^[A-Za-z0-9_.]+$")


class PilotError(RuntimeError):
    """Input, provider, or safety gate failure."""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _dict(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise PilotError(f"{label} must be an object")
    return value


def _read_json(path: Path, label: str) -> dict[str, Any]:
    try:
        return _dict(json.loads(path.read_text(encoding="utf-8")), label)
    except (OSError, json.JSONDecodeError) as error:
        raise PilotError(f"cannot read {label}: {path}") from error


def parse_utc(value: object, label: str) -> datetime:
    if type(value) is not str:
        raise PilotError(f"{label} must be an ISO-8601 timestamp")
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as error:
        raise PilotError(f"{label} is not a valid ISO-8601 timestamp") from error
    if parsed.tzinfo is None or parsed.utcoffset() is None or parsed.microsecond:
        raise PilotError(f"{label} must include timezone and whole-second precision")
    return parsed.astimezone(timezone.utc)


def validate_policy(policy: Mapping[str, Any], now: datetime) -> dict[str, Any]:
    if now.tzinfo is None or now.utcoffset() is None:
        raise PilotError("controller clock must be timezone-aware")
    if type(policy.get("schema")) is not int or policy["schema"] != 1:
        raise PilotError("policy schema must be 1")
    if policy.get("provider") != "scaleway" or policy.get("launch_authorized") is not True:
        raise PilotError("policy is planning-only; launch_authorized must be explicitly true")
    if policy.get("login_user") != "ubuntu":
        raise PilotError("the pinned Ubuntu image requires login_user=ubuntu")
    auth = _dict(policy.get("authorization"), "authorization")
    for key in ("organization_id", "project_id", "zone", "not_after", "max_cost_eur", "estimated_all_in_cost_eur", "cost_checked_at", "cost_source"):
        value = auth.get(key)
        if type(value) is not str or not value.strip():
            raise PilotError(f"authorization.{key} must be explicitly set")
    if not ID_RE.fullmatch(auth["organization_id"]) or not ID_RE.fullmatch(auth["project_id"]):
        raise PilotError("organization_id and project_id must be UUIDs")
    zone = auth["zone"]
    if zone not in {f"{region}-{n}" for region in ("fr-par", "nl-ams", "pl-waw") for n in ("1", "2", "3")} | {"it-mil-1"}:
        raise PilotError("authorization.zone is not a recognized Scaleway zone")
    not_after = parse_utc(auth["not_after"], "authorization.not_after")
    if not_after <= now:
        raise PilotError("authorization deadline has expired")
    lifetime = auth.get("max_instance_lifetime_seconds")
    runtime = auth.get("max_worker_runtime_seconds")
    if type(lifetime) is not int or not 1 <= lifetime <= HARD_MAX_LIFETIME_SECONDS:
        raise PilotError("max_instance_lifetime_seconds must be in (0, 12 hours]")
    if type(runtime) is not int or not 1 <= runtime <= HARD_MAX_WORKER_SECONDS or runtime > lifetime:
        raise PilotError("max_worker_runtime_seconds must be in (0, 10 hours] and no longer than host TTL")
    if not_after > now.replace(microsecond=0) and (not_after - now.astimezone(timezone.utc)).total_seconds() > lifetime:
        raise PilotError("authorization deadline exceeds the configured host lifetime")
    try:
        cap = float(auth["max_cost_eur"])
    except ValueError as error:
        raise PilotError("max_cost_eur must be a positive finite number") from error
    if not (0 < cap < float("inf")):
        raise PilotError("max_cost_eur must be a positive finite number")
    try:
        estimated = float(auth["estimated_all_in_cost_eur"])
    except ValueError as error:
        raise PilotError("estimated_all_in_cost_eur must be a positive finite number") from error
    if not (0 < estimated <= cap):
        raise PilotError("current all-in estimate must be positive and within the authorized EUR cap")
    components = _dict(auth.get("cost_components_eur"), "authorization.cost_components_eur")
    component_values: list[float] = []
    for key in ("compute", "public_ipv4", "storage", "egress_and_other"):
        if type(components.get(key)) is not str:
            raise PilotError(f"cost component {key} must be a finite non-negative EUR amount string")
        try:
            value = float(components.get(key))
        except (TypeError, ValueError) as error:
            raise PilotError(f"cost component {key} must be a finite non-negative EUR amount") from error
        if not math.isfinite(value) or value < 0:
            raise PilotError(f"cost component {key} must be a finite non-negative EUR amount")
        component_values.append(value)
    if abs(sum(component_values) - estimated) > 0.01:
        raise PilotError("itemized cost components do not reconcile to the all-in estimate")
    cost_checked = parse_utc(auth["cost_checked_at"], "authorization.cost_checked_at")
    cost_age = (now.astimezone(timezone.utc) - cost_checked).total_seconds()
    if cost_age < 0 or cost_age > 24 * 60 * 60:
        raise PilotError("all-in cost estimate is missing, future-dated, or older than 24 hours")
    requirements = _dict(policy.get("requirements"), "requirements")
    for key, expected in {"single_host": True, "single_worker": True, "linux_x86_64": True,
                          "minimum_memory_gib": 128, "minimum_local_disk_gib": 200,
                          "root_volume": "local:559GB", "public_ipv4": True}.items():
        if type(requirements.get(key)) is not type(expected) or requirements.get(key) != expected:
            raise PilotError(f"requirements.{key} does not match the one-host GP1-L envelope")
    machine = _dict(policy.get("machine"), "machine")
    profile = policy.get("cli_profile")
    if type(profile) is not str or not profile.strip() or profile in {"default", "explicit-lean-cloud"}:
        raise PilotError("cli_profile must name the dedicated Scaleway pilot profile")
    if machine.get("type") != EXPECTED_TYPE:
        raise PilotError(f"machine.type must be exactly {EXPECTED_TYPE}")
    for key in ("image_id", "security_group_id", "ssh_key_id", "ssh_identity_file", "ssh_source_cidr"):
        if type(machine.get(key)) is not str or not machine[key].strip():
            raise PilotError(f"machine.{key} must be explicitly set")
    if not ID_RE.fullmatch(machine["image_id"]) or not ID_RE.fullmatch(machine["security_group_id"]) or not ID_RE.fullmatch(machine["ssh_key_id"]):
        raise PilotError("image_id, security_group_id and ssh_key_id must be UUIDs")
    try:
        network = ipaddress.ip_network(machine["ssh_source_cidr"], strict=True)
    except ValueError as error:
        raise PilotError("ssh_source_cidr must be an explicit network CIDR") from error
    if network.prefixlen == 0:
        raise PilotError("SSH ingress from the entire Internet is forbidden")
    repo = _dict(policy.get("repository"), "repository")
    if repo.get("url") != CANONICAL_REPO or type(repo.get("commit")) is not str or not COMMIT_RE.fullmatch(repo["commit"]):
        raise PilotError("repository must specify the canonical URL and a full 40-hex commit")
    job = _dict(policy.get("job"), "job")
    for key in ("directory", "manifest_sha256", "database_sha256"):
        if type(job.get(key)) is not str or not job[key].strip():
            raise PilotError(f"job.{key} must be explicitly set")
    if not SHA_RE.fullmatch(job["manifest_sha256"]) or not SHA_RE.fullmatch(job["database_sha256"]):
        raise PilotError("job hashes must be lowercase SHA-256 digests")
    return {"deadline": not_after, "lifetime": lifetime, "runtime": runtime, "cost_cap_eur": cap,
            "organization_id": auth["organization_id"], "project_id": auth["project_id"], "zone": zone,
            "machine": machine, "repository": repo, "job": job, "cli_profile": profile,
            "requirements": requirements, "cost_source": auth["cost_source"],
            "cost_components_eur": components}


def validate_job(job_dir: Path, policy_job: Mapping[str, Any]) -> tuple[Path, Path, list[str]]:
    expected_dir = Path(str(policy_job["directory"])).resolve()
    if job_dir.resolve() != expected_dir:
        raise PilotError("job directory does not match the approved policy")
    manifest, database = job_dir / "modules.txt", job_dir / "mathlib-db.sqlite3"
    if manifest.is_symlink() or database.is_symlink() or not manifest.is_file() or not database.is_file() or not os.access(database, os.W_OK):
        raise PilotError("job must contain modules.txt and a writable mathlib-db.sqlite3")
    manifest_bytes = manifest.read_bytes()
    if sha256(manifest_bytes) != policy_job["manifest_sha256"] or sha256_file(database) != policy_job["database_sha256"]:
        raise PilotError("job manifest or database hash differs from the approved policy")
    try:
        lines = manifest_bytes.decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        raise PilotError("modules.txt is not UTF-8") from error
    modules = [line.strip() for line in lines if line.strip()]
    if not modules or any(not MODULE_RE.fullmatch(name) for name in modules) or len(set(modules)) != len(modules):
        raise PilotError("modules.txt must contain unique Lean module names, one per line")
    return manifest, database, modules


def default_runner(command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(list(command), text=True, capture_output=True, timeout=timeout, check=False)
    except (OSError, subprocess.SubprocessError) as error:
        raise PilotError(f"command could not be executed: {command[0]}") from error


def _payload(result: subprocess.CompletedProcess[str], label: str) -> Any:
    if result.returncode != 0:
        # Provider diagnostics can contain sensitive account details; retain only
        # the operation and exit status in user-facing errors.
        raise PilotError(f"{label} failed (exit {result.returncode})")
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise PilotError(f"{label} returned invalid JSON") from error


class ScalewayPilot:
    def __init__(self, *, policy_path: Path = POLICY_PATH, state_path: Path,
                 runner: Callable[[Sequence[str], int], subprocess.CompletedProcess[str]] = default_runner,
                 now: Callable[[], datetime] = lambda: datetime.now(timezone.utc)) -> None:
        self.policy_path, self.state_path = policy_path, state_path
        self.runner, self.now = runner, now

    def policy(self) -> tuple[dict[str, Any], bytes]:
        raw = self.policy_path.read_bytes()
        return _dict(json.loads(raw), "policy"), raw

    def _run(self, command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
        return self.runner(command, timeout)

    def _scw(self, args: Sequence[str], *, policy: Mapping[str, Any] | None = None,
             timeout: int = 60) -> Any:
        prefix = ["scw", "--output", "json"]
        if policy:
            prefix += ["--profile", str(policy.get("cli_profile", "default"))]
        result = self._run([*prefix, *args], timeout)
        return _payload(result, "Scaleway CLI operation")

    def _save(self, state: Mapping[str, Any]) -> None:
        self.state_path.parent.mkdir(parents=True, exist_ok=True)
        temp = self.state_path.with_suffix(self.state_path.suffix + ".tmp")
        temp.write_text(json.dumps(state, sort_keys=True, indent=2) + "\n", encoding="utf-8")
        os.replace(temp, self.state_path)

    def _load_state(self) -> dict[str, Any]:
        return _read_json(self.state_path, "pilot state")

    def _existing_context(self) -> tuple[dict[str, Any], dict[str, Any]]:
        state = self._load_state()
        policy, raw = self.policy()
        if state.get("policy_sha256") != sha256(raw):
            raise PilotError("policy changed after server creation")
        profile = policy.get("cli_profile")
        if type(profile) is not str or not profile.strip() or profile in {"default", "explicit-lean-cloud"}:
            raise PilotError("existing-resource operation requires the dedicated Scaleway pilot profile")
        auth = _dict(policy.get("authorization"), "authorization")
        for key in ("organization_id", "project_id", "zone"):
            if state.get(key) != auth.get(key):
                raise PilotError(f"saved {key} differs from the original policy")
        return state, policy

    def _identity(self, checked: Mapping[str, Any]) -> dict[str, Any]:
        projects = self._scw(["account", "project", "list", f"organization-id={checked['organization_id']}"], policy=checked)
        items = projects.get("projects", []) if isinstance(projects, dict) else None
        if not isinstance(items, list) or not any(item.get("id") == checked["project_id"] and item.get("organization_id") == checked["organization_id"] for item in items if isinstance(item, dict)):
            raise PilotError("authenticated organization/project identity does not match policy")
        return {"organization_id": checked["organization_id"], "project_id": checked["project_id"], "authenticated": True}

    def _repo_gate(self, checked: Mapping[str, Any], repo_root: Path) -> dict[str, str]:
        def git(args: Sequence[str]) -> str:
            result = self._run(["git", *args], 30)
            if result.returncode:
                raise PilotError(f"git {args[0]} failed (exit {result.returncode})")
            return result.stdout.strip()
        commit = checked["repository"]["commit"]
        if git(["rev-parse", "--verify", "HEAD"]) != commit:
            raise PilotError("checkout HEAD does not equal the approved full commit")
        if git(["status", "--porcelain=v1", "--untracked-files=all"]):
            raise PilotError("published source checkout is dirty")
        refs = git(["ls-remote", CANONICAL_REPO])
        if not any(line.split()[:1] == [commit] for line in refs.splitlines()):
            raise PilotError("approved source commit is not published on canonical origin")
        return {"commit": commit, "repo_root": str(repo_root.resolve()), "published": True, "clean": True}

    def _active_resources(self, checked: Mapping[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        args = ["instance", "server", "list", f"project-id={checked['project_id']}", f"zone={checked['zone']}"]
        data = self._scw(args, policy=checked)
        servers = data.get("servers", []) if isinstance(data, dict) else None
        if not isinstance(servers, list):
            raise PilotError("server listing has unexpected shape")
        tagged = []
        for server in servers:
            if not isinstance(server, dict) or not isinstance(server.get("tags", []), list):
                raise PilotError("server listing entry has unexpected shape")
            if NAME_PREFIX in str(server.get("name", "")) or "explicit-lean-simp-pilot" in server.get("tags", []):
                tagged.append(server)
        volumes = self._scw(["instance", "volume", "list", f"project-id={checked['project_id']}", f"zone={checked['zone']}"], policy=checked)
        items = volumes.get("volumes", []) if isinstance(volumes, dict) else None
        if not isinstance(items, list):
            raise PilotError("volume listing has unexpected shape")
        matching = []
        for volume in items:
            if not isinstance(volume, dict) or not isinstance(volume.get("tags", []), list):
                raise PilotError("volume listing entry has unexpected shape")
            if NAME_PREFIX in str(volume.get("name", "")) or "explicit-lean-simp-pilot" in volume.get("tags", []):
                matching.append(volume)
        if tagged or matching:
            raise PilotError("active duplicate pilot server or attached storage exists")
        return servers, items

    def _check_type_image_network(self, checked: Mapping[str, Any]) -> dict[str, Any]:
        zone = checked["zone"]
        types = self._scw(["instance", "server-type", "list", f"zone={zone}"], policy=checked)
        type_items = types.get("servers", types.get("server_types", [])) if isinstance(types, dict) else None
        if not isinstance(type_items, list):
            raise PilotError("server-type listing has unexpected shape")
        selected = [x for x in type_items if isinstance(x, dict) and x.get("name", x.get("id")) == EXPECTED_TYPE]
        if len(selected) != 1:
            raise PilotError("exact GP1-L server type is unavailable or ambiguous in selected zone")
        ram_bytes = selected[0].get("ram")
        if type(ram_bytes) is not int or ram_bytes < 128 * 1024**3:
            raise PilotError("GP1-L type catalog does not confirm at least 128 GiB RAM")
        image_data = self._scw(["instance", "image", "list", f"zone={zone}", f"project-id={checked['project_id']}"], policy=checked)
        images = image_data.get("images", []) if isinstance(image_data, dict) else None
        image = checked["machine"]["image_id"]
        if not isinstance(images, list) or not any(isinstance(x, dict) and x.get("id") == image and x.get("arch") in ("x86_64", "amd64") and "ubuntu" in str(x.get("name", "")).lower() for x in images):
            raise PilotError("pinned Linux x86_64 image is not available in selected zone/project")
        sg = self._scw(["instance", "security-group", "get", checked["machine"]["security_group_id"], f"zone={zone}"], policy=checked)
        group = sg.get("security_group", sg) if isinstance(sg, dict) else None
        if not isinstance(group, dict) or group.get("project") != checked["project_id"] and group.get("project_id") != checked["project_id"]:
            raise PilotError("security group project identity does not match policy")
        if group.get("inbound_default_policy") != "drop":
            raise PilotError("security group default inbound policy must drop traffic")
        rules = group.get("rules")
        if not isinstance(rules, list):
            raise PilotError("security group rules unavailable")
        cidr = checked["machine"]["ssh_source_cidr"]
        ssh_rules = [r for r in rules if isinstance(r, dict) and r.get("direction") == "inbound"]
        if len(ssh_rules) != 1 or ssh_rules[0].get("protocol") not in ("TCP", "tcp") or ssh_rules[0].get("dest_port_from") != 22 or ssh_rules[0].get("dest_port_to") != 22 or ssh_rules[0].get("ip_range") != cidr:
            raise PilotError("security group must allow only SSH from the approved source CIDR")
        key_data = self._scw(["iam", "ssh-key", "get", checked["machine"]["ssh_key_id"]], policy=checked)
        ssh_key = key_data.get("ssh_key", key_data) if isinstance(key_data, dict) else None
        if not isinstance(ssh_key, dict) or ssh_key.get("project_id") != checked["project_id"]:
            raise PilotError("SSH key project identity does not match policy")
        private_key = Path(checked["machine"]["ssh_identity_file"]).expanduser()
        if not private_key.is_file() or not os.access(private_key, os.R_OK):
            raise PilotError("configured SSH identity file is unavailable")
        if stat.S_IMODE(private_key.stat().st_mode) & 0o077:
            raise PilotError("SSH identity file permissions must exclude group and other access")
        if ssh_key.get("name") is None or not ssh_key.get("public_key"):
            raise PilotError("configured Scaleway SSH key has incomplete identity data")
        public_key = ssh_key.get("public_key")
        if type(public_key) is not str or not re.fullmatch(r"(?:ssh-ed25519|ssh-rsa|ecdsa-sha2-nistp(?:256|384|521)) [A-Za-z0-9+/=]+(?: .*)?", public_key):
            raise PilotError("configured SSH public key has an unsupported or malformed format")
        return {"server_type": selected[0], "image_id": image, "security_group_id": checked["machine"]["security_group_id"],
                "ssh_key_id": checked["machine"]["ssh_key_id"], "ssh_key_name": ssh_key["name"],
                "ssh_public_key": " ".join(public_key.split()[:2])}

    def preflight(self, *, repo_root: Path, job_dir: Path) -> dict[str, Any]:
        policy, raw = self.policy()
        checked = validate_policy(policy, self.now())
        manifest, database, modules = validate_job(job_dir, checked["job"])
        version = self._run(["scw", "version"], 15)
        if version.returncode:
            raise PilotError("Scaleway CLI is unavailable")
        version_lines = version.stdout.strip().splitlines()
        if not version_lines:
            raise PilotError("Scaleway CLI did not report a version")
        identity = self._identity(checked)
        source = self._repo_gate(checked, repo_root)
        self._active_resources(checked)
        shape = self._check_type_image_network(checked)
        return {"read_only": True, "policy_sha256": sha256(raw), "cli_version": version_lines[0],
                "identity": identity, "source": source, "machine": shape,
                "job": {"module_count": len(modules), "manifest_sha256": sha256(manifest.read_bytes()),
                        "database_sha256": sha256_file(database)}, "worker_count": 1,
                "deadline": checked["deadline"].isoformat().replace("+00:00", "Z")}

    def plan(self) -> dict[str, Any]:
        policy, raw = self.policy()
        launch_ok = policy.get("launch_authorized") is True
        blockers = [] if launch_ok else ["coordinator must populate exact project, region, price, TTL, job and source bounds and set launch_authorized=true"]
        if launch_ok:
            try:
                validate_policy(policy, self.now())
            except PilotError as error:
                blockers.append(str(error))
            else:
                blockers.append("read-only preflight is still required before create")
        return {"read_only": True, "provider": "scaleway", "authorized": launch_ok,
                "policy_sha256": sha256(raw), "mutation_count": 0,
                "blockers": blockers}

    def create(self, *, repo_root: Path, job_dir: Path, confirm: bool = False) -> dict[str, Any]:
        lock_path = self.state_path.with_suffix(self.state_path.suffix + ".lock")
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o600)
        try:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise PilotError("another local Scaleway create operation is in progress") from error
            return self._create_locked(repo_root=repo_root, job_dir=job_dir, confirm=confirm)
        finally:
            os.close(descriptor)

    def _create_locked(self, *, repo_root: Path, job_dir: Path, confirm: bool) -> dict[str, Any]:
        if not confirm:
            raise PilotError("creation requires --confirm-create")
        if self.state_path.exists():
            raise PilotError("a pilot state file already exists; this controller instance is single-use")
        preflight = self.preflight(repo_root=repo_root, job_dir=job_dir)
        policy, raw = self.policy()
        checked = validate_policy(policy, self.now())
        name = NAME_PREFIX + sha256(raw)[:12]
        login_user = str(policy.get("login_user", "ubuntu"))
        if not re.fullmatch(r"[a-z_][a-z0-9_-]*", login_user):
            raise PilotError("login_user must be a safe Unix account name")
        create_started = self.now().astimezone(timezone.utc)
        host_deadline = min(checked["deadline"], create_started + timedelta(seconds=checked["lifetime"]))
        calendar_deadline = host_deadline.strftime("%Y-%m-%d %H:%M:%S UTC")
        cloud_config = ("#cloud-config\nssh_authorized_keys:\n  - " + preflight["machine"]["ssh_public_key"] + "\n"
                        "write_files:\n"
                        "  - path: /etc/systemd/system/explicit-lean-simp-pilot-ttl.service\n"
                        "    permissions: '0644'\n"
                        "    content: |\n"
                        "      [Unit]\n      Description=Bounded Explicit Lean pilot shutdown\n"
                        "      [Service]\n      Type=oneshot\n      ExecStart=/usr/bin/systemctl poweroff\n"
                        "  - path: /etc/systemd/system/explicit-lean-simp-pilot-ttl.timer\n"
                        "    permissions: '0644'\n"
                        "    content: |\n"
                        "      [Unit]\n      Description=Bounded Explicit Lean pilot TTL\n"
                        "      [Timer]\n      OnCalendar=" + calendar_deadline + "\n      Persistent=true\n"
                        "      Unit=explicit-lean-simp-pilot-ttl.service\n"
                        "      [Install]\n      WantedBy=timers.target\n"
                        "runcmd:\n  - [systemctl, daemon-reload]\n  - [systemctl, enable, --now, explicit-lean-simp-pilot-ttl.timer]\n")
        cloud_path: Path | None = None
        try:
            with tempfile.NamedTemporaryFile("w", encoding="utf-8", prefix="scw-cloud-init-", suffix=".yaml", delete=False) as handle:
                handle.write(cloud_config); cloud_path = Path(handle.name)
            result = self._scw(["instance", "server", "create", f"name={name}", f"type={EXPECTED_TYPE}",
                                f"image={checked['machine']['image_id']}", "ip=new", f"root-volume={checked['requirements']['root_volume']}",
                                f"security-group-id={checked['machine']['security_group_id']}",
                                f"cloud-init=@{cloud_path}", f"project-id={checked['project_id']}", f"zone={checked['zone']}",
                                "tags.0=explicit-lean-simp-pilot", "tags.1=single-worker", "--wait"], policy=checked, timeout=300)
        finally:
            if cloud_path is not None:
                cloud_path.unlink(missing_ok=True)
        server = result.get("server", result) if isinstance(result, dict) else None
        server_id = server.get("id") if isinstance(server, dict) else None
        if type(server_id) is not str or not ID_RE.fullmatch(server_id):
            raise PilotError("create response lacks a valid server ID; inspect provider before retrying")
        state = {"schema": 1, "phase": "created", "server_id": server_id, "name": name, "zone": checked["zone"],
                 "project_id": checked["project_id"], "organization_id": checked["organization_id"],
                 "created_at": create_started.isoformat(), "deadline": host_deadline.isoformat(),
                 "lifetime_seconds": checked["lifetime"], "worker_runtime_seconds": checked["runtime"],
                 "policy_sha256": preflight["policy_sha256"], "preflight": preflight, "mutation": "server-create"}
        self._save(state)
        observed = self._scw(["instance", "server", "get", server_id, f"zone={checked['zone']}"], policy=checked)
        observed_server = observed.get("server", observed)
        if not isinstance(observed_server, dict):
            raise PilotError("created server details are malformed; state retained for cleanup")
        tags = observed_server.get("tags", [])
        if not isinstance(tags, list):
            raise PilotError("created server tags are missing; state retained for cleanup")
        if (observed_server.get("name") != name or observed_server.get("project_id", observed_server.get("project")) != checked["project_id"]
                or observed_server.get("zone") != checked["zone"]
                or observed_server.get("commercial_type", observed_server.get("type")) != EXPECTED_TYPE
                or "explicit-lean-simp-pilot" not in tags):
            raise PilotError("created server identity/shape did not match policy; state retained for cleanup")
        return state

    def status(self) -> dict[str, Any]:
        state, policy = self._existing_context()
        auth = _dict(policy.get("authorization"), "authorization")
        self._identity({"organization_id": auth["organization_id"], "project_id": auth["project_id"],
                        "cli_profile": policy["cli_profile"]})
        server = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        if not isinstance(server, dict):
            raise PilotError("server status response has unexpected shape")
        return {"read_only": True, "state": state, "provider": server.get("server", server)}

    def _ssh(self, state: Mapping[str, Any], *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
        policy, _ = self.policy(); machine = _dict(policy.get("machine"), "machine")
        server = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        data = server.get("server", server) if isinstance(server, dict) else None
        if not isinstance(data, dict):
            raise PilotError("server address response has unexpected shape")
        public_ip = data.get("public_ip", {}) if isinstance(data, dict) else None
        address = public_ip.get("address") if isinstance(public_ip, dict) else None
        if not isinstance(address, str) or not address:
            raise PilotError("server has no public IPv4 address")
        base = ["ssh", "-i", str(Path(machine["ssh_identity_file"]).expanduser()), "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes", "-o", "ConnectTimeout=20", f"{policy.get('login_user', 'ubuntu')}@{address}"]
        return self._run([*base, *args], timeout)

    def run_worker(self, *, job_dir: Path, repo_root: Path) -> dict[str, Any]:
        state = self._load_state(); policy, raw = self.policy(); checked = validate_policy(policy, self.now())
        if state.get("policy_sha256") != sha256(raw):
            raise PilotError("policy changed after server creation")
        manifest, database, _ = validate_job(job_dir, checked["job"])
        created = datetime.fromisoformat(state["created_at"])
        age = (self.now().astimezone(timezone.utc) - created.astimezone(timezone.utc)).total_seconds()
        if age >= checked["lifetime"] or self.now().astimezone(timezone.utc) >= checked["deadline"]:
            raise PilotError("host TTL or authorization deadline reached")
        if state.get("phase") != "created":
            raise PilotError("worker may be dispatched once per server")
        self._repo_gate(checked, repo_root)
        self._identity(checked)
        self._check_type_image_network(checked)
        observed = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=checked)
        observed_server = observed.get("server", observed)
        if not isinstance(observed_server, dict):
            raise PilotError("existing server details are malformed")
        observed_tags = observed_server.get("tags", [])
        if not isinstance(observed_tags, list) or observed_server.get("name") != state.get("name") or observed_server.get("project_id", observed_server.get("project")) != checked["project_id"] or observed_server.get("zone") != checked["zone"] or observed_server.get("commercial_type", observed_server.get("type")) != EXPECTED_TYPE or "explicit-lean-simp-pilot" not in observed_tags:
            raise PilotError("existing server identity/shape mismatch; refusing worker dispatch")
        ttl_remaining = int(checked["lifetime"] - age)
        cutoff_remaining = int((checked["deadline"] - self.now().astimezone(timezone.utc)).total_seconds())
        if ttl_remaining <= 0 or cutoff_remaining <= 0:
            raise PilotError("no host lifetime remains before TTL/deadline")
        watchdog = self._ssh(state, "sudo", "systemd-run", f"--unit=explicit-lean-simp-ttl-{state['server_id']}",
                             f"--on-active={ttl_remaining}s", "/usr/bin/systemctl", "poweroff", timeout=60)
        if watchdog.returncode:
            raise PilotError("guest TTL watchdog could not be armed")
        state.update({"guest_poweroff_watchdog_armed": True, "host_ttl_remaining_seconds": ttl_remaining})
        self._save(state)
        # Verify remote image architecture/OS via cloud-init's standard fields
        # and clone only the exact already-published commit.
        commit = checked["repository"]["commit"]
        bootstrap = "set -eu; test \"$(uname -m)\" = x86_64; test -f /etc/os-release; " \
                    "sudo apt-get update; sudo DEBIAN_FRONTEND=noninteractive apt-get install -y git python3 python3-pip build-essential curl; " \
                    "git ls-remote https://github.com/Barraketh/explicit-lean.git | awk '{print $1}' | grep -Fx " + shlex.quote(commit) + "; " \
                    "git clone --no-checkout https://github.com/Barraketh/explicit-lean.git /opt/explicit-lean; " \
                    "git -C /opt/explicit-lean checkout --detach " + shlex.quote(commit) + "; " \
                    "test \"$(git -C /opt/explicit-lean rev-parse HEAD)\" = " + shlex.quote(commit) + "; " \
                    "curl --fail --silent --show-error " + ELAN_URL + " -o /tmp/elan.tar.gz; " \
                    "echo " + ELAN_SHA256 + "'  /tmp/elan.tar.gz' | sha256sum -c -; " \
                    "tar -xzf /tmp/elan.tar.gz -C /tmp elan-init; /tmp/elan-init -y --default-toolchain none; " \
                    ". \"$HOME/.elan/env\"; cd /opt/explicit-lean; lake exe cache get"
        state.update({"phase": "bootstrap-started", "bootstrap_started_at": self.now().isoformat()})
        self._save(state)
        boot = self._ssh(state, "sh", "-lc", shlex.quote(bootstrap), timeout=min(1800, checked["runtime"]))
        if boot.returncode:
            raise PilotError(f"remote pinned checkout/dependency bootstrap failed (exit {boot.returncode})")
        login_user = str(policy.get("login_user", "ubuntu"))
        if not re.fullmatch(r"[a-z_][a-z0-9_-]*", login_user):
            raise PilotError("login_user must be a safe Unix account name")
        remote = f"/home/{login_user}/explicit-lean-simp-job"
        mkdir = self._ssh(state, "mkdir", "-p", remote, timeout=60)
        if mkdir.returncode:
            raise PilotError("remote job directory creation failed")
        machine = checked["machine"]
        server_data = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        server_obj = server_data.get("server", server_data)
        address = server_obj["public_ip"]["address"]
        target = f"{policy.get('login_user', 'ubuntu')}@{address}:{remote}/"
        scp_base = ["scp", "-i", str(Path(machine["ssh_identity_file"]).expanduser()), "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes"]
        copied = self._run([*scp_base, str(manifest), str(database), target], min(300, checked["runtime"]))
        if copied.returncode:
            raise PilotError("job transfer failed")
        remote_worker = ("set -eu; cd /opt/explicit-lean; . \"$HOME/.elan/env\"; "
                         "mkdir -p /var/tmp/explicit-lean-simp-job/artifacts; "
                         "set +e; timeout --signal=TERM --kill-after=30 " + str(checked["runtime"]) +
                         " python3 -B Experiment/simp_replacement_worker.py --database " + remote + "/mathlib-db.sqlite3 --manifest " + remote + "/modules.txt --artifacts " + remote + "/artifacts > " + remote + "/worker.log 2>&1; rc=$?; set -e; "
                         "dbhash=$(sha256sum " + remote + "/mathlib-db.sqlite3 | awk '{print $1}'); "
                         "manifesthash=$(sha256sum " + remote + "/modules.txt | awk '{print $1}'); "
                         "printf '{\"schema\":1,\"exit_code\":%s,\"commit\":\"%s\",\"database_sha256\":\"%s\",\"manifest_sha256\":\"%s\"}\\n' \"$rc\" " + shlex.quote(commit) + " \"$dbhash\" \"$manifesthash\" > " + remote + "/complete.json; "
                         "tar -czf " + remote + "/result.tar.gz -C " + remote + " mathlib-db.sqlite3 worker.log complete.json artifacts; exit \"$rc\"")
        started = self.now().astimezone(timezone.utc)
        cutoff_remaining = int((checked["deadline"] - started).total_seconds())
        worker_timeout = min(checked["runtime"], ttl_remaining, cutoff_remaining)
        if worker_timeout <= 0:
            raise PilotError("no worker runtime remains before host TTL/deadline")
        state.update({"phase": "worker-started", "worker_started_at": started.isoformat(), "worker_timeout_seconds": worker_timeout,
                      "host_ttl_remaining_seconds": ttl_remaining})
        self._save(state)
        # Override the wrapper's timeout with the smaller remaining policy time.
        remote_worker = remote_worker.replace(str(checked["runtime"]), str(worker_timeout), 1)
        ran = self._ssh(state, "sh", "-lc", shlex.quote(remote_worker), timeout=worker_timeout + 120)
        state.update({"worker_exit_code": ran.returncode, "phase": "worker-finished" if ran.returncode == 0 else "worker-failed"})
        self._save(state)
        return state

    def collect(self, *, output_dir: Path) -> dict[str, Any]:
        state, policy = self._existing_context()
        if state.get("phase") not in {"worker-finished", "worker-failed"} or type(state.get("worker_exit_code")) is not int:
            raise PilotError("collection requires a terminal worker state")
        output_dir.mkdir(parents=True, exist_ok=True)
        if any(output_dir.iterdir()):
            raise PilotError("artifact output directory must be empty")
        remote = "/var/tmp/explicit-lean-simp-job/result.tar.gz"
        auth = _dict(policy.get("authorization"), "authorization")
        self._identity({"organization_id": auth["organization_id"], "project_id": auth["project_id"],
                        "cli_profile": policy["cli_profile"]})
        server_data = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        server_obj = server_data.get("server", server_data) if isinstance(server_data, dict) else None
        if not isinstance(server_obj, dict) or not isinstance(server_obj.get("public_ip"), dict) or type(server_obj["public_ip"].get("address")) is not str:
            raise PilotError("result server address response has unexpected shape")
        address = server_obj["public_ip"]["address"]
        server_tags = server_obj.get("tags", [])
        if not isinstance(server_tags, list) or server_obj.get("name") != state.get("name") or server_obj.get("project_id", server_obj.get("project")) != state.get("project_id") or "explicit-lean-simp-pilot" not in server_tags:
            raise PilotError("result server identity mismatch")
        target = f"{policy.get('login_user', 'ubuntu')}@{address}:{remote}"
        local_tar = output_dir / "result.tar.gz"
        machine = _dict(policy.get("machine"), "machine")
        proc = self._run(["scp", "-i", str(Path(machine["ssh_identity_file"]).expanduser()), "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes", target, str(local_tar)], 300)
        if proc.returncode:
            raise PilotError("artifact collection failed")
        import tarfile
        extracted: list[Path] = []
        with tarfile.open(local_tar, "r:gz") as archive:
            members = archive.getmembers()
            names = {member.name for member in members}
            expected = {"mathlib-db.sqlite3", "worker.log", "complete.json"}
            allowed = lambda member: (member.name in expected or member.name == "artifacts" and member.isdir()
                                      or member.name.startswith("artifacts/"))
            if len(names) != len(members) or not expected.issubset(names) or any(Path(member.name).is_absolute() or ".." in Path(member.name).parts or not allowed(member) for member in members):
                raise PilotError("artifact archive has missing or unsafe entries")
            for member in members:
                relative = Path(member.name)
                if member.isdir():
                    (output_dir / relative).mkdir(parents=True, exist_ok=True)
                    continue
                if not member.isfile():
                    raise PilotError("artifact archive contains a non-regular file")
                target = output_dir / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                source = archive.extractfile(member)
                if source is None:
                    raise PilotError("artifact archive entry could not be read")
                with source, target.open("wb") as destination:
                    shutil.copyfileobj(source, destination)
                extracted.append(target)
        marker = _read_json(output_dir / "complete.json", "completion marker")
        job = _dict(policy.get("job"), "job")
        repository = _dict(policy.get("repository"), "repository")
        manifest, database, _ = validate_job(Path(job["directory"]), job)
        if (type(marker.get("schema")) is not int or marker.get("schema") != 1
                or type(marker.get("exit_code")) is not int or marker.get("exit_code") != state.get("worker_exit_code")
                or marker.get("commit") != repository.get("commit")):
            raise PilotError("completion marker identity or worker exit is invalid")
        result_db = output_dir / "mathlib-db.sqlite3"
        if not result_db.is_file() or sha256_file(result_db) != marker.get("database_sha256") or marker.get("manifest_sha256") != sha256(manifest.read_bytes()):
            raise PilotError("completion marker checksum mismatch")
        file_hashes = {str(path.relative_to(output_dir)): sha256_file(path) for path in extracted if path.is_file()}
        state.update({"phase": "collected" if state["worker_exit_code"] == 0 else "collected-worker-failed",
                      "collected_at": self.now().isoformat(), "artifact_sha256": sha256_file(local_tar),
                      "database_sha256": sha256_file(result_db), "artifact_file_hashes": file_hashes,
                      "output_dir": str(output_dir.resolve())})
        self._save(state)
        return state

    def cleanup(self, *, confirm: bool = False) -> dict[str, Any]:
        if not confirm:
            raise PilotError("deletion requires --confirm-delete")
        state = self._load_state()
        policy, _ = self.policy()
        profile = policy.get("cli_profile")
        if type(profile) is not str or not profile.strip() or profile in {"default", "explicit-lean-cloud"}:
            raise PilotError("cleanup requires the dedicated Scaleway pilot profile")
        auth = _dict(policy.get("authorization"), "authorization")
        project_id, zone = auth["project_id"], auth["zone"]
        if (state.get("organization_id") != auth.get("organization_id") or state.get("project_id") != project_id
                or state.get("zone") != zone or not ID_RE.fullmatch(str(state.get("server_id", "")))
                or not str(state.get("name", "")).startswith(NAME_PREFIX)):
            raise PilotError("saved pilot resource identity does not match cleanup policy")
        self._identity({"organization_id": auth["organization_id"], "project_id": project_id,
                        "cli_profile": policy["cli_profile"]})
        current = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        server = current.get("server", current) if isinstance(current, dict) else None
        if not isinstance(server, dict):
            raise PilotError("server details unavailable; refusing deletion")
        if server.get("project") != project_id and server.get("project_id") != project_id:
            raise PilotError("server project identity mismatch; refusing deletion")
        server_tags = server.get("tags", [])
        if not isinstance(server_tags, list) or (server.get("name") != state["name"] or server.get("zone") != zone
                or server.get("commercial_type", server.get("type")) != EXPECTED_TYPE
                or "explicit-lean-simp-pilot" not in server_tags):
            raise PilotError("server ownership tags mismatch; refusing deletion")
        attached: set[str] = set(state.get("attached_volume_ids", []))
        volumes_before = self._scw(["instance", "volume", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
        before_items = volumes_before.get("volumes", []) if isinstance(volumes_before, dict) else None
        if not isinstance(before_items, list):
            raise PilotError("pre-delete volume listing has unexpected shape")
        for volume in before_items:
            if not isinstance(volume, dict):
                continue
            server_ref = volume.get("server_id", volume.get("server"))
            if isinstance(server_ref, dict):
                server_ref = server_ref.get("id")
            if server_ref == state["server_id"] and type(volume.get("id")) is str:
                attached.add(volume["id"])
        state["attached_volume_ids"] = sorted(attached)
        self._save(state)
        result = self._scw(["instance", "server", "delete", state["server_id"], "with-volumes=all", "with-ip", f"zone={state['zone']}", "--wait"], policy=policy, timeout=300)
        # Confirm the exact server and all tagged storage are gone. Any CLI
        # failure here leaves the state nonterminal so cleanup can be retried.
        listing = self._scw(["instance", "server", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
        servers = listing.get("servers", []) if isinstance(listing, dict) else None
        if not isinstance(servers, list) or any(isinstance(s, dict) and s.get("id") == state["server_id"] for s in servers):
            raise PilotError("server deletion could not be confirmed")
        volumes = self._scw(["instance", "volume", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
        items = volumes.get("volumes", []) if isinstance(volumes, dict) else None
        remaining_ids = {v.get("id") for v in items if isinstance(v, dict)} if isinstance(items, list) else set()
        if not isinstance(items, list) or any(isinstance(v, dict) and "explicit-lean-simp-pilot" in v.get("tags", []) for v in items) or attached.intersection(remaining_ids):
            raise PilotError("attached storage deletion could not be confirmed")
        state.update({"phase": "deleted", "deleted_at": self.now().isoformat(), "delete_response": result})
        self._save(state)
        return state


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, default=POLICY_PATH)
    parser.add_argument("--state", type=Path, default=ROOT / ".lake/scaleway-simp-pilot/state.json")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("plan", help="show policy readiness without provider calls")
    pf = sub.add_parser("preflight", help="run read-only identity/source/image/network/storage gates")
    pf.add_argument("--repo", type=Path, required=True); pf.add_argument("--job", type=Path, required=True)
    launch = sub.add_parser("create", help="create the single authorized server")
    launch.add_argument("--repo", type=Path, required=True); launch.add_argument("--job", type=Path, required=True)
    launch.add_argument("--confirm-create", action="store_true")
    sub.add_parser("status", help="read provider status only")
    run = sub.add_parser("run-worker", help="bootstrap exact checkout, transfer job and run worker once")
    run.add_argument("--repo", type=Path, required=True); run.add_argument("--job", type=Path, required=True)
    collect = sub.add_parser("collect", help="download and verify worker results")
    collect.add_argument("--output", type=Path, required=True)
    cleanup = sub.add_parser("cleanup", help="delete exact pilot server, attached volume and IP")
    cleanup.add_argument("--confirm-delete", action="store_true")
    args = parser.parse_args(argv)
    ctl = ScalewayPilot(policy_path=args.policy, state_path=args.state)
    try:
        if args.command == "plan": result = ctl.plan()
        elif args.command == "preflight": result = ctl.preflight(repo_root=args.repo, job_dir=args.job)
        elif args.command == "create": result = ctl.create(repo_root=args.repo, job_dir=args.job, confirm=args.confirm_create)
        elif args.command == "status": result = ctl.status()
        elif args.command == "run-worker": result = ctl.run_worker(job_dir=args.job, repo_root=args.repo)
        elif args.command == "collect": result = ctl.collect(output_dir=args.output)
        else: result = ctl.cleanup(confirm=args.confirm_delete)
        print(json.dumps(result, sort_keys=True, indent=2, default=str))
        return 0
    except (PilotError, OSError, ValueError, KeyError) as error:
        print(f"scaleway pilot blocked: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
