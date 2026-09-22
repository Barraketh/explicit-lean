#!/usr/bin/env python3
"""Fail-closed controller for two bounded workers on one Scaleway host.

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
import sqlite3
import stat
import subprocess
import sys
import tempfile
import time
import uuid
from typing import Any, Callable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = ROOT / "tracking/tasks/T64-scaleway-runner/pilot-policy.json"
CANONICAL_REPO = "https://github.com/Barraketh/explicit-lean.git"
DEFAULT_MACHINE_TYPE = "GP1-L"
HARD_MAX_LIFETIME_SECONDS = 12 * 60 * 60
HARD_MAX_WORKER_SECONDS = 10 * 60 * 60
HARD_MAX_COST_USD = 20.0
MAX_RESULT_ARCHIVE_BYTES = 8 * 1024**3
MAX_TOTAL_ARCHIVE_BYTES = 16 * 1024**3
MAX_TAR_MEMBERS = 100_000
MAX_TAR_MEMBER_BYTES = 8 * 1024**3
MAX_TOTAL_EXTRACTED_BYTES = 32 * 1024**3
COLLECTION_DISK_RESERVE_BYTES = 4 * 1024**3
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


def _parse_root_volume(value: object) -> dict[str, Any]:
    """Parse only the local and SBS root-volume forms explicitly supported."""
    if type(value) is not str:
        raise PilotError("requirements.root_volume must be a supported volume string")
    local = re.fullmatch(r"local:([1-9][0-9]*)GB", value)
    if local:
        return {"kind": "local", "size_gib": int(local.group(1)), "iops": None,
                "provider_types": {"l_ssd", "local", "local_ssd"}}
    sbs = re.fullmatch(r"sbs:([1-9][0-9]*)GB:([1-9][0-9]*)", value)
    if sbs:
        iops = int(sbs.group(2))
        sbs_type = {5000: "sbs_5k", 15000: "sbs_15k"}.get(iops)
        if sbs_type is None:
            raise PilotError("SBS root volume IOPS must be 5000 or 15000")
        return {"kind": "sbs", "size_gib": int(sbs.group(1)), "iops": iops,
                "provider_types": {"sbs_volume", sbs_type}, "block_types": {sbs_type}}
    raise PilotError("requirements.root_volume must be local:<size>GB or sbs:<size>GB:<iops>")


def _list_response(value: object, key: str, label: str) -> list[Any]:
    """Accept Scaleway CLI's actual top-level arrays or a named wrapper."""
    if isinstance(value, list):
        return value
    if isinstance(value, dict) and isinstance(value.get(key), list):
        return value[key]
    raise PilotError(f"{label} response has unexpected shape")


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
    for key in ("organization_id", "project_id", "zone", "not_after", "max_cost_eur", "estimated_all_in_cost_eur",
                "cost_checked_at", "cost_source", "max_cost_usd", "eur_usd_rate", "fx_checked_at", "fx_source"):
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
        cap_usd = float(auth["max_cost_usd"])
        eur_usd = float(auth["eur_usd_rate"])
    except ValueError as error:
        raise PilotError("USD cap and EUR/USD rate must be positive finite numbers") from error
    if not (0 < cap_usd <= HARD_MAX_COST_USD) or not math.isfinite(eur_usd) or eur_usd <= 0:
        raise PilotError("USD cap must be in (0, $20] and EUR/USD rate must be positive and finite")
    if cap * eur_usd > cap_usd:
        raise PilotError("configured EUR cost cap exceeds the explicit USD budget")
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
    fx_checked = parse_utc(auth["fx_checked_at"], "authorization.fx_checked_at")
    fx_age = (now.astimezone(timezone.utc) - fx_checked).total_seconds()
    if fx_age < 0 or fx_age > 24 * 60 * 60:
        raise PilotError("USD/EUR conversion is missing, future-dated, or older than 24 hours")
    requirements = _dict(policy.get("requirements"), "requirements")
    for key, expected in {"single_host": True, "worker_count": 2,
                          "linux_x86_64": True, "public_ipv4": True}.items():
        if type(requirements.get(key)) is not type(expected) or requirements.get(key) != expected:
            raise PilotError(f"requirements.{key} does not match the one-host envelope")
    for key in ("minimum_memory_gib", "minimum_local_disk_gib"):
        if type(requirements.get(key)) is not int or requirements[key] < 1:
            raise PilotError(f"requirements.{key} must be a positive integer")
    root_volume = _parse_root_volume(requirements.get("root_volume"))
    root_size_bytes = root_volume["size_gib"] * 1_000_000_000
    minimum_disk_bytes = requirements["minimum_local_disk_gib"] * 1024**3
    if root_size_bytes < minimum_disk_bytes:
        raise PilotError("requirements.root_volume is smaller than minimum_local_disk_gib")
    machine = _dict(policy.get("machine"), "machine")
    profile = policy.get("cli_profile")
    if type(profile) is not str or not profile.strip() or profile in {"default", "explicit-lean-cloud"}:
        raise PilotError("cli_profile must name the dedicated Scaleway pilot profile")
    if type(machine.get("type")) is not str or not re.fullmatch(r"[A-Z0-9]+(?:-[A-Z0-9]+)*", machine["type"]):
        raise PilotError("machine.type must be an exact Scaleway commercial type")
    for key in ("image_id", "security_group_id", "ssh_key_id", "ssh_identity_file", "ssh_source_cidr", "known_hosts_file"):
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
    if not Path(machine["known_hosts_file"]).is_absolute():
        raise PilotError("known_hosts_file must be an absolute path")
    repo = _dict(policy.get("repository"), "repository")
    if repo.get("url") != CANONICAL_REPO or type(repo.get("commit")) is not str or not COMMIT_RE.fullmatch(repo["commit"]):
        raise PilotError("repository must specify the canonical URL and a full 40-hex commit")
    jobs = policy.get("jobs")
    if not isinstance(jobs, list) or len(jobs) != 2:
        raise PilotError("policy must pin exactly two independent jobs")
    seen: set[str] = set()
    for index, value in enumerate(jobs):
        job = _dict(value, f"jobs[{index}]")
        if job.get("id") not in {"job-000", "job-001"} or job["id"] in seen:
            raise PilotError("job identifiers must be unique job-000 and job-001")
        seen.add(job["id"])
        for key in ("directory", "manifest_sha256", "database_sha256"):
            if type(job.get(key)) is not str or not job[key].strip():
                raise PilotError(f"jobs[{index}].{key} must be explicitly set")
        if not SHA_RE.fullmatch(job["manifest_sha256"]) or not SHA_RE.fullmatch(job["database_sha256"]):
            raise PilotError("job hashes must be lowercase SHA-256 digests")
    if seen != {"job-000", "job-001"}:
        raise PilotError("policy must pin job-000 and job-001")
    return {"deadline": not_after, "lifetime": lifetime, "runtime": runtime, "cost_cap_eur": cap,
            "organization_id": auth["organization_id"], "project_id": auth["project_id"], "zone": zone,
            "machine": machine, "repository": repo, "jobs": jobs, "cli_profile": profile,
            "requirements": requirements, "cost_source": auth["cost_source"],
            "root_volume": root_volume,
            "cost_components_eur": components, "cost_cap_usd": cap_usd, "eur_usd_rate": eur_usd}


def validate_job(job_dir: Path, policy_job: Mapping[str, Any]) -> tuple[Path, Path, list[str]]:
    expected_dir = Path(str(policy_job["directory"])).resolve()
    if job_dir.resolve() != expected_dir:
        raise PilotError("job directory does not match the approved policy")
    manifest, database = job_dir / "modules.txt", job_dir / "mathlib-db.sqlite3"
    if (manifest.is_symlink() or database.is_symlink() or not manifest.is_file() or not database.is_file()
            or not stat.S_ISREG(manifest.stat(follow_symlinks=False).st_mode)
            or not stat.S_ISREG(database.stat(follow_symlinks=False).st_mode)
            or not os.access(database, os.W_OK)):
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


def validate_job_root(job_root: Path, policy_jobs: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    """Check two independent DB copies form an exact pending-module partition."""
    if job_root.is_symlink() or not job_root.is_dir():
        raise PilotError("job root must be a real directory")
    root = job_root.resolve()
    result = []
    for expected_id in ("job-000", "job-001"):
        matches = [item for item in policy_jobs if item.get("id") == expected_id]
        if len(matches) != 1:
            raise PilotError("policy job set is incomplete or ambiguous")
        item = matches[0]
        untrusted_directory = root / expected_id
        if untrusted_directory.is_symlink() or not untrusted_directory.is_dir():
            raise PilotError(f"{expected_id} must be a real directory")
        directory = untrusted_directory.resolve()
        if Path(str(item["directory"])).resolve() != directory:
            raise PilotError(f"{expected_id} directory differs from the approved policy")
        manifest, database, modules = validate_job(directory, item)
        result.append({"id": expected_id, "directory": directory, "manifest": manifest,
                       "database": database, "modules": modules,
                       "manifest_sha256": sha256_file(manifest), "database_sha256": sha256_file(database)})
    db0, db1 = (item["database"] for item in result)
    stat0, stat1 = db0.stat(follow_symlinks=False), db1.stat(follow_symlinks=False)
    if (stat0.st_dev, stat0.st_ino) == (stat1.st_dev, stat1.st_ino):
        raise PilotError("job databases must be distinct regular files, not hard links")
    if result[0]["database_sha256"] != result[1]["database_sha256"]:
        raise PilotError("job databases do not match the same approved baseline bytes")
    queues: list[set[str]] = []
    for job in result:
        uri = f"file:{job['database'].resolve().as_posix()}?mode=ro"
        try:
            con = sqlite3.connect(uri, uri=True)
            try:
                names = {row[0] for row in con.execute(
                    "SELECT DISTINCT r.module_name FROM simp_replacements AS r "
                    "JOIN modules AS m ON m.name=r.module_name WHERE r.status='pending'")}
            finally:
                con.close()
        except sqlite3.Error as error:
            raise PilotError("job database lacks a readable simp replacement baseline") from error
        queues.append(names)
    if queues[0] != queues[1]:
        raise PilotError("job database pending queues differ")
    assigned0, assigned1 = set(result[0]["modules"]), set(result[1]["modules"])
    if assigned0.intersection(assigned1):
        raise PilotError("job manifests overlap")
    assigned = assigned0.union(assigned1)
    if assigned != queues[0]:
        missing = queues[0] - assigned
        extra = assigned - queues[0]
        raise PilotError(f"job manifests are not the exact pending-module partition (missing={len(missing)}, extra={len(extra)})")
    return result


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
        items = _list_response(projects, "projects", "project listing")
        if not any(item.get("id") == checked["project_id"] and item.get("organization_id") == checked["organization_id"] for item in items if isinstance(item, dict)):
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
        servers = _list_response(data, "servers", "server listing")
        tagged = []
        for server in servers:
            if not isinstance(server, dict) or not isinstance(server.get("tags", []), list):
                raise PilotError("server listing entry has unexpected shape")
            if NAME_PREFIX in str(server.get("name", "")) or "explicit-lean-simp-pilot" in server.get("tags", []):
                tagged.append(server)
        volumes = self._scw(["instance", "volume", "list", f"project-id={checked['project_id']}", f"zone={checked['zone']}"], policy=checked)
        items = _list_response(volumes, "volumes", "volume listing")
        matching = []
        for volume in items:
            if not isinstance(volume, dict) or not isinstance(volume.get("tags", []), list):
                raise PilotError("volume listing entry has unexpected shape")
            if NAME_PREFIX in str(volume.get("name", "")) or "explicit-lean-simp-pilot" in volume.get("tags", []):
                matching.append(volume)
        if checked["root_volume"]["kind"] == "sbs":
            block_volumes = self._list_sbs_volumes(checked)
            if any(NAME_PREFIX in str(volume.get("name", ""))
                   or "explicit-lean-simp-pilot" in volume.get("tags", []) for volume in block_volumes):
                raise PilotError("active orphan or duplicate pilot SBS storage exists")
        if tagged or matching:
            raise PilotError("active duplicate pilot server or attached storage exists")
        return servers, items

    def _check_type_image_network(self, checked: Mapping[str, Any]) -> dict[str, Any]:
        zone = checked["zone"]
        machine_type = checked["machine"]["type"]
        minimum_ram = checked["requirements"]["minimum_memory_gib"] * 1024**3
        type_data = self._scw(["instance", "server-type", "list", f"zone={zone}"], policy=checked)
        type_items = _list_response(type_data, "servers", "server-type listing")
        matching_types = [item for item in type_items if isinstance(item, dict) and item.get("name") == machine_type]
        selected_type = matching_types[0] if len(matching_types) == 1 else None
        if not isinstance(selected_type, dict) or selected_type.get("availability") != "available":
            raise PilotError("exact configured server type is unavailable or ambiguous in selected zone")
        if selected_type.get("arch") != "x64":
            raise PilotError("provider server type architecture is not x64 (x86_64)")
        ram = selected_type.get("ram")
        if type(ram) is not int or ram < minimum_ram:
            raise PilotError("provider server type RAM is missing or below the configured minimum")
        image_data = self._scw(["marketplace", "local-image", "list", f"image-id={checked['machine']['image_id']}", f"zone={zone}"], policy=checked)
        images = _list_response(image_data, "images", "marketplace local-image listing") if isinstance(image_data, (list, dict)) else None
        image = checked["machine"]["image_id"]
        expected_image_type = "instance_local" if checked["root_volume"]["kind"] == "local" else "instance_sbs"
        compatible = [x for x in images if isinstance(x, dict) and x.get("arch") == "x86_64"
                      and x.get("zone") == zone and x.get("label") == "ubuntu_noble"
                      and x.get("type") == expected_image_type and isinstance(x.get("compatible_commercial_types"), list)
                      and machine_type in x["compatible_commercial_types"]]
        if len(compatible) != 1:
            raise PilotError("pinned Ubuntu x86_64 image is not compatible with the configured type and root-volume kind")
        sg = self._scw(["instance", "security-group", "get", checked["machine"]["security_group_id"], f"zone={zone}"], policy=checked)
        group = sg.get("security_group", sg) if isinstance(sg, dict) else None
        if not isinstance(group, dict) or group.get("project") != checked["project_id"] and group.get("project_id") != checked["project_id"]:
            raise PilotError("security group project identity does not match policy")
        if group.get("inbound_default_policy") != "drop":
            raise PilotError("security group default inbound policy must drop traffic")
        rules_data = self._scw(["instance", "security-group", "list-rules",
                                f"security-group-id={checked['machine']['security_group_id']}", f"zone={zone}"], policy=checked)
        rules = _list_response(rules_data, "rules", "security-group rule listing")
        cidr = checked["machine"]["ssh_source_cidr"]
        ssh_rules = [r for r in rules if isinstance(r, dict) and r.get("direction") == "inbound"]
        if (len(ssh_rules) != 1 or ssh_rules[0].get("protocol") not in ("TCP", "tcp")
                or ssh_rules[0].get("action") != "accept" or ssh_rules[0].get("dest_port_from") != 22
                or ssh_rules[0].get("dest_port_to") not in (None, 22) or ssh_rules[0].get("ip_range") != cidr):
            raise PilotError("security group must allow only SSH from the approved source CIDR")
        key_data = self._scw(["iam", "ssh-key", "get", checked["machine"]["ssh_key_id"]], policy=checked)
        ssh_key = key_data.get("ssh_key", key_data) if isinstance(key_data, dict) else None
        if (not isinstance(ssh_key, dict)
                or ssh_key.get("project_id", ssh_key.get("project")) != checked["project_id"]):
            raise PilotError("SSH key project identity does not match policy")
        private_key = Path(checked["machine"]["ssh_identity_file"]).expanduser()
        if not private_key.is_file() or not os.access(private_key, os.R_OK):
            raise PilotError("configured SSH identity file is unavailable")
        if stat.S_IMODE(private_key.stat().st_mode) & 0o077:
            raise PilotError("SSH identity file permissions must exclude group and other access")
        known_hosts = Path(checked["machine"]["known_hosts_file"])
        if known_hosts.is_symlink() or not known_hosts.is_file() or not os.access(known_hosts, os.R_OK):
            raise PilotError("dedicated known_hosts_file must be a readable regular file")
        if ssh_key.get("name") is None or not ssh_key.get("public_key"):
            raise PilotError("configured Scaleway SSH key has incomplete identity data")
        public_key = ssh_key.get("public_key")
        if type(public_key) is not str or not re.fullmatch(r"(?:ssh-ed25519|ssh-rsa|ecdsa-sha2-nistp(?:256|384|521)) [A-Za-z0-9+/=]+(?: .*)?", public_key):
            raise PilotError("configured SSH public key has an unsupported or malformed format")
        return {"server_type": {"name": machine_type, **selected_type}, "image_id": image,
                "local_image_id": compatible[0].get("id"), "security_group_id": checked["machine"]["security_group_id"],
                "ssh_key_id": checked["machine"]["ssh_key_id"], "ssh_key_name": ssh_key["name"],
                "ssh_public_key": " ".join(public_key.split()[:2])}

    @staticmethod
    def _one_public_ip(server: Mapping[str, Any]) -> dict[str, Any]:
        candidates = []
        public_ip = server.get("public_ip")
        if isinstance(public_ip, dict):
            candidates.append(public_ip)
        public_ips = server.get("public_ips")
        if isinstance(public_ips, list):
            candidates.extend(item for item in public_ips if isinstance(item, dict))
        unique: dict[str, dict[str, Any]] = {}
        for item in candidates:
            item_id = item.get("id")
            if type(item_id) is not str:
                continue
            previous = unique.get(item_id)
            if previous is not None and any(
                    previous.get(field) != item.get(field)
                    for field in ("address", "family", "dynamic")):
                raise PilotError("server flexible IP records disagree")
            unique[item_id] = item
        if len(unique) != 1:
            raise PilotError("created server must expose exactly one identified flexible IP")
        result = next(iter(unique.values()))
        if not ID_RE.fullmatch(result["id"]) or type(result.get("address")) is not str or not result["address"]:
            raise PilotError("server flexible IP identity is malformed")
        if result.get("family") not in (None, "inet"):
            raise PilotError("server flexible IP is not IPv4")
        if result.get("dynamic") not in (None, False):
            raise PilotError("server public IP is not the requested flexible IP")
        return result

    @classmethod
    def _state_pinned_public_ip(cls, server: Mapping[str, Any], state: Mapping[str, Any]) -> dict[str, Any]:
        public_ip = cls._one_public_ip(server)
        expected_id, expected_address = state.get("public_ip_id"), state.get("public_ip_address")
        if (type(expected_id) is not str or expected_id != public_ip["id"]
                or type(expected_address) is not str or expected_address != public_ip["address"]):
            raise PilotError("server flexible IP differs from state-pinned identity")
        return public_ip

    def _get_sbs_volume(self, volume_id: str, checked: Mapping[str, Any], *,
                        expected_server_id: str | None = None,
                        require_detached: bool = False) -> dict[str, Any]:
        response = self._scw(["block", "volume", "get", volume_id, f"zone={checked['zone']}"], policy=checked)
        details = response.get("volume", response) if isinstance(response, dict) else None
        root = checked["root_volume"]
        detail_id = details.get("id", details.get("volume_id")) if isinstance(details, dict) else None
        if (not isinstance(details, dict) or detail_id != volume_id
                or details.get("type") not in root["block_types"]
                or type(details.get("size")) is not int
                or details["size"] != root["size_gib"] * 1_000_000_000
                or not isinstance(details.get("specs"), dict)
                or details["specs"].get("perf_iops") != root["iops"]):
            raise PilotError("SBS volume identity, type, exact size, or IOPS differs from policy")
        project = details.get("project_id", details.get("project"))
        if isinstance(project, dict):
            project = project.get("id")
        if project is not None and project != checked["project_id"]:
            raise PilotError("SBS volume project differs from policy")
        if details.get("zone") is not None and details["zone"] != checked["zone"]:
            raise PilotError("SBS volume zone differs from policy")
        server_ref = details.get("server_id", details.get("server"))
        if isinstance(server_ref, dict):
            server_ref = server_ref.get("id")
        if server_ref is not None and (require_detached or server_ref != expected_server_id):
            raise PilotError("SBS volume attachment identity is unexpected")
        return details

    def _list_sbs_volumes(self, checked: Mapping[str, Any]) -> list[dict[str, Any]]:
        response = self._scw(["block", "volume", "list", f"project-id={checked['project_id']}",
                              f"zone={checked['zone']}"], policy=checked)
        items = _list_response(response, "volumes", "SBS volume listing")
        volumes: list[dict[str, Any]] = []
        for item in items:
            if not isinstance(item, dict):
                raise PilotError("SBS volume listing entry has unexpected shape")
            volume_id = item.get("id", item.get("volume_id"))
            if type(volume_id) is not str or not ID_RE.fullmatch(volume_id):
                raise PilotError("SBS volume listing entry lacks an exact ID")
            project = item.get("project_id", item.get("project"))
            if isinstance(project, dict):
                project = project.get("id")
            if project is not None and project != checked["project_id"]:
                raise PilotError("SBS volume listing contains a volume from another project")
            if item.get("zone") is not None and item["zone"] != checked["zone"]:
                raise PilotError("SBS volume listing contains a volume from another zone")
            if "tags" in item and not isinstance(item["tags"], list):
                raise PilotError("SBS volume listing tags have unexpected shape")
            volumes.append(item)
        return volumes

    def _cleanup_sbs_volumes(self, checked: Mapping[str, Any], known_ids: set[str], *,
                             require_known_visible: bool = False) -> None:
        if len(known_ids) > 1 or any(not ID_RE.fullmatch(volume_id) for volume_id in known_ids):
            raise PilotError("saved SBS root-volume identity is malformed or ambiguous")
        items = self._list_sbs_volumes(checked)
        listed_ids = {item.get("id", item.get("volume_id")) for item in items}
        tagged = [item for item in items if (NAME_PREFIX in str(item.get("name", ""))
                  or "explicit-lean-simp-pilot" in item.get("tags", []))]
        if any(item.get("id", item.get("volume_id")) not in known_ids for item in tagged):
            raise PilotError("tagged SBS storage does not match the exact saved root volume")
        if require_known_visible and (not known_ids or not known_ids.issubset(listed_ids)):
            raise PilotError("exact SBS root volume is not visible in block volume listing; retry cleanup")
        for volume_id in sorted(known_ids & listed_ids):
            self._get_sbs_volume(volume_id, checked, require_detached=True)
            self._scw(["block", "volume", "delete", volume_id, f"zone={checked['zone']}", "--wait"],
                      policy=checked, timeout=300)
        after = self._list_sbs_volumes(checked)
        after_ids = {item.get("id", item.get("volume_id")) for item in after}
        after_tagged = [item for item in after if (NAME_PREFIX in str(item.get("name", ""))
                        or "explicit-lean-simp-pilot" in item.get("tags", []))]
        if known_ids & after_ids or after_tagged:
            raise PilotError("SBS root-volume deletion could not be confirmed")

    @staticmethod
    def _server_root_attachment(server: Mapping[str, Any], checked: Mapping[str, Any]) -> dict[str, Any]:
        has_upper = "Volumes" in server
        has_lower = "volumes" in server
        if has_upper and has_lower:
            raise PilotError("server response has ambiguous Volumes/volumes fields")
        volume_key = "Volumes" if has_upper else "volumes"
        volumes = server.get(volume_key)
        if isinstance(volumes, dict):
            if set(volumes) != {"0"}:
                raise PilotError("created server exposes unknown or multiple attached volumes")
            attachment = volumes["0"]
            slot_zero = True
        elif isinstance(volumes, list) and len(volumes) == 1:
            attachment = volumes[0]
            slot_zero = has_upper
        else:
            raise PilotError("created server volume inventory is unavailable or ambiguous")
        if not isinstance(attachment, dict) or type(attachment.get("id")) is not str or not ID_RE.fullmatch(attachment["id"]):
            raise PilotError("created server root volume lacks an identified volume")
        root = checked["root_volume"]
        attachment_type = attachment.get("volume_type")
        if type(attachment_type) is not str or attachment_type not in root["provider_types"]:
            raise PilotError("created server root attachment type differs from policy")
        expected_bytes = root["size_gib"] * 1_000_000_000
        if attachment.get("size") is not None and (
                type(attachment["size"]) is not int or attachment["size"] != expected_bytes):
            raise PilotError("created server root attachment size differs from policy")
        attachment_iops = attachment.get("iops")
        if attachment_iops is not None:
            expected_iops = root.get("iops")
            if type(attachment_iops) is str:
                actual_iops = {"5K": 5000, "15K": 15000}.get(attachment_iops)
            elif type(attachment_iops) is int:
                actual_iops = attachment_iops
            else:
                actual_iops = None
            if type(actual_iops) is not int or actual_iops != expected_iops:
                raise PilotError("created server root attachment IOPS differs from policy")
        boot_ref = server.get("boot_volume_id", server.get("boot_volume"))
        if isinstance(boot_ref, dict):
            boot_ref = boot_ref.get("id")
        if boot_ref is not None:
            if type(boot_ref) is not str or attachment["id"] != boot_ref:
                raise PilotError("created server root volume does not match its boot-volume reference")
        elif not (attachment.get("boot") is True or (
                root["kind"] == "sbs" and slot_zero and attachment.get("boot") in (None, False))):
            raise PilotError("created server root volume is not explicitly identified as the boot volume")
        return attachment

    def _verify_server_identity(self, server: Mapping[str, Any], checked: Mapping[str, Any],
                                state: Mapping[str, Any]) -> dict[str, Any]:
        tags = server.get("tags")
        if (server.get("id") != state.get("server_id") or server.get("name") != state.get("name")
                or server.get("project", server.get("project_id")) != checked["project_id"]
                or server.get("zone") != checked["zone"]
                or server.get("commercial_type", server.get("type")) != checked["machine"]["type"]
                or not isinstance(tags, list) or "explicit-lean-simp-pilot" not in tags):
            raise PilotError("server identity/ownership tags do not match the authorized run")
        image = server.get("image")
        image_id = image.get("id") if isinstance(image, dict) else image
        if image_id != state.get("local_image_id"):
            raise PilotError("created server image does not match the pinned local image")
        if isinstance(image, dict) and (image.get("arch") not in (None, "x86_64")
                or image.get("zone") not in (None, checked["zone"])):
            raise PilotError("created server image architecture or zone differs from policy")
        if isinstance(image, dict) and image.get("name") is not None and "ubuntu" not in str(image["name"]).lower():
            raise PilotError("created server image is not the pinned Ubuntu image")
        group = server.get("security_group")
        group_id = group.get("id") if isinstance(group, dict) else group
        if group_id != checked["machine"]["security_group_id"]:
            raise PilotError("created server security group does not match policy")
        key_id = checked["machine"]["ssh_key_id"]
        for field in ("ssh_key_id", "admin_password_encryption_ssh_key_id"):
            observed_key = server.get(field)
            if observed_key is not None and observed_key != key_id:
                raise PilotError("created server SSH key identity differs from policy")
        preflight = state.get("preflight")
        preflight_machine = preflight.get("machine") if isinstance(preflight, dict) else None
        public_key = preflight_machine.get("ssh_public_key") if isinstance(preflight_machine, dict) else None
        if (state.get("ssh_key_id") != key_id or type(public_key) is not str
                or state.get("ssh_public_key_sha256") != sha256(public_key.encode("utf-8"))):
            raise PilotError("server bootstrap SSH key provenance is not pinned")
        root_policy = checked["root_volume"]
        attached_root = self._server_root_attachment(server, checked)
        details = attached_root
        if root_policy["kind"] == "sbs":
            details = self._get_sbs_volume(attached_root["id"], checked,
                                           expected_server_id=state.get("server_id"))
        elif type(details.get("size")) is not int:
            response = self._scw(["instance", "volume", "get", attached_root["id"], f"zone={checked['zone']}"] , policy=checked)
            details = response.get("volume", response) if isinstance(response, dict) else None
        expected_bytes = root_policy["size_gib"] * 1_000_000_000
        detail_id = details.get("id", details.get("volume_id")) if isinstance(details, dict) else None
        detail_type = details.get("volume_type") if isinstance(details, dict) else None
        reported_project = details.get("project_id", details.get("project")) if isinstance(details, dict) else None
        if isinstance(reported_project, dict):
            reported_project = reported_project.get("id")
        reported_zone = details.get("zone") if isinstance(details, dict) else None
        if root_policy["kind"] == "local" and (not isinstance(details, dict) or detail_id != attached_root["id"]
                or detail_type not in root_policy["provider_types"]
                or type(details.get("size")) is not int or details["size"] != expected_bytes):
            raise PilotError("created server root volume type or exact size differs from policy")
        if root_policy["kind"] == "local" and reported_project is not None and reported_project != checked["project_id"]:
            raise PilotError("created server root volume project differs from policy")
        if root_policy["kind"] == "local" and reported_zone is not None and reported_zone != checked["zone"]:
            raise PilotError("created server root volume zone differs from policy")
        public_ip = self._one_public_ip(server)
        expected_ip_id = state.get("public_ip_id")
        if expected_ip_id is not None and expected_ip_id != public_ip["id"]:
            raise PilotError("server flexible IP changed from the created resource")
        if state.get("public_ip_address") is not None and state["public_ip_address"] != public_ip["address"]:
            raise PilotError("server flexible IP address changed from the created resource")
        return {"public_ip_id": public_ip["id"], "public_ip_address": public_ip["address"],
                "volume_ids": [attached_root["id"]]}

    def _require_known_host(self, address: str, machine: Mapping[str, Any]) -> None:
        path = Path(str(machine["known_hosts_file"]))
        if path.is_symlink() or not path.is_file() or not os.access(path, os.R_OK):
            raise PilotError("dedicated known_hosts_file must be a readable regular file")
        result = self._run(["ssh-keygen", "-F", address, "-f", str(path)], 10)
        if result.returncode != 0:
            raise PilotError("verified server host key is absent from the dedicated known_hosts_file")

    def preflight(self, *, repo_root: Path, job_root: Path) -> dict[str, Any]:
        policy, raw = self.policy()
        checked = validate_policy(policy, self.now())
        jobs = validate_job_root(job_root, checked["jobs"])
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
                "jobs": [{"id": job["id"], "module_count": len(job["modules"]),
                          "manifest_sha256": job["manifest_sha256"],
                          "database_sha256": job["database_sha256"]} for job in jobs], "worker_count": 2,
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

    def create(self, *, repo_root: Path, job_root: Path, confirm: bool = False) -> dict[str, Any]:
        lock_path = self.state_path.with_suffix(self.state_path.suffix + ".lock")
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o600)
        try:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise PilotError("another local Scaleway create operation is in progress") from error
            return self._create_locked(repo_root=repo_root, job_root=job_root, confirm=confirm)
        finally:
            os.close(descriptor)

    def _create_locked(self, *, repo_root: Path, job_root: Path, confirm: bool) -> dict[str, Any]:
        if not confirm:
            raise PilotError("creation requires --confirm-create")
        if self.state_path.exists():
            raise PilotError("a pilot state file already exists; this controller instance is single-use")
        preflight = self.preflight(repo_root=repo_root, job_root=job_root)
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
        remote_job_directory = f"/home/{login_user}/explicit-lean-simp-jobs"
        state = {"schema": 1, "phase": "create-requested", "server_id": None, "name": name,
                 "remote_job_directory": remote_job_directory, "zone": checked["zone"],
                 "project_id": checked["project_id"], "organization_id": checked["organization_id"],
                 "created_at": create_started.isoformat(), "deadline": host_deadline.isoformat(),
                 "lifetime_seconds": checked["lifetime"], "worker_runtime_seconds": checked["runtime"],
                 "policy_sha256": preflight["policy_sha256"], "preflight": preflight,
                 "local_image_id": preflight["machine"]["local_image_id"],
                 "ssh_key_id": checked["machine"]["ssh_key_id"],
                 "ssh_public_key_sha256": sha256(preflight["machine"]["ssh_public_key"].encode("utf-8")),
                 "jobs": [{"id": job["id"], "manifest_sha256": job["manifest_sha256"],
                           "database_sha256": job["database_sha256"], "module_count": len(job["modules"]),
                           "phase": "pending"} for job in validate_job_root(job_root, checked["jobs"])],
                 "mutation": "server-create-requested"}
        cloud_path: Path | None = None
        try:
            with tempfile.NamedTemporaryFile("w", encoding="utf-8", prefix="scw-cloud-init-", suffix=".yaml", delete=False) as handle:
                handle.write(cloud_config); cloud_path = Path(handle.name)
            self._save(state)
            result = self._scw(["instance", "server", "create", f"name={name}", f"type={checked['machine']['type']}",
                                f"image={preflight['machine']['local_image_id']}", "ip=new", f"root-volume={checked['requirements']['root_volume']}",
                                f"security-group-id={checked['machine']['security_group_id']}",
                                f"cloud-init=@{cloud_path}", f"project-id={checked['project_id']}", f"zone={checked['zone']}",
                                "tags.0=explicit-lean-simp-pilot", "tags.1=two-workers", "--wait"], policy=checked, timeout=300)
        except PilotError as error:
            raise PilotError("create outcome is ambiguous; state retained; use status, then cleanup to recover any created server") from error
        finally:
            if cloud_path is not None:
                cloud_path.unlink(missing_ok=True)
        server = result.get("server", result) if isinstance(result, dict) else None
        server_id = server.get("id") if isinstance(server, dict) else None
        if type(server_id) is not str or not ID_RE.fullmatch(server_id):
            raise PilotError("create response lacks a valid server ID; state retained for status/cleanup recovery")
        state.update({"phase": "created", "server_id": server_id, "mutation": "server-create"})
        if isinstance(server, dict):
            try:
                initial_ip = self._one_public_ip(server)
            except PilotError:
                # The follow-up get is authoritative; preserve recoverable state.
                pass
            else:
                state["public_ip_id"] = initial_ip["id"]
                state["public_ip_address"] = initial_ip["address"]
        self._save(state)
        observed = self._scw(["instance", "server", "get", server_id, f"zone={checked['zone']}"], policy=checked)
        observed_server = observed.get("server", observed)
        if not isinstance(observed_server, dict):
            raise PilotError("created server details are malformed; state retained for cleanup")
        verified = self._verify_server_identity(observed_server, checked, state)
        state.update(verified)
        self._save(state)
        return state

    def status(self) -> dict[str, Any]:
        state, policy = self._existing_context()
        auth = _dict(policy.get("authorization"), "authorization")
        self._identity({"organization_id": auth["organization_id"], "project_id": auth["project_id"],
                        "cli_profile": policy["cli_profile"]})
        if not state.get("server_id"):
            listing = self._scw(["instance", "server", "list", f"project-id={state['project_id']}", f"zone={state['zone']}"], policy=policy)
            servers = _list_response(listing, "servers", "pending-create server listing")
            candidates = [server for server in servers if isinstance(server, dict) and server.get("name") == state.get("name")]
            return {"read_only": True, "phase": state.get("phase"), "state": state, "pending_create_matches": candidates}
        if state.get("phase") in {"workers-running", "workers-finished", "workers-failed"}:
            workers = self.poll_workers()
            state, policy = self._existing_context()
        else:
            workers = None
        server = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        if not isinstance(server, dict):
            raise PilotError("server status response has unexpected shape")
        return {"read_only": True, "state": state, "workers": workers, "provider": server.get("server", server)}

    def _ssh(self, state: Mapping[str, Any], *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
        policy, _ = self.policy(); machine = _dict(policy.get("machine"), "machine")
        server = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        data = server.get("server", server) if isinstance(server, dict) else None
        if not isinstance(data, dict) or data.get("id") != state.get("server_id"):
            raise PilotError("server address response identity mismatch")
        address = self._state_pinned_public_ip(data, state)["address"]
        self._require_known_host(address, machine)
        base = ["ssh", "-i", str(Path(machine["ssh_identity_file"]).expanduser()), "-o", "BatchMode=yes",
                "-o", "StrictHostKeyChecking=yes", "-o", f"UserKnownHostsFile={machine['known_hosts_file']}",
                "-o", "ConnectTimeout=20", f"{policy.get('login_user', 'ubuntu')}@{address}"]
        return self._run([*base, *args], timeout)

    def _launch_worker_once(self, state: Mapping[str, Any], job: Mapping[str, Any],
                            worker_timeout: int, commit: str, launch_token: str) -> subprocess.CompletedProcess[str]:
        """Atomically claim a job before launch; an existing claim is never relaunched."""
        remote_job = state["remote_job_directory"] + "/" + job["id"]
        worker = ("set +e; timeout --signal=TERM --kill-after=30 " + str(worker_timeout) +
                  " python3 -B Experiment/simp_replacement_worker.py --database " + remote_job +
                  "/mathlib-db.sqlite3 --manifest " + remote_job + "/modules.txt --artifacts " + remote_job +
                  "/artifacts > " + remote_job + "/worker.log 2>&1; rc=$?; "
                  "dbhash=$(sha256sum " + remote_job + "/mathlib-db.sqlite3 | awk '{print $1}'); "
                  "manifesthash=$(sha256sum " + remote_job + "/modules.txt | awk '{print $1}'); "
                  "printf '{\"schema\":1,\"exit_code\":%s,\"commit\":\"%s\",\"database_sha256\":\"%s\",\"manifest_sha256\":\"%s\"}\\n' \"$rc\" " +
                  shlex.quote(commit) + " \"$dbhash\" \"$manifesthash\" > " + remote_job +
                  "/complete.json.tmp; mv " + remote_job + "/complete.json.tmp " + remote_job +
                  "/complete.json; tar -czf " + remote_job + "/result.tar.gz -C " + remote_job +
                  " mathlib-db.sqlite3 worker.log complete.json artifacts")
        script = ("set -eu; d=" + shlex.quote(remote_job) + "; token=" + shlex.quote(launch_token) + "; mkdir -p \"$d/artifacts\"; "
                  "if test -f \"$d/complete.json\"; then printf 'COMPLETE\\n'; exit 0; fi; "
                  "if ! mkdir \"$d/.launch-claim\" 2>/dev/null; then "
                  "p=$(cat \"$d/worker.pid\" 2>/dev/null || true); "
                  "case \"$p\" in ''|*[!0-9]*) printf 'AMBIGUOUS\\n'; exit 42;; esac; "
                  "expected=$(cat \"$d/.launch-claim/token\" 2>/dev/null || true); "
                  "if test \"$expected\" = \"$token\" && kill -0 \"$p\" 2>/dev/null "
                  "&& tr '\\000' '\\n' < \"/proc/$p/environ\" | grep -Fx \"EXPLICIT_LEAN_WORKER_TOKEN=$token\" >/dev/null "
                  "&& tr '\\000' ' ' < \"/proc/$p/cmdline\" | grep -F \"Experiment/simp_replacement_worker.py --database $d/mathlib-db.sqlite3 --manifest $d/modules.txt\" >/dev/null; "
                  "then printf 'RUNNING %s\\n' \"$p\"; exit 0; fi; "
                  "printf 'AMBIGUOUS\\n'; exit 42; fi; "
                  "printf '%s\\n' \"$token\" > \"$d/.launch-claim/token.tmp\"; "
                  "mv \"$d/.launch-claim/token.tmp\" \"$d/.launch-claim/token\"; "
                  "cd /opt/explicit-lean; . \"$HOME/.elan/env\"; "
                  "EXPLICIT_LEAN_WORKER_TOKEN=\"$token\" nohup bash -lc " + shlex.quote(worker) + " > \"$d/launcher.log\" 2>&1 < /dev/null & "
                  "p=$!; printf '%s\\n' \"$p\" > \"$d/worker.pid.tmp\"; "
                  "mv \"$d/worker.pid.tmp\" \"$d/worker.pid\"; printf 'RUNNING %s\\n' \"$p\"")
        return self._ssh(state, "sh", "-lc", shlex.quote(script), timeout=60)

    @staticmethod
    def _bootstrap_resume_is_safe(state: Mapping[str, Any]) -> bool:
        """Only retry bootstrap while state proves dispatch has not begun."""
        if state.get("phase") != "bootstrap-started":
            return False
        if "worker_started_at" in state or "worker_timeout_seconds" in state:
            return False
        jobs = state.get("jobs")
        if not isinstance(jobs, list) or len(jobs) != 2:
            return False
        job_ids = [job.get("id") for job in jobs if isinstance(job, dict)]
        if len(job_ids) != 2 or any(type(job_id) is not str for job_id in job_ids) or set(job_ids) != {"job-000", "job-001"}:
            return False
        return all(isinstance(job, dict) and job.get("phase") == "pending" and "launch_token" not in job
                   for job in jobs)

    def _reconcile_dispatch(self, state: dict[str, Any], policy: Mapping[str, Any],
                            checked: Mapping[str, Any]) -> dict[str, Any]:
        """Resume a partial dispatch without duplicating any potentially launched worker."""
        remote = state.get("remote_job_directory")
        if remote != "/home/ubuntu/explicit-lean-simp-jobs":
            raise PilotError("saved remote jobs directory is invalid")
        jobs = {item["id"]: item for item in state.get("jobs", [])}
        if set(jobs) != {"job-000", "job-001"}:
            raise PilotError("saved dispatch job set is incomplete")
        created = datetime.fromisoformat(state["created_at"]).astimezone(timezone.utc)
        hard_end = min(created + timedelta(seconds=checked["lifetime"]), checked["deadline"])
        worker_end = datetime.fromisoformat(state["worker_started_at"]).astimezone(timezone.utc) + timedelta(
            seconds=int(state["worker_timeout_seconds"]))
        now = self.now().astimezone(timezone.utc)
        worker_timeout = int((min(hard_end, worker_end) - now).total_seconds())
        status_shell = ("set -eu; d=" + remote + "/{job}; "
                        "if test -f \"$d/complete.json\"; then printf 'COMPLETE\\t'; cat \"$d/complete.json\"; "
                        "elif test -d \"$d/.launch-claim\"; then p=$(cat \"$d/worker.pid\" 2>/dev/null || true); "
                        "token=$(cat \"$d/.launch-claim/token\" 2>/dev/null || true); expected=EXPECTED_TOKEN; "
                        "case \"$p\" in ''|*[!0-9]*) printf 'AMBIGUOUS\\n';; *) "
                        "if test \"$token\" = \"$expected\" && kill -0 \"$p\" 2>/dev/null "
                        "&& tr '\\000' '\\n' < \"/proc/$p/environ\" | grep -Fx \"EXPLICIT_LEAN_WORKER_TOKEN=$expected\" >/dev/null "
                        "&& tr '\\000' ' ' < \"/proc/$p/cmdline\" | grep -F \"Experiment/simp_replacement_worker.py --database $d/mathlib-db.sqlite3 --manifest $d/modules.txt\" >/dev/null; "
                        "then printf 'RUNNING\\t%s\\n' \"$p\"; "
                        "else printf 'AMBIGUOUS\\n'; fi;; esac; "
                        "elif test -e \"$d/worker.pid\" || test -e \"$d/complete.json.tmp\" "
                        "|| test -e \"$d/result.tar.gz\"; then printf 'AMBIGUOUS\\n'; "
                        "else printf 'NOT_LAUNCHED\\n'; fi")
        commit = str(_dict(policy.get("repository"), "repository")["commit"])
        for job_id in ("job-000", "job-001"):
            if not jobs[job_id].get("launch_token"):
                jobs[job_id] = {**jobs[job_id], "launch_token": uuid.uuid4().hex}
                state["jobs"] = [jobs[key] for key in ("job-000", "job-001")]
                self._save(state)
            launch_token = jobs[job_id]["launch_token"]
            if not re.fullmatch(r"[0-9a-f]{32}", str(launch_token)):
                raise PilotError(f"{job_id} launch token is malformed")
            command = status_shell.replace("EXPECTED_TOKEN", shlex.quote(str(launch_token))).format(job=job_id)
            result = self._ssh(state, "sh", "-lc", shlex.quote(command), timeout=60)
            if result.returncode:
                state["phase"] = "dispatch-failed"
                state["dispatch_error"] = f"could not reconcile {job_id}; outcome remains unknown"
                self._save(state)
                raise PilotError(state["dispatch_error"])
            observed = result.stdout.strip()
            if observed == "NOT_LAUNCHED":
                if worker_timeout <= 0:
                    state["phase"] = "dispatch-failed"
                    self._save(state)
                    raise PilotError(f"{job_id} is provably not launched but no worker budget remains")
                launched = self._launch_worker_once(state, jobs[job_id], worker_timeout, commit, str(launch_token))
                if launched.returncode:
                    state["phase"] = "dispatch-failed"
                    state["dispatch_error"] = f"{job_id} launch outcome is ambiguous; refusing relaunch"
                    self._save(state)
                    raise PilotError(state["dispatch_error"])
                observed = launched.stdout.strip()
            if observed.startswith("RUNNING ") or observed.startswith("RUNNING\t"):
                pid = observed.split(maxsplit=1)[1]
                if not pid.isdigit():
                    raise PilotError(f"{job_id} returned an invalid worker PID")
                jobs[job_id] = {**jobs[job_id], "phase": "running", "pid": pid}
            elif observed.startswith("COMPLETE\t"):
                try:
                    marker = json.loads(observed.split("\t", 1)[1])
                except (json.JSONDecodeError, IndexError) as error:
                    raise PilotError(f"{job_id} completion marker is malformed") from error
                if (marker.get("commit") != commit or marker.get("manifest_sha256") != jobs[job_id].get("manifest_sha256")
                        or type(marker.get("exit_code")) is not int or not re.fullmatch(r"[0-9a-f]{64}", str(marker.get("database_sha256")))):
                    raise PilotError(f"{job_id} completion marker does not match its pinned job")
                jobs[job_id] = {**jobs[job_id], "phase": "finished" if marker["exit_code"] == 0 else "failed",
                                "exit_code": marker["exit_code"], "database_result_sha256": marker["database_sha256"]}
            else:
                state.update({"phase": "dispatch-failed", "jobs": [jobs[key] for key in ("job-000", "job-001")],
                              "dispatch_error": f"{job_id} launch state is ambiguous; refusing to start another worker"})
                self._save(state)
                raise PilotError(state["dispatch_error"])
            state["jobs"] = [jobs[key] for key in ("job-000", "job-001")]
            self._save(state)
        phases = [jobs[key]["phase"] for key in ("job-000", "job-001")]
        state["phase"] = ("workers-running" if "running" in phases else
                           "workers-finished" if all(value == "finished" for value in phases) else "workers-failed")
        if state["phase"] != "workers-running":
            state["workers_finished_at"] = self.now().isoformat()
        state.pop("dispatch_error", None)
        self._save(state)
        return state

    def run_workers(self, *, job_root: Path, repo_root: Path) -> dict[str, Any]:
        state = self._load_state(); policy, raw = self.policy(); checked = validate_policy(policy, self.now())
        if state.get("policy_sha256") != sha256(raw):
            raise PilotError("policy changed after server creation")
        if state.get("project_id") != checked["project_id"] or state.get("organization_id") != checked["organization_id"] or state.get("zone") != checked["zone"]:
            raise PilotError("saved server identity differs from launch policy")
        jobs = validate_job_root(job_root, checked["jobs"])
        created = datetime.fromisoformat(state["created_at"])
        now = self.now().astimezone(timezone.utc)
        age = (now - created.astimezone(timezone.utc)).total_seconds()
        if age >= checked["lifetime"] or now >= checked["deadline"]:
            raise PilotError("host TTL or authorization deadline reached")
        if state.get("phase") != "created" and not self._bootstrap_resume_is_safe(state):
            raise PilotError("both workers may be dispatched once per server")
        self._repo_gate(checked, repo_root)
        self._identity(checked); self._check_type_image_network(checked)
        observed = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=checked)
        observed_server = observed.get("server", observed)
        if not isinstance(observed_server, dict):
            raise PilotError("existing server details are malformed")
        verified = self._verify_server_identity(observed_server, checked, state)
        if state.get("volume_ids") and verified["volume_ids"] != state["volume_ids"]:
            raise PilotError("created server root volume identity changed")
        state.update(verified)
        self._save(state)
        ttl_remaining = int(checked["lifetime"] - age)
        cutoff_remaining = int((checked["deadline"] - now).total_seconds())
        worker_timeout = min(checked["runtime"], ttl_remaining, cutoff_remaining)
        if worker_timeout <= 0:
            raise PilotError("no worker runtime remains before host TTL/deadline")
        watchdog = self._ssh(state, "sudo", "systemd-run", f"--unit=explicit-lean-simp-ttl-{state['server_id']}",
                             f"--on-active={ttl_remaining}s", "/usr/bin/systemctl", "poweroff", timeout=60)
        if watchdog.returncode:
            raise PilotError("guest TTL watchdog could not be armed")
        state.update({"guest_poweroff_watchdog_armed": True, "host_ttl_remaining_seconds": ttl_remaining})
        self._save(state)
        commit = checked["repository"]["commit"]
        bootstrap = "set -eu; test \"$(uname -m)\" = x86_64; test -f /etc/os-release; " \
                    "sudo apt-get update; sudo DEBIAN_FRONTEND=noninteractive apt-get install -y git python3 python3-pip build-essential curl zstd; " \
                    "git ls-remote https://github.com/Barraketh/explicit-lean.git | awk '{print $1}' | grep -Fx " + shlex.quote(commit) + "; " \
                    "sudo install -d -o ubuntu -g ubuntu /opt/explicit-lean; " \
                    "if test -d /opt/explicit-lean/.git; then " \
                    "test \"$(git -C /opt/explicit-lean remote get-url origin)\" = https://github.com/Barraketh/explicit-lean.git; " \
                    "else test -z \"$(find /opt/explicit-lean -mindepth 1 -maxdepth 1 -print -quit)\"; " \
                    "git clone --no-checkout https://github.com/Barraketh/explicit-lean.git /opt/explicit-lean/.; fi; " \
                    "git -C /opt/explicit-lean fetch --no-tags origin " + shlex.quote(commit) + "; " \
                    "git -C /opt/explicit-lean checkout --detach " + shlex.quote(commit) + "; " \
                    "test \"$(git -C /opt/explicit-lean rev-parse HEAD)\" = " + shlex.quote(commit) + "; " \
                    "curl --fail --silent --show-error " + ELAN_URL + " -o /tmp/elan.tar.gz; " \
                    "echo " + ELAN_SHA256 + "'  /tmp/elan.tar.gz' | sha256sum -c -; " \
                    "tar -xzf /tmp/elan.tar.gz -C /tmp elan-init; /tmp/elan-init -y --default-toolchain none; " \
                    ". \"$HOME/.elan/env\"; cd /opt/explicit-lean; lake exe cache get; " \
                    "lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw; " \
                    "test -s .lake/build/lib/lean/ExplicitLean/SimpTrace.olean; " \
                    "test -s .lake/build/lib/lean/ExplicitLean/ExplicitRw.olean"
        state.update({"phase": "bootstrap-started", "bootstrap_started_at": now.isoformat()}); self._save(state)
        boot = self._ssh(state, "sh", "-lc", shlex.quote(bootstrap), timeout=min(1800, checked["runtime"]))
        if boot.returncode:
            raise PilotError(f"remote pinned checkout/dependency bootstrap failed (exit {boot.returncode})")
        remote = state.get("remote_job_directory")
        if remote != "/home/ubuntu/explicit-lean-simp-jobs":
            raise PilotError("saved remote job directory is invalid")
        mkdir = self._ssh(state, "mkdir", "-p", remote, timeout=60)
        if mkdir.returncode:
            raise PilotError("remote jobs directory creation failed")
        machine = checked["machine"]
        server_data = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        server_obj = server_data.get("server", server_data)
        if not isinstance(server_obj, dict) or server_obj.get("id") != state["server_id"]:
            raise PilotError("server identity changed before job transfer")
        address = self._state_pinned_public_ip(server_obj, state)["address"]
        self._require_known_host(address, machine)
        target = f"{policy.get('login_user', 'ubuntu')}@{address}:{remote}/"
        scp_base = ["scp", "-r", "-i", str(Path(machine["ssh_identity_file"]).expanduser()), "-o", "BatchMode=yes",
                    "-o", "StrictHostKeyChecking=yes", "-o", f"UserKnownHostsFile={machine['known_hosts_file']}"]
        copied = self._run([*scp_base, *(str(job["directory"]) for job in jobs), target], min(600, checked["runtime"]))
        if copied.returncode:
            raise PilotError("two-job transfer failed")
        for job in jobs:
            remote_job = remote + "/" + job["id"]
            verify = ("set -eu; test \"$(sha256sum " + remote_job + "/modules.txt | awk '{print $1}')\" = " +
                      shlex.quote(job["manifest_sha256"]) + "; test \"$(sha256sum " + remote_job +
                      "/mathlib-db.sqlite3 | awk '{print $1}')\" = " + shlex.quote(job["database_sha256"]))
            checked_remote = self._ssh(state, "sh", "-lc", shlex.quote(verify), timeout=60)
            if checked_remote.returncode:
                raise PilotError(f"uploaded {job['id']} input hashes differ from policy")
        dispatch_now = self.now().astimezone(timezone.utc)
        elapsed = (dispatch_now - created.astimezone(timezone.utc)).total_seconds()
        worker_timeout = min(checked["runtime"], int(checked["lifetime"] - elapsed),
                             int((checked["deadline"] - dispatch_now).total_seconds()))
        if worker_timeout <= 0:
            raise PilotError("bootstrap and transfer consumed the remaining worker window")
        state.update({"phase": "dispatching", "worker_started_at": dispatch_now.isoformat(),
                      "worker_timeout_seconds": worker_timeout,
                      "jobs": [{"id": item["id"], "manifest_sha256": item["manifest_sha256"],
                                "database_sha256": item["database_sha256"], "module_count": item["module_count"],
                                "phase": "starting"} for item in state["jobs"]]})
        self._save(state)
        return self._reconcile_dispatch(state, checked, checked)

    def poll_workers(self) -> dict[str, Any]:
        state, policy = self._existing_context()
        if state.get("phase") not in {"workers-running", "workers-finished", "workers-failed"}:
            raise PilotError("worker status requires dispatched jobs")
        remote = state.get("remote_job_directory")
        if remote != "/home/ubuntu/explicit-lean-simp-jobs":
            raise PilotError("saved remote jobs directory is invalid")
        command = "set -eu; for j in job-000 job-001; do d=" + remote + "/$j; if test -f \"$d/complete.json\"; then printf '%s\\t' \"$j\"; cat \"$d/complete.json\"; else printf '%s\\tRUNNING\\n' \"$j\"; fi; done"
        result = self._ssh(state, "sh", "-lc", shlex.quote(command), timeout=60)
        if result.returncode:
            raise PilotError("worker status poll failed")
        observed: dict[str, str] = {}
        for line in result.stdout.splitlines():
            parts = line.split("\t", 1)
            if len(parts) != 2 or parts[0] not in {"job-000", "job-001"} or parts[0] in observed:
                raise PilotError("worker status response is malformed")
            observed[parts[0]] = parts[1]
        if set(observed) != {"job-000", "job-001"}:
            raise PilotError("worker status response is incomplete")
        statuses = []
        for item in state["jobs"]:
            text = observed[item["id"]]
            if text == "RUNNING":
                statuses.append({**item, "phase": "running"})
            else:
                try:
                    marker = json.loads(text)
                except json.JSONDecodeError as error:
                    raise PilotError("worker completion marker is invalid") from error
                if marker.get("commit") != policy["repository"]["commit"] or type(marker.get("exit_code")) is not int:
                    raise PilotError("worker completion marker identity is invalid")
                statuses.append({**item, "phase": "finished" if marker["exit_code"] == 0 else "failed",
                                 "exit_code": marker["exit_code"], "database_result_sha256": marker.get("database_sha256")})
        state["jobs"] = statuses
        state["phase"] = "workers-running" if any(x["phase"] == "running" for x in statuses) else ("workers-finished" if all(x["phase"] == "finished" for x in statuses) else "workers-failed")
        if state["phase"] != "workers-running":
            state["workers_finished_at"] = self.now().isoformat()
        self._save(state)
        return {"read_only": True, "phase": state["phase"], "jobs": [{k: v for k, v in item.items() if k != "directory"} for item in statuses]}

    def collect_workers(self, *, output_dir: Path) -> dict[str, Any]:
        state, policy = self._existing_context()
        if state.get("phase") not in {"workers-finished", "workers-failed"}:
            raise PilotError("collection requires both workers to finish")
        if output_dir.exists() and any(output_dir.iterdir()):
            raise PilotError("result output directory must be empty")
        output_dir.mkdir(parents=True, exist_ok=True)
        auth = _dict(policy.get("authorization"), "authorization")
        self._identity({"organization_id": auth["organization_id"], "project_id": auth["project_id"],
                        "cli_profile": policy["cli_profile"]})
        server_data = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        server_obj = server_data.get("server", server_data) if isinstance(server_data, dict) else None
        if not isinstance(server_obj, dict) or server_obj.get("id") != state.get("server_id"):
            raise PilotError("result server address response has unexpected shape")
        tags = server_obj.get("tags", [])
        if (server_obj.get("name") != state.get("name") or server_obj.get("project_id", server_obj.get("project")) != state.get("project_id")
                or not isinstance(tags, list) or "explicit-lean-simp-pilot" not in tags):
            raise PilotError("result server identity mismatch")
        address = self._state_pinned_public_ip(server_obj, state)["address"]
        machine = _dict(policy.get("machine"), "machine")
        self._require_known_host(address, machine)
        login = str(policy.get("login_user", "ubuntu"))
        remote_root = state.get("remote_job_directory")
        if remote_root != "/home/ubuntu/explicit-lean-simp-jobs":
            raise PilotError("saved remote jobs directory is invalid")
        output_dir.parent.mkdir(parents=True, exist_ok=True)
        size_command = ("set -eu; for j in job-000 job-001; do f=" + remote_root +
                        "/$j/result.tar.gz; test -f \"$f\"; printf '%s\\t%s\\n' \"$j\" \"$(stat -c %s \"$f\")\"; done")
        size_result = self._ssh(state, "sh", "-lc", shlex.quote(size_command), timeout=60)
        if size_result.returncode:
            raise PilotError("remote result archive sizing failed")
        remote_sizes: dict[str, int] = {}
        for line in size_result.stdout.splitlines():
            parts = line.split("\t")
            if len(parts) != 2 or parts[0] not in {"job-000", "job-001"} or parts[0] in remote_sizes or not parts[1].isdigit():
                raise PilotError("remote result archive sizes are malformed")
            remote_sizes[parts[0]] = int(parts[1])
        if set(remote_sizes) != {"job-000", "job-001"}:
            raise PilotError("remote result archive size list is incomplete")
        if any(size <= 0 or size > MAX_RESULT_ARCHIVE_BYTES for size in remote_sizes.values()) or sum(remote_sizes.values()) > MAX_TOTAL_ARCHIVE_BYTES:
            raise PilotError("remote result archive exceeds the configured compressed-size bound")
        free_before = shutil.disk_usage(output_dir.parent).free
        if free_before < sum(remote_sizes.values()) + MAX_TOTAL_EXTRACTED_BYTES + COLLECTION_DISK_RESERVE_BYTES:
            raise PilotError("insufficient local free disk for compressed results, bounded extraction, and reserve")
        file_hashes: dict[str, str] = {}
        job_results = []
        total_extracted = 0
        for spec in policy["jobs"]:
            job_id = spec["id"]
            out = output_dir / job_id
            out.mkdir()
            remote_tar = f"{login}@{address}:{remote_root}/{job_id}/result.tar.gz"
            local_tar = out / "result.tar.gz"
            proc = self._run(["scp", "-i", str(Path(machine["ssh_identity_file"]).expanduser()),
                              "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes",
                              "-o", f"UserKnownHostsFile={machine['known_hosts_file']}", remote_tar, str(local_tar)], 300)
            if proc.returncode:
                raise PilotError(f"{job_id} result transfer failed")
            actual_archive_size = local_tar.stat().st_size
            if actual_archive_size <= 0 or actual_archive_size > MAX_RESULT_ARCHIVE_BYTES or actual_archive_size != remote_sizes[job_id]:
                raise PilotError(f"{job_id} downloaded archive size differs from its bounded remote size")
            free_for_extract = shutil.disk_usage(output_dir.parent).free
            if free_for_extract < MAX_TOTAL_EXTRACTED_BYTES + COLLECTION_DISK_RESERVE_BYTES:
                raise PilotError("local free disk fell below the bounded extraction reserve")
            import tarfile
            extracted: list[Path] = []
            with tarfile.open(local_tar, "r:gz") as archive:
                members = archive.getmembers()
                names = {member.name for member in members}
                required = {"mathlib-db.sqlite3", "worker.log", "complete.json"}
                def allowed(member: Any) -> bool:
                    return (member.name in required or member.name == "artifacts" and member.isdir()
                            or member.name.startswith("artifacts/"))
                member_total = sum(member.size for member in members if member.isfile())
                if (len(members) > MAX_TAR_MEMBERS or member_total > MAX_TOTAL_EXTRACTED_BYTES
                        or any(member.size < 0 or member.size > MAX_TAR_MEMBER_BYTES for member in members)
                        or total_extracted + member_total > MAX_TOTAL_EXTRACTED_BYTES
                        or not required.issubset(names) or len(names) != len(members) or any(
                        Path(member.name).is_absolute() or ".." in Path(member.name).parts or not allowed(member)
                        for member in members)):
                    raise PilotError(f"{job_id} result archive has missing or unsafe entries")
                if shutil.disk_usage(output_dir.parent).free < member_total + COLLECTION_DISK_RESERVE_BYTES:
                    raise PilotError("local free disk is insufficient for declared result members and reserve")
                for member in members:
                    relative = Path(member.name)
                    if member.isdir():
                        (out / relative).mkdir(parents=True, exist_ok=True)
                    elif not member.isfile():
                        raise PilotError(f"{job_id} result archive contains a non-regular file")
                    else:
                        target = out / relative
                        target.parent.mkdir(parents=True, exist_ok=True)
                        source = archive.extractfile(member)
                        if source is None:
                            raise PilotError(f"{job_id} result entry could not be read")
                        written = 0
                        with source, target.open("wb") as destination:
                            while written < member.size:
                                chunk = source.read(min(1024 * 1024, member.size - written))
                                if not chunk:
                                    raise PilotError(f"{job_id} result entry ended before its declared size")
                                written += len(chunk)
                                total_extracted += len(chunk)
                                if total_extracted > MAX_TOTAL_EXTRACTED_BYTES:
                                    raise PilotError("result extraction exceeded the cumulative write bound")
                                if written % (64 * 1024**2) < len(chunk):
                                    remaining_member = member.size - written
                                    if shutil.disk_usage(output_dir.parent).free < remaining_member + COLLECTION_DISK_RESERVE_BYTES:
                                        raise PilotError("local free disk fell below the in-progress extraction reserve")
                                destination.write(chunk)
                        if written != member.size:
                            raise PilotError(f"{job_id} result entry size did not match its tar header")
                        extracted.append(target)
            marker = _read_json(out / "complete.json", f"{job_id} completion marker")
            repository = _dict(policy.get("repository"), "repository")
            if (marker.get("schema") != 1 or type(marker.get("exit_code")) is not int
                    or marker.get("commit") != repository.get("commit")
                    or marker.get("manifest_sha256") != spec.get("manifest_sha256")
                    or marker.get("database_sha256") != sha256_file(out / "mathlib-db.sqlite3")):
                raise PilotError(f"{job_id} completion marker or result hash is invalid")
            if marker["exit_code"] != next(item.get("exit_code") for item in state["jobs"] if item["id"] == job_id):
                raise PilotError(f"{job_id} completion marker exit does not match status")
            file_hashes.update({f"{job_id}/{path.relative_to(out)}": sha256_file(path) for path in extracted})
            job_results.append({"id": job_id, "exit_code": marker["exit_code"],
                                "database_sha256": sha256_file(out / "mathlib-db.sqlite3"),
                                "archive_sha256": sha256_file(local_tar),
                                "artifact_file_hashes": {str(path.relative_to(out)): sha256_file(path) for path in extracted}})
        state.update({"phase": "collected" if all(item["exit_code"] == 0 for item in job_results) else "collected-worker-failed",
                      "collected_at": self.now().isoformat(), "output_dir": str(output_dir.resolve()),
                      "jobs": [{**next(item for item in state["jobs"] if item["id"] == result["id"]),
                                "phase": "collected" if result["exit_code"] == 0 else "collected-failed",
                                "result_database_sha256": result["database_sha256"],
                                "result_archive_sha256": result["archive_sha256"]} for result in job_results],
                      "artifact_file_hashes": file_hashes})
        self._save(state)
        return state

    def supervise(self, *, job_root: Path, repo_root: Path, output_dir: Path,
                  poll_seconds: int = 60) -> dict[str, Any]:
        """Run, poll, collect and always attempt exact-resource cleanup."""
        if type(poll_seconds) is not int or not 5 <= poll_seconds <= 600:
            raise PilotError("poll interval must be between 5 and 600 seconds")
        started = time.monotonic()
        final: dict[str, Any] = {"supervisor": "started"}
        failure: str | None = None
        cleanup_allowed = False
        terminal: str | None = None
        dispatch_expired = False
        try:
            state = self._load_state()
            phase = state.get("phase")
            resumable = {"created", "bootstrap-started", "dispatching", "dispatch-failed",
                         "workers-running", "workers-finished", "workers-failed",
                         "collected", "collected-worker-failed"}
            if phase not in resumable:
                raise PilotError("supervisor state phase is not resumable; resources and remote data are untouched")
            if phase == "bootstrap-started" and not self._bootstrap_resume_is_safe(state):
                raise PilotError("bootstrap resume refused because worker dispatch evidence exists")
            cleanup_allowed = phase in {"created", "bootstrap-started"}
            if phase in {"created", "bootstrap-started"}:
                try:
                    state = self.run_workers(job_root=job_root, repo_root=repo_root)
                    phase = state.get("phase")
                except Exception as error:
                    state = self._load_state()
                    phase = state.get("phase")
                    if phase not in {"dispatching", "dispatch-failed"}:
                        raise
                    final["initial_dispatch_error"] = f"{type(error).__name__}: {error}"
                if phase in {"workers-running", "workers-finished", "workers-failed", "dispatching", "dispatch-failed"}:
                    cleanup_allowed = False
            if phase in {"dispatching", "dispatch-failed"}:
                policy, raw = self.policy()
                if state.get("policy_sha256") != sha256(raw):
                    raise PilotError("policy changed during partial worker dispatch")
                created_at = datetime.fromisoformat(state["created_at"]).astimezone(timezone.utc)
                hard_end = min(parse_utc(state["deadline"], "state.deadline"),
                               created_at + timedelta(seconds=int(state["lifetime_seconds"])))
                if self.now().astimezone(timezone.utc) >= hard_end:
                    failure = "ambiguous worker dispatch remained unresolved at the hard host deadline"
                    dispatch_expired = True
                    cleanup_allowed = True
                    state["unrecovered_dispatch_at"] = self.now().isoformat()
                    state["unrecovered_dispatch_reason"] = "supervisor resumed at or after the hard host deadline"
                    state["remote_results_may_be_lost_after_cleanup"] = True
                    self._save(state)
                else:
                    checked = validate_policy(policy, self.now())
                    server_data = self._scw(["instance", "server", "get", state["server_id"],
                                             f"zone={state['zone']}"], policy=checked)
                    server = server_data.get("server", server_data)
                    if not isinstance(server, dict):
                        raise PilotError("server details unavailable during dispatch recovery")
                    verified = self._verify_server_identity(server, checked, state)
                    if state.get("volume_ids") and verified["volume_ids"] != state["volume_ids"]:
                        raise PilotError("created boot volume identity changed during dispatch recovery")
                    state.update(verified)
                    remaining = min(checked["lifetime"] - (self.now().astimezone(timezone.utc) - created_at).total_seconds(),
                                    (checked["deadline"] - self.now().astimezone(timezone.utc)).total_seconds())
                    dispatch_budget = max(0, min(checked["runtime"] + 1800, int(remaining)))
                    while True:
                        try:
                            state = self._reconcile_dispatch(state, checked, checked)
                            phase = state.get("phase")
                            break
                        except Exception as error:
                            final["last_dispatch_error"] = f"{type(error).__name__}: {error}"
                            if time.monotonic() - started >= dispatch_budget:
                                failure = "ambiguous worker dispatch could not be resolved before the host/worker budget expired"
                                dispatch_expired = True
                                cleanup_allowed = True
                                checkpoint = self._load_state()
                                checkpoint["unrecovered_dispatch_at"] = self.now().isoformat()
                                checkpoint["unrecovered_dispatch_reason"] = final["last_dispatch_error"]
                                checkpoint["remote_results_may_be_lost_after_cleanup"] = True
                                self._save(checkpoint)
                                break
                            time.sleep(min(poll_seconds, max(1, dispatch_budget - (time.monotonic() - started))))
            if phase in {"workers-finished", "workers-failed"}:
                terminal = phase
            elif phase in {"collected", "collected-worker-failed"}:
                cleanup_allowed = True
                final["collection_already_validated"] = True
                if phase == "collected-worker-failed":
                    failure = "one or more jobs had failed; previously validated result bundles are retained"
            if dispatch_expired:
                budget = 0
            else:
                policy, _ = self.policy()
                checked = validate_policy(policy, self.now())
                created = datetime.fromisoformat(state["created_at"]).astimezone(timezone.utc)
                remaining = min(checked["lifetime"] - (self.now().astimezone(timezone.utc) - created).total_seconds(),
                                (checked["deadline"] - self.now().astimezone(timezone.utc)).total_seconds())
                budget = max(0, min(checked["runtime"] + 1800, int(remaining)))
            while terminal is None and not final.get("collection_already_validated") and not dispatch_expired:
                if phase not in {"created", "bootstrap-started", "dispatching", "dispatch-failed", "workers-running"}:
                    failure = "worker state is not eligible for polling or collection"
                    break
                try:
                    snapshot = self.poll_workers()
                    final["workers"] = snapshot
                    if snapshot["phase"] in {"workers-finished", "workers-failed"}:
                        terminal = snapshot["phase"]
                        break
                except Exception as error:
                    final["last_poll_error"] = f"{type(error).__name__}: {error}"
                if time.monotonic() - started >= budget:
                    failure = "supervisor worker/host time budget expired"
                    cleanup_allowed = True
                    break
                time.sleep(min(poll_seconds, max(1, budget - (time.monotonic() - started))))
            state = self._load_state()
            if terminal is not None:
                attempt = 0
                while True:
                    attempt += 1
                    staged_output = output_dir.with_name(output_dir.name + f".attempt-{attempt:02d}-{uuid.uuid4().hex[:8]}")
                    try:
                        final["collection"] = self.collect_workers(output_dir=staged_output)
                        if output_dir.exists() and any(output_dir.iterdir()):
                            raise PilotError("final result output directory is no longer empty")
                        if output_dir.exists():
                            output_dir.rmdir()
                        os.replace(staged_output, output_dir)
                        final["collection"]["output_dir"] = str(output_dir.resolve())
                        collected_state = self._load_state()
                        collected_state["output_dir"] = str(output_dir.resolve())
                        self._save(collected_state)
                        if collected_state.get("phase") == "collected-worker-failed":
                            failure = "one or more jobs exited unsuccessfully; both result bundles were collected"
                        cleanup_allowed = True
                        break
                    except Exception as error:
                        final["collection_attempts"] = attempt
                        final["last_collection_error"] = f"{type(error).__name__}: {error}"
                        checkpoint = self._load_state()
                        checkpoint["supervisor_collection_attempts"] = attempt
                        checkpoint["supervisor_last_collection_error"] = final["last_collection_error"]
                        checkpoint["supervisor_partial_collection_retained"] = False
                        self._save(checkpoint)
                        # Each tar contains a full database and artifacts. Keep
                        # disk use bounded across repeated SCP/validation errors.
                        if staged_output.exists():
                            if staged_output.is_symlink() or not staged_output.is_dir():
                                raise PilotError("failed collection staging path changed type; refusing to remove it")
                            shutil.rmtree(staged_output)
                        if time.monotonic() - started >= budget:
                            failure = "result collection did not validate before the host/deadline budget expired"
                            cleanup_allowed = True
                            break
                        time.sleep(min(poll_seconds, max(1, budget - (time.monotonic() - started))))
            elif not final.get("collection_already_validated"):
                final["supervisor_timeout"] = True
        except Exception as error:
            failure = f"{type(error).__name__}: {error}"
            if self.state_path.exists():
                try:
                    failed_phase = self._load_state().get("phase")
                    if failed_phase in {"workers-running", "workers-finished", "workers-failed",
                                        "dispatching", "dispatch-failed"}:
                        cleanup_allowed = False
                    elif failed_phase == "bootstrap-started":
                        cleanup_allowed = self._bootstrap_resume_is_safe(self._load_state())
                    elif failed_phase in {"created", "collected", "collected-worker-failed"}:
                        cleanup_allowed = True
                except Exception:
                    cleanup_allowed = False
        finally:
            if self.state_path.exists():
                try:
                    checkpoint = self._load_state()
                    checkpoint["supervisor_report"] = final
                    self._save(checkpoint)
                except Exception as error:
                    final["state_checkpoint_error"] = f"{type(error).__name__}: {error}"
            try:
                if cleanup_allowed and self.state_path.exists() and self._load_state().get("phase") != "deleted":
                    final["cleanup"] = self.cleanup(confirm=True)
            except Exception as error:
                final["cleanup_error"] = f"{type(error).__name__}: {error}"
        final["elapsed_seconds"] = int(time.monotonic() - started)
        if failure is not None:
            final["error"] = failure
        final["complete"] = failure is None and "cleanup_error" not in final and final.get("cleanup", {}).get("phase") == "deleted"
        return final

    def cleanup(self, *, confirm: bool = False) -> dict[str, Any]:
        if not confirm:
            raise PilotError("deletion requires --confirm-delete")
        state = self._load_state()
        if state.get("phase") == "deleted":
            return state
        policy, _ = self.policy()
        profile = policy.get("cli_profile")
        if type(profile) is not str or not profile.strip() or profile in {"default", "explicit-lean-cloud"}:
            raise PilotError("cleanup requires the dedicated Scaleway pilot profile")
        auth = _dict(policy.get("authorization"), "authorization")
        machine = _dict(policy.get("machine"), "machine")
        expected_type = machine.get("type")
        if type(expected_type) is not str or not expected_type:
            raise PilotError("cleanup policy lacks an exact machine.type")
        project_id, zone = auth["project_id"], auth["zone"]
        if (state.get("organization_id") != auth.get("organization_id") or state.get("project_id") != project_id
                or state.get("zone") != zone or not str(state.get("name", "")).startswith(NAME_PREFIX)):
            raise PilotError("saved pilot resource identity does not match cleanup policy")
        self._identity({"organization_id": auth["organization_id"], "project_id": project_id,
                        "cli_profile": policy["cli_profile"]})
        if not state.get("server_id"):
            listing = self._scw(["instance", "server", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
            servers = _list_response(listing, "servers", "ambiguous-create server listing")
            candidates = [server for server in servers if isinstance(server, dict)
                          and server.get("name") == state.get("name")
                          and isinstance(server.get("tags", []), list)
                          and "explicit-lean-simp-pilot" in server.get("tags", [])]
            if len(candidates) != 1:
                raise PilotError("ambiguous create remains unresolved; exact tagged server was not found uniquely; retain state and retry cleanup after provider visibility settles")
            candidate = candidates[0]
            candidate_id = candidate.get("id")
            if (type(candidate_id) is not str or not ID_RE.fullmatch(candidate_id)
                    or candidate.get("project_id", candidate.get("project")) != project_id
                    or candidate.get("zone") != zone
                    or candidate.get("commercial_type", candidate.get("type")) != expected_type):
                raise PilotError("ambiguous create candidate identity mismatch; refusing adoption/deletion")
            state.update({"server_id": candidate_id, "phase": "create-recovered"})
            self._save(state)
        visible = self._scw(["instance", "server", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
        visible_servers = _list_response(visible, "servers", "cleanup server listing")
        if not any(isinstance(item, dict) and item.get("id") == state["server_id"] for item in visible_servers):
            volumes = self._scw(["instance", "volume", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
            items = _list_response(volumes, "volumes", "cleanup volume listing")
            known_ids = set(state.get("attached_volume_ids", [])) | set(state.get("volume_ids", []))
            cleanup_root = _parse_root_volume(_dict(policy.get("requirements"), "requirements").get("root_volume"))
            lingering_instance_volumes = [item for item in items if isinstance(item, dict)
                and ((item.get("id") in known_ids and cleanup_root["kind"] != "sbs")
                     or ("explicit-lean-simp-pilot" in item.get("tags", [])
                         and not (cleanup_root["kind"] == "sbs" and item.get("id") in known_ids)))]
            if lingering_instance_volumes:
                raise PilotError("server is absent but tagged or previously attached storage remains")
            checked = {"project_id": project_id, "zone": zone,
                       "root_volume": cleanup_root}
            if checked["root_volume"]["kind"] == "sbs":
                sbs_ids = set(state.get("attached_volume_ids", state.get("volume_ids", [])))
                self._cleanup_sbs_volumes(checked, sbs_ids)
            ip_id = state.get("public_ip_id")
            if type(ip_id) is not str or not ID_RE.fullmatch(ip_id):
                raise PilotError("server is absent and the exact flexible IP ID is unknown; refusing to claim cleanup")
            ips = self._scw(["instance", "ip", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
            ip_items = _list_response(ips, "ips", "cleanup flexible-IP listing")
            if any(isinstance(item, dict) and item.get("id") == ip_id for item in ip_items):
                raise PilotError("server is absent but its flexible IP remains reserved")
            state.update({"phase": "deleted", "deleted_at": self.now().isoformat(),
                          "delete_response": "server, attached storage, and exact flexible IP verified absent"})
            self._save(state)
            return state
        current = self._scw(["instance", "server", "get", state["server_id"], f"zone={state['zone']}"], policy=policy)
        server = current.get("server", current) if isinstance(current, dict) else None
        if not isinstance(server, dict) or server.get("id") != state.get("server_id"):
            raise PilotError("server details unavailable; refusing deletion")
        if server.get("project") != project_id and server.get("project_id") != project_id:
            raise PilotError("server project identity mismatch; refusing deletion")
        server_tags = server.get("tags", [])
        if not isinstance(server_tags, list) or (server.get("name") != state["name"] or server.get("zone") != zone
                or server.get("commercial_type", server.get("type")) != expected_type
                or "explicit-lean-simp-pilot" not in server_tags):
            raise PilotError("server ownership tags mismatch; refusing deletion")
        public_ip = self._one_public_ip(server)
        if state.get("public_ip_id") is not None and state["public_ip_id"] != public_ip["id"]:
            raise PilotError("server flexible IP differs from the recorded resource")
        state["public_ip_id"] = public_ip["id"]
        state["public_ip_address"] = public_ip["address"]
        attached: set[str] = set(state.get("attached_volume_ids", []))
        attached.update(state.get("volume_ids", []))
        root_policy = _parse_root_volume(_dict(policy.get("requirements"), "requirements").get("root_volume"))
        cleanup_checked = {"project_id": project_id, "zone": zone, "root_volume": root_policy}
        if root_policy["kind"] == "sbs":
            root_attachment = self._server_root_attachment(server, cleanup_checked)
            if attached and attached != {root_attachment["id"]}:
                raise PilotError("saved SBS root volume ID differs from the server attachment")
            attached.add(root_attachment["id"])
            listed_sbs = self._list_sbs_volumes(cleanup_checked)
            if root_attachment["id"] not in {item.get("id", item.get("volume_id")) for item in listed_sbs}:
                raise PilotError("exact SBS root volume is not visible in block volume listing; retry cleanup")
            if any((NAME_PREFIX in str(item.get("name", ""))
                    or "explicit-lean-simp-pilot" in item.get("tags", []))
                   and item.get("id", item.get("volume_id")) != root_attachment["id"]
                   for item in listed_sbs):
                raise PilotError("unexpected tagged SBS storage exists; refusing broad cleanup")
            self._get_sbs_volume(root_attachment["id"], cleanup_checked,
                                 expected_server_id=state["server_id"])
        volumes_before = self._scw(["instance", "volume", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
        before_items = _list_response(volumes_before, "volumes", "pre-delete volume listing")
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
        servers = _list_response(listing, "servers", "post-delete server listing")
        if any(isinstance(s, dict) and s.get("id") == state["server_id"] for s in servers):
            raise PilotError("server deletion could not be confirmed")
        volumes = self._scw(["instance", "volume", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
        items = _list_response(volumes, "volumes", "post-delete volume listing")
        remaining_ids = {v.get("id") for v in items if isinstance(v, dict)}
        if any(isinstance(v, dict) and "explicit-lean-simp-pilot" in v.get("tags", []) for v in items) or attached.intersection(remaining_ids):
            raise PilotError("attached storage deletion could not be confirmed")
        if root_policy["kind"] == "sbs":
            self._cleanup_sbs_volumes(cleanup_checked, attached)
        ips_after = self._scw(["instance", "ip", "list", f"project-id={project_id}", f"zone={zone}"], policy=policy)
        ip_items_after = _list_response(ips_after, "ips", "post-delete flexible-IP listing")
        if any(isinstance(item, dict) and item.get("id") == state["public_ip_id"] for item in ip_items_after):
            raise PilotError("flexible IP deletion could not be confirmed")
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
    pf.add_argument("--repo", type=Path, required=True); pf.add_argument("--jobs", type=Path, required=True)
    launch = sub.add_parser("create", help="create the single authorized two-worker server")
    launch.add_argument("--repo", type=Path, required=True); launch.add_argument("--jobs", type=Path, required=True)
    launch.add_argument("--confirm-create", action="store_true")
    sub.add_parser("status", help="read provider status only")
    run = sub.add_parser("run-workers", help="bootstrap exact checkout, transfer two jobs and launch workers concurrently")
    run.add_argument("--repo", type=Path, required=True); run.add_argument("--jobs", type=Path, required=True)
    collect = sub.add_parser("collect-workers", help="download and verify both worker results")
    collect.add_argument("--output", type=Path, required=True)
    monitor = sub.add_parser("supervise", help="poll workers, collect results and delete resources automatically")
    monitor.add_argument("--repo", type=Path, required=True); monitor.add_argument("--jobs", type=Path, required=True)
    monitor.add_argument("--output", type=Path, required=True); monitor.add_argument("--poll-seconds", type=int, default=60)
    cleanup = sub.add_parser("cleanup", help="delete exact pilot server, attached volume and IP")
    cleanup.add_argument("--confirm-delete", action="store_true")
    args = parser.parse_args(argv)
    ctl = ScalewayPilot(policy_path=args.policy, state_path=args.state)
    try:
        if args.command == "plan": result = ctl.plan()
        elif args.command == "preflight": result = ctl.preflight(repo_root=args.repo, job_root=args.jobs)
        elif args.command == "create": result = ctl.create(repo_root=args.repo, job_root=args.jobs, confirm=args.confirm_create)
        elif args.command == "status": result = ctl.status()
        elif args.command == "run-workers": result = ctl.run_workers(job_root=args.jobs, repo_root=args.repo)
        elif args.command == "collect-workers": result = ctl.collect_workers(output_dir=args.output)
        elif args.command == "supervise":
            result = ctl.supervise(job_root=args.jobs, repo_root=args.repo, output_dir=args.output,
                                   poll_seconds=args.poll_seconds)
            if not result.get("complete"):
                print(json.dumps(result, sort_keys=True, indent=2, default=str))
                return 2
        else: result = ctl.cleanup(confirm=args.confirm_delete)
        print(json.dumps(result, sort_keys=True, indent=2, default=str))
        return 0
    except (PilotError, OSError, ValueError, KeyError) as error:
        print(f"scaleway pilot blocked: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
