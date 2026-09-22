#!/usr/bin/env python3
"""Mock-only contract tests for the two-worker Scaleway controller."""

from __future__ import annotations

from copy import deepcopy
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sqlite3
import tarfile
import tempfile
from types import SimpleNamespace
from typing import Any, Sequence

import scaleway_simp_replacements as pilot


NOW = datetime(2026, 9, 22, 12, 0, tzinfo=timezone.utc)
ORG = "11111111-1111-4111-8111-111111111111"
PROJECT = "22222222-2222-4222-8222-222222222222"
IMAGE = "33333333-3333-4333-8333-333333333333"
LOCAL_IMAGE = "33333333-3333-4333-8333-333333333334"
IP_ID = "33333333-3333-4333-8333-333333333335"
VOLUME_ID = "33333333-3333-4333-8333-333333333336"
SG = "44444444-4444-4444-8444-444444444444"
KEY = "55555555-5555-4555-8555-555555555555"
SERVER = "66666666-6666-4666-8666-666666666666"
COMMIT = "a" * 40


def blocked(function: Any) -> None:
    try:
        function()
    except pilot.PilotError:
        return
    raise AssertionError("expected fail-closed PilotError")


def setup(root: Path, *, machine_type: str = "GP1-L", minimum_memory_gib: int = 128,
          minimum_local_disk_gib: int = 200, root_volume: str = "local:559GB") -> tuple[Path, Path, Path, Path]:
    repo = root / "repo"; repo.mkdir()
    job_root = root / "jobs"; job_root.mkdir()
    baseline = root / "baseline.sqlite3"
    with sqlite3.connect(baseline) as con:
        con.execute("CREATE TABLE modules(name TEXT PRIMARY KEY)")
        con.execute("CREATE TABLE simp_replacements(module_name TEXT NOT NULL, ordinal INTEGER NOT NULL, status TEXT NOT NULL, PRIMARY KEY(module_name, ordinal))")
        for module in ("Mathlib.Algebra.Group.Basic", "Mathlib.Data.Bool.Basic"):
            con.execute("INSERT INTO modules VALUES (?)", (module,))
            con.execute("INSERT INTO simp_replacements VALUES (?, 0, 'pending')", (module,))
    baseline_bytes = baseline.read_bytes()
    jobs = []
    for index, module in enumerate(("Mathlib.Algebra.Group.Basic", "Mathlib.Data.Bool.Basic")):
        job = job_root / f"job-{index:03d}"; job.mkdir()
        manifest = job / "modules.txt"; database = job / "mathlib-db.sqlite3"
        manifest.write_text(module + "\n", encoding="utf-8")
        database.write_bytes(baseline_bytes)
        jobs.append({"id": f"job-{index:03d}", "directory": str(job.resolve()),
                     "manifest_sha256": pilot.sha256_file(manifest),
                     "database_sha256": pilot.sha256_file(database)})
    identity = root / "pilot_key"; identity.write_text("mock private key", encoding="utf-8"); identity.chmod(0o600)
    known_hosts = root / "pilot_known_hosts"; known_hosts.write_text("", encoding="utf-8")
    policy = {
        "schema": 1, "provider": "scaleway", "launch_authorized": True,
        "cli_profile": "test-dedicated-pilot", "login_user": "ubuntu",
        "authorization": {"organization_id": ORG, "project_id": PROJECT, "zone": "nl-ams-1",
            "not_after": "2026-09-22T18:00:00Z", "max_instance_lifetime_seconds": 6 * 3600,
            "max_worker_runtime_seconds": 5 * 3600, "max_cost_eur": "16.00",
            "estimated_all_in_cost_eur": "14.00", "cost_checked_at": "2026-09-22T12:00:00Z",
            "max_cost_usd": "20.00", "eur_usd_rate": "1.1463",
            "fx_checked_at": "2026-09-22T12:00:00Z", "fx_source": "ECB reference rate",
            "cost_source": "mock official pricing snapshot",
            "cost_components_eur": {"compute": "12.00", "public_ipv4": "1.00", "storage": "0.50", "egress_and_other": "0.50"}},
        "machine": {"type": machine_type, "image_id": IMAGE, "security_group_id": SG,
            "ssh_key_id": KEY, "ssh_identity_file": str(identity), "known_hosts_file": str(known_hosts),
            "ssh_source_cidr": "192.0.2.0/24"},
        "repository": {"url": pilot.CANONICAL_REPO, "commit": COMMIT}, "jobs": jobs,
        "requirements": {"single_host": True, "worker_count": 2, "linux_x86_64": True,
            "minimum_memory_gib": minimum_memory_gib, "minimum_local_disk_gib": minimum_local_disk_gib,
            "root_volume": root_volume, "public_ipv4": True},
    }
    policy_path = root / "policy.json"; policy_path.write_text(json.dumps(policy), encoding="utf-8")
    return repo, job_root, identity, policy_path


class Provider:
    """Scaleway 2.61-shaped responses; never invokes the real CLI."""
    def __init__(self, *, machine_type: str = "GP1-L", ram_gib: int = 128, arch: str = "x64",
                 volume_type: str = "l_ssd", volume_size_gb: int | None = 559,
                 volume_detail_size_gb: int | None = None,
                 volume_iops: int | None = None, volume_boot: bool = True,
                 image_type: str = "instance_local", server_volume_shape: str = "volumes",
                 attachment_iops: int | str | None = None,
                 public_ip_shape: str = "both") -> None:
        self.commands: list[tuple[str, ...]] = []
        self.external_commands: list[tuple[str, ...]] = []
        self.server: dict[str, Any] | None = None
        self.ips: list[dict[str, Any]] = []
        self.volume_items: list[dict[str, Any]] = []
        self.block_volumes: list[dict[str, Any]] = []
        self.fail_create_after_commit = False
        self.retain_ip_on_delete = False
        self.retain_sbs_volume_after_server_delete = False
        self.bad_server_shape: str | None = None
        self.wrong_account = False
        self.machine_type = machine_type
        self.ram_gib = ram_gib
        self.arch = arch
        self.volume_type = volume_type
        self.volume_size_gb = volume_size_gb
        self.volume_detail_size_gb = volume_detail_size_gb if volume_detail_size_gb is not None else volume_size_gb
        self.volume_iops = volume_iops
        self.volume_boot = volume_boot
        self.image_type = image_type
        self.server_volume_shape = server_volume_shape
        self.attachment_iops = attachment_iops
        self.public_ip_shape = public_ip_shape

    def __call__(self, command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
        del timeout
        args = tuple(command); self.commands.append(args)
        if args[:2] == ("git", "rev-parse"):
            return self.done(args, COMMIT + "\n")
        if args[:2] == ("git", "status"):
            return self.done(args)
        if args[:2] == ("git", "ls-remote"):
            return self.done(args, f"{COMMIT}\trefs/heads/main\n")
        if args[:2] == ("scw", "version"):
            return self.done(args, "Version 2.61.0\n")
        if args and args[0] == "ssh-keygen":
            known = Path(args[-1]).read_text()
            ok = len(args) > 2 and args[2] in known
            return subprocess.CompletedProcess(args, 0 if ok else 1, args[2] + "\n" if ok else "", "")
        if args and args[0] in {"ssh", "scp"}:
            self.external_commands.append(args)
            return self.done(args)
        if args[:3] != ("scw", "--output", "json"):
            raise AssertionError(f"unexpected command {args}")
        cmd = args[5:]
        if cmd[:3] == ("account", "project", "list"):
            org = "99999999-9999-4999-8999-999999999999" if self.wrong_account else ORG
            return self.json(args, [{"id": PROJECT, "organization_id": org}])
        if cmd[:3] == ("instance", "server", "list"):
            return self.json(args, [self.server] if self.server else [])
        if cmd[:3] == ("instance", "volume", "list"):
            return self.json(args, self.volume_items)
        if cmd[:3] == ("block", "volume", "list"):
            assert "project-id=" + PROJECT in cmd and "zone=nl-ams-1" in cmd
            return self.json(args, self.block_volumes)
        if cmd[:3] == ("instance", "ip", "list"):
            return self.json(args, self.ips)
        if cmd[:3] == ("instance", "server-type", "list"):
            assert "zone=nl-ams-1" in cmd
            return self.json(args, [{"name": self.machine_type, "availability": "available", "arch": self.arch,
                "ram": self.ram_gib * 1024**3}])
        if cmd[:3] == ("marketplace", "local-image", "list"):
            assert f"image-id={IMAGE}" in cmd
            return self.json(args, [{"id": LOCAL_IMAGE, "arch": "x86_64", "zone": "nl-ams-1",
                "label": "ubuntu_noble", "type": self.image_type, "compatible_commercial_types": [self.machine_type]}])
        if cmd[:3] == ("instance", "security-group", "get"):
            return self.json(args, {"id": SG, "project": PROJECT, "inbound_default_policy": "drop", "rules": None})
        if cmd[:3] == ("instance", "security-group", "list-rules"):
            return self.json(args, [{"direction": "inbound", "protocol": "TCP", "action": "accept",
                "dest_port_from": 22, "dest_port_to": None, "ip_range": "192.0.2.0/24"}])
        if cmd[:3] == ("iam", "ssh-key", "get"):
            return self.json(args, {"id": KEY, "project": PROJECT, "name": "mock",
                "public_key": "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIE7fixture"})
        if cmd[:3] == ("instance", "server", "create"):
            cloud = next(arg.split("=", 1)[1].removeprefix("@") for arg in cmd if arg.startswith("cloud-init=@"))
            assert "OnCalendar=" in Path(cloud).read_text()
            assert "tags.1=two-workers" in cmd
            volume_entry = {"id": VOLUME_ID,
                "size": self.volume_size_gb * 1_000_000_000 if self.volume_size_gb is not None else None,
                "volume_type": self.volume_type, "boot": self.volume_boot, "zone": "nl-ams-1"}
            if self.attachment_iops is not None:
                volume_entry["iops"] = self.attachment_iops
            if self.bad_server_shape == "root_attachment_size":
                volume_entry["size"] = 99 * 1_000_000_000
            if self.bad_server_shape == "root_attachment_type":
                volume_entry["volume_type"] = "l_ssd"
            if self.bad_server_shape == "root_attachment_iops":
                volume_entry["iops"] = "5K"
            server_volumes: Any = {"0": volume_entry} if self.server_volume_shape == "volumes" else [volume_entry]
            ip_record = {"id": IP_ID, "address": "198.51.100.4", "family": "inet", "state": "attached"}
            self.server = {"id": SERVER, "name": next(x.split("=", 1)[1] for x in cmd if x.startswith("name=")),
                "project": PROJECT, "zone": "nl-ams-1", "commercial_type": self.machine_type,
                "tags": ["explicit-lean-simp-pilot", "two-workers"],
                "image": {"id": LOCAL_IMAGE, "name": "Ubuntu 24.04 Noble Numbat", "arch": "x86_64", "zone": "nl-ams-1"},
                "security_group": {"id": SG, "name": "pilot"},
                "ssh_key_id": KEY,
                self.server_volume_shape: server_volumes}
            if self.public_ip_shape in {"both", "singular"}:
                self.server["public_ip"] = dict(ip_record)
            if self.public_ip_shape in {"both", "plural"}:
                self.server["public_ips"] = [dict(ip_record)]
            self.ips = [dict(ip_record, project=PROJECT, zone="nl-ams-1")]
            self.volume_items = [dict(volume_entry, server={"id": SERVER}, tags=[])]
            self.block_volumes = ([{"id": VOLUME_ID, "project_id": PROJECT, "zone": "nl-ams-1",
                "type": "sbs_15k" if self.volume_iops == 15000 else "sbs_5k",
                "size": self.volume_detail_size_gb * 1_000_000_000,
                "specs": {"perf_iops": self.volume_iops}, "server": {"id": SERVER}, "tags": []}]
                if self.image_type == "instance_sbs" else [])
            assert f"image={LOCAL_IMAGE}" in cmd
            if self.fail_create_after_commit:
                return subprocess.CompletedProcess(args, 124, "", "ambiguous timeout")
            return self.json(args, {"server": self.server})
        if cmd[:3] == ("instance", "server", "get"):
            observed = deepcopy(self.server)
            if observed is not None:
                volume_field = "Volumes" if "Volumes" in observed else "volumes"
                volume_collection = observed[volume_field]
                volume_entry = volume_collection[0] if isinstance(volume_collection, list) else volume_collection["0"]
            if observed is not None and self.bad_server_shape == "image":
                observed["image"]["id"] = IMAGE
            elif observed is not None and self.bad_server_shape == "server_type":
                observed["commercial_type"] = "GP1-S"
            elif observed is not None and self.bad_server_shape == "security_group":
                observed["security_group"]["id"] = IMAGE
            elif observed is not None and self.bad_server_shape == "ssh_key":
                observed["ssh_key_id"] = IMAGE
            elif observed is not None and self.bad_server_shape == "root_volume":
                volume_entry["size"] = 100
            elif observed is not None and self.bad_server_shape == "not_boot_volume":
                volume_entry["boot"] = False
            elif observed is not None and self.bad_server_shape == "root_attachment_type":
                volume_entry["volume_type"] = "l_ssd"
            elif observed is not None and self.bad_server_shape == "root_attachment_size":
                volume_entry["size"] = 99 * 1_000_000_000
            elif observed is not None and self.bad_server_shape == "root_attachment_iops":
                volume_entry["iops"] = "5K"
            elif observed is not None and self.bad_server_shape == "multiple_root_volumes":
                if isinstance(observed[volume_field], list):
                    observed[volume_field].append(dict(volume_entry, id=IMAGE))
                else:
                    observed[volume_field]["1"] = dict(volume_entry, id=IMAGE)
            elif observed is not None and self.bad_server_shape == "both_volume_fields":
                observed["volumes"] = {"0": volume_entry}
            elif observed is not None and self.bad_server_shape == "wrong_boot_volume_id":
                observed["boot_volume_id"] = IMAGE
            elif observed is not None and self.bad_server_shape == "dynamic_ip":
                if "public_ip" in observed:
                    observed["public_ip"]["dynamic"] = True
                if "public_ips" in observed:
                    observed["public_ips"][0]["dynamic"] = True
            elif observed is not None and self.bad_server_shape == "conflicting_ip_records":
                if "public_ips" in observed:
                    observed["public_ips"][0]["address"] = "198.51.100.99"
            return self.json(args, {"server": observed})
        if cmd[:3] == ("block", "volume", "get"):
            assert cmd[3] == VOLUME_ID and "zone=nl-ams-1" in cmd
            volume = {"id": VOLUME_ID, "project_id": PROJECT, "zone": "nl-ams-1",
                "size": self.volume_detail_size_gb * 1_000_000_000 if self.volume_detail_size_gb is not None else None,
                "type": "sbs_15k" if self.volume_iops == 15000 else "sbs_5k",
                "specs": {"perf_iops": self.volume_iops}}
            if self.bad_server_shape == "root_volume_type":
                volume["type"] = "sbs_5k"
            elif self.bad_server_shape == "root_volume_size":
                volume["size"] = 99 * 1_000_000_000
            elif self.bad_server_shape == "root_volume_iops":
                volume["specs"]["perf_iops"] = 5000
            elif self.bad_server_shape == "root_volume_project":
                volume["project_id"] = IMAGE
            elif self.bad_server_shape == "root_volume_zone":
                volume["zone"] = "fr-par-1"
            return self.json(args, {"volume": volume})
        if cmd[:3] == ("block", "volume", "delete"):
            volume_id = cmd[3]
            assert volume_id == VOLUME_ID and "zone=nl-ams-1" in cmd
            self.block_volumes = [item for item in self.block_volumes if item.get("id") != volume_id]
            return self.json(args, {})
        if cmd[:3] == ("instance", "volume", "get"):
            volume = {"id": VOLUME_ID,
                "size": self.volume_detail_size_gb * 1_000_000_000 if self.volume_detail_size_gb is not None else None,
                "volume_type": self.volume_type}
            if self.volume_iops is not None:
                volume["iops"] = self.volume_iops
            if self.bad_server_shape == "root_volume_type":
                volume["volume_type"] = "l_ssd"
            elif self.bad_server_shape == "root_volume_size":
                volume["size"] = 99 * 1_000_000_000
            elif self.bad_server_shape == "root_volume_iops":
                volume["iops"] = 5000
            return self.json(args, {"volume": volume})
        if cmd[:3] == ("instance", "server", "delete"):
            self.server = None
            if not self.retain_ip_on_delete:
                self.ips = []
            self.volume_items = []
            if not self.retain_sbs_volume_after_server_delete:
                self.block_volumes = []
            return self.json(args, {})
        raise AssertionError(f"unhandled provider command {cmd}")

    @staticmethod
    def done(args: Sequence[str], stdout: str = "") -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(args, 0, stdout, "")

    @staticmethod
    def json(args: Sequence[str], data: Any) -> subprocess.CompletedProcess[str]:
        return Provider.done(args, json.dumps(data))


def ctl(root: Path, policy: Path, provider: Provider, now: datetime = NOW) -> pilot.ScalewayPilot:
    return pilot.ScalewayPilot(policy_path=policy, state_path=root / "state.json", runner=provider,
                               now=lambda: now)


def test_policy_cost_deadline_worker_count_and_job_hashes_fail_closed() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); _, jobs, _, path = setup(root)
        policy = json.loads(path.read_text())
        for change in (
            lambda p: p.update(requirements={**p["requirements"], "worker_count": 1}),
            lambda p: p.update(jobs=p["jobs"][:1]),
            lambda p: p["authorization"].update(max_instance_lifetime_seconds=13 * 3600),
            lambda p: p["authorization"].update(estimated_all_in_cost_eur="16.01"),
            lambda p: p["authorization"].update(max_cost_eur="17.50"),
            lambda p: p["authorization"].update(max_cost_usd="20.01"),
            lambda p: p["authorization"].update(fx_checked_at="2026-09-20T12:00:00Z"),
        ):
            bad = deepcopy(policy); change(bad)
            blocked(lambda: pilot.validate_policy(bad, NOW))
        (jobs / "job-001" / "modules.txt").write_text("Mathlib.Other\n")
        blocked(lambda: pilot.validate_job_root(jobs, policy["jobs"]))


def test_machine_and_root_volume_policy_is_explicit_and_fail_closed() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); _, _, _, path = setup(root)
        base = json.loads(path.read_text())
        for mutate in (
            lambda p: p["requirements"].update(minimum_memory_gib=0),
            lambda p: p["requirements"].update(minimum_local_disk_gib="100"),
            lambda p: p["requirements"].update(root_volume="sbs:100GB:0"),
            lambda p: p["requirements"].update(root_volume="local:100GB"),
            lambda p: p["machine"].update(type=""),
        ):
            bad = deepcopy(base); mutate(bad)
            blocked(lambda: pilot.validate_policy(bad, NOW))
        below_binary_minimum = deepcopy(base)
        below_binary_minimum["requirements"].update(
            minimum_local_disk_gib=100, root_volume="sbs:100GB:15000")
        blocked(lambda: pilot.validate_policy(below_binary_minimum, NOW))


def test_pop2_sbs_fallback_checks_type_ram_image_and_exact_boot_volume() -> None:
    pop_type = "POP2-HM-16C-128G"
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        repo, jobs, _, path = setup(root, machine_type=pop_type, minimum_memory_gib=128,
                                    minimum_local_disk_gib=100, root_volume="sbs:120GB:15000")
        provider = Provider(machine_type=pop_type, ram_gib=128, volume_type="sbs_volume",
                            volume_size_gb=None, volume_detail_size_gb=120,
                            volume_iops=15000, volume_boot=False, image_type="instance_sbs")
        controller = ctl(root, path, provider)
        preflight = controller.preflight(repo_root=repo, job_root=jobs)
        assert preflight["machine"]["server_type"]["name"] == pop_type
        state = controller.create(repo_root=repo, job_root=jobs, confirm=True)
        assert state["volume_ids"] == [VOLUME_ID]
        create = next(command for command in provider.commands if command[5:8] == ("instance", "server", "create"))
        assert f"type={pop_type}" in create and "root-volume=sbs:120GB:15000" in create
        assert any(command[5:8] == ("block", "volume", "get") for command in provider.commands)

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root, machine_type=pop_type,
            minimum_memory_gib=128, minimum_local_disk_gib=100, root_volume="sbs:120GB:15000")
        blocked(lambda: ctl(root, path, Provider(machine_type=pop_type, ram_gib=127,
            volume_type="sbs_volume", volume_size_gb=None, volume_detail_size_gb=120,
            volume_iops=15000, volume_boot=False, image_type="instance_sbs"))
            .preflight(repo_root=repo, job_root=jobs))

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root, machine_type=pop_type,
            minimum_memory_gib=128, minimum_local_disk_gib=100, root_volume="sbs:120GB:15000")
        blocked(lambda: ctl(root, path, Provider(machine_type=pop_type, ram_gib=128, arch="arm64",
            volume_type="sbs_volume", volume_size_gb=None, volume_detail_size_gb=120,
            volume_iops=15000, volume_boot=False, image_type="instance_sbs"))
            .preflight(repo_root=repo, job_root=jobs))

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root, machine_type=pop_type,
            minimum_memory_gib=128, minimum_local_disk_gib=100, root_volume="sbs:120GB:15000")
        blocked(lambda: ctl(root, path, Provider(machine_type=pop_type, ram_gib=128,
            volume_type="sbs_volume", volume_size_gb=None, volume_detail_size_gb=120,
            volume_iops=15000, volume_boot=False, image_type="instance_local"))
            .preflight(repo_root=repo, job_root=jobs))

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root, machine_type=pop_type,
            minimum_memory_gib=128, minimum_local_disk_gib=100, root_volume="sbs:120GB:15000")
        provider = Provider(machine_type=pop_type, ram_gib=128, volume_type="sbs_volume",
            volume_size_gb=None, volume_detail_size_gb=120, volume_iops=15000,
            volume_boot=False, image_type="instance_sbs")
        provider.block_volumes = [{"id": VOLUME_ID, "project_id": PROJECT, "zone": "nl-ams-1",
            "name": "explicit-lean-simp-orphan", "tags": []}]
        blocked(lambda: ctl(root, path, provider).preflight(repo_root=repo, job_root=jobs))

    for bad_volume in ("root_attachment_type", "root_attachment_size", "root_attachment_iops",
                       "multiple_root_volumes", "both_volume_fields",
                       "root_volume_type", "root_volume_size", "root_volume_iops",
                       "root_volume_project", "root_volume_zone"):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); repo, jobs, _, path = setup(root, machine_type=pop_type,
                minimum_memory_gib=128, minimum_local_disk_gib=100, root_volume="sbs:120GB:15000")
            provider = Provider(machine_type=pop_type, ram_gib=128, volume_type="sbs_volume",
                                volume_size_gb=None, volume_detail_size_gb=120,
                                volume_iops=15000, volume_boot=False, image_type="instance_sbs",
                                server_volume_shape="Volumes" if bad_volume in {
                                    "root_attachment_iops", "multiple_root_volumes", "both_volume_fields"} else "volumes",
                                attachment_iops="15K" if bad_volume == "root_attachment_iops" else None)
            provider.bad_server_shape = bad_volume
            blocked(lambda: ctl(root, path, provider).create(repo_root=repo, job_root=jobs, confirm=True))

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root, machine_type=pop_type,
            minimum_memory_gib=128, minimum_local_disk_gib=100, root_volume="sbs:120GB:15000")
        provider = Provider(machine_type=pop_type, ram_gib=128, volume_type="sbs_15k",
            volume_size_gb=120, volume_detail_size_gb=120, volume_iops=15000,
            volume_boot=False, image_type="instance_sbs", server_volume_shape="Volumes",
            attachment_iops="15K")
        controller = ctl(root, path, provider)
        created = controller.create(repo_root=repo, job_root=jobs, confirm=True)
        assert created["volume_ids"] == [VOLUME_ID] and "Volumes" in provider.server
        provider.retain_sbs_volume_after_server_delete = True
        assert controller.cleanup(confirm=True)["phase"] == "deleted"


def test_read_only_preflight_uses_real_cli_response_shapes_and_two_hash_pins() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider()
        result = ctl(root, path, provider).preflight(repo_root=repo, job_root=jobs)
        assert result["read_only"] and result["worker_count"] == 2 and len(result["jobs"]) == 2
        assert result["machine"]["local_image_id"] == LOCAL_IMAGE
        assert any(command[5:8] == ("marketplace", "local-image", "list") for command in provider.commands)
        assert not any("create" in command or "delete" in command for command in provider.commands)
        provider.wrong_account = True
        blocked(lambda: ctl(root, path, provider).preflight(repo_root=repo, job_root=jobs))


def test_job_root_rejects_overlap_missing_pending_modules_and_hardlinks() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); _, jobs, _, policy_path = setup(root)
        policy = json.loads(policy_path.read_text())
        first = jobs / "job-000" / "modules.txt"
        second = jobs / "job-001" / "modules.txt"
        first.write_text("Mathlib.Algebra.Group.Basic\n", encoding="utf-8")
        second.write_text("Mathlib.Algebra.Group.Basic\n", encoding="utf-8")
        policy["jobs"][0]["manifest_sha256"] = pilot.sha256_file(first)
        policy["jobs"][1]["manifest_sha256"] = pilot.sha256_file(second)
        blocked(lambda: pilot.validate_job_root(jobs, policy["jobs"]))

        second.write_text("Mathlib.Data.Bool.Basic\n", encoding="utf-8")
        policy["jobs"][1]["manifest_sha256"] = pilot.sha256_file(second)
        database0 = jobs / "job-000" / "mathlib-db.sqlite3"
        database1 = jobs / "job-001" / "mathlib-db.sqlite3"
        database1.unlink(); database1.hardlink_to(database0)
        blocked(lambda: pilot.validate_job_root(jobs, policy["jobs"]))

        database1.unlink()
        with sqlite3.connect(database1) as con:
            con.execute("CREATE TABLE modules(name TEXT PRIMARY KEY)")
            con.execute("CREATE TABLE simp_replacements(module_name TEXT NOT NULL, ordinal INTEGER NOT NULL, status TEXT NOT NULL, PRIMARY KEY(module_name, ordinal))")
            con.execute("INSERT INTO modules VALUES ('Mathlib.Algebra.Group.Basic')")
            con.execute("INSERT INTO simp_replacements VALUES ('Mathlib.Algebra.Group.Basic', 0, 'pending')")
            con.execute("INSERT INTO modules VALUES ('Mathlib.Data.Bool.Basic')")
            con.execute("INSERT INTO simp_replacements VALUES ('Mathlib.Data.Bool.Basic', 0, 'success')")
        policy["jobs"][1]["database_sha256"] = pilot.sha256_file(database1)
        blocked(lambda: pilot.validate_job_root(jobs, policy["jobs"]))


def test_create_and_two_workers_launch_concurrently_with_remote_hash_check() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(public_ip_shape="plural")
        controller = ctl(root, path, provider)
        created = controller.create(repo_root=repo, job_root=jobs, confirm=True)
        assert created["phase"] == "created" and len(created["jobs"]) == 2
        assert created["public_ip_id"] == IP_ID and created["local_image_id"] == LOCAL_IMAGE
        assert created["volume_ids"] == [VOLUME_ID] and created["ssh_key_id"] == KEY
        (root / "pilot_known_hosts").write_text("198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")
        ssh_calls: list[tuple[str, ...]] = []
        remote_state: dict[str, tuple[str, str]] = {}
        def ssh_fake(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            del timeout
            ssh_calls.append(args)
            command = " ".join(args)
            job_id = "job-000" if "job-000" in command else "job-001" if "job-001" in command else ""
            if "NOT_LAUNCHED" in command:
                status, pid = remote_state.get(job_id, ("NOT_LAUNCHED", ""))
                output = f"RUNNING {pid}\n" if status == "RUNNING" else status + "\n"
            elif "nohup bash -lc" in command:
                remote_state[job_id] = ("RUNNING", "4310")
                output = "RUNNING 4310\n"
            else:
                output = ""
            return subprocess.CompletedProcess(args, 0, output, "")
        controller._ssh = ssh_fake  # type: ignore[method-assign]
        running = controller.run_workers(job_root=jobs, repo_root=repo)
        assert running["phase"] == "workers-running"
        uploads = [command for command in provider.external_commands if command[0] == "scp"]
        assert len(uploads) == 1 and "ubuntu@198.51.100.4:/home/ubuntu/explicit-lean-simp-jobs/" in uploads[0][-1]
        launches = [args for args in ssh_calls if "nohup bash -lc" in " ".join(args)]
        assert len(launches) == 2
        assert all("timeout --signal=TERM" in " ".join(args) for args in launches)
        assert all("EXPLICIT_LEAN_WORKER_TOKEN" in " ".join(args) and ".launch-claim/token" in " ".join(args)
                   for args in launches)
        status_checks = [" ".join(args) for args in ssh_calls if "NOT_LAUNCHED" in " ".join(args)]
        assert len(status_checks) == 2 and all("/proc/$p/environ" in command and "/proc/$p/cmdline" in command
                                               for command in status_checks)
        bootstrap = next(args[-1] for args in ssh_calls if "lake build ExplicitLean.SimpTrace" in " ".join(args))
        assert "apt-get install -y" in bootstrap and "zstd" in bootstrap
        assert "sudo install -d -o ubuntu -g ubuntu /opt/explicit-lean" in bootstrap
        assert "git clone --no-checkout https://github.com/Barraketh/explicit-lean.git /opt/explicit-lean/." in bootstrap
        assert "git -C /opt/explicit-lean fetch --no-tags origin" in bootstrap
        assert "lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw" in bootstrap
        assert "test -s .lake/build/lib/lean/ExplicitLean/SimpTrace.olean" in bootstrap
        assert "test -s .lake/build/lib/lean/ExplicitLean/ExplicitRw.olean" in bootstrap
        assert sum(command and command[0] == "scp" and "-r" in command for command in provider.commands) == 1
        assert any("UserKnownHostsFile=" in " ".join(command) for command in provider.commands if command and command[0] == "scp")
        state = json.loads((root / "state.json").read_text())
        assert [job["phase"] for job in state["jobs"]] == ["running", "running"]


def test_bootstrap_started_can_resume_only_before_any_worker_dispatch_evidence() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider()
        controller = ctl(root, path, provider)
        state = controller.create(repo_root=repo, job_root=jobs, confirm=True)
        state["phase"] = "bootstrap-started"
        state["bootstrap_started_at"] = NOW.isoformat()
        state["guest_poweroff_watchdog_armed"] = True
        state["host_ttl_remaining_seconds"] = 6 * 3600
        controller._save(state)
        (root / "pilot_known_hosts").write_text(
            "198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")
        ssh_calls: list[tuple[str, ...]] = []

        def ssh_fake(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            del timeout
            ssh_calls.append(args)
            command = " ".join(args)
            if "NOT_LAUNCHED" in command:
                return subprocess.CompletedProcess(args, 0, "NOT_LAUNCHED\n", "")
            if "nohup bash -lc" in command:
                return subprocess.CompletedProcess(args, 0, "RUNNING 4310\n", "")
            return subprocess.CompletedProcess(args, 0, "", "")

        controller._ssh = ssh_fake  # type: ignore[method-assign]
        resumed = controller.run_workers(job_root=jobs, repo_root=repo)
        assert resumed["phase"] == "workers-running"
        timer_checks = [" ".join(args) for args in ssh_calls if "NextElapseUSecMonotonic" in " ".join(args)]
        assert len(timer_checks) == 1 and "test \"$next\" -le" in timer_checks[0]
        assert not any("systemd-run" in args for args in ssh_calls)
        bootstrap = next(" ".join(args) for args in ssh_calls if "git clone --no-checkout" in " ".join(args))
        assert "sudo install -d -o ubuntu -g ubuntu /opt/explicit-lean" in bootstrap
        assert "git -C /opt/explicit-lean remote get-url origin" in bootstrap

    evidence_cases = [
        ("state", "worker_started_at"), ("state", "worker_timeout_seconds"),
        ("state", "dispatch_error"), ("job", "launch_token"), ("job", "pid"),
        ("job", "exit_code"), ("job", "database_result_sha256"),
        ("job", "result_database_sha256"), ("job", "result_archive_sha256"),
    ]
    for location, evidence in evidence_cases:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider()
            controller = ctl(root, path, provider)
            state = controller.create(repo_root=repo, job_root=jobs, confirm=True)
            state["phase"] = "bootstrap-started"
            state["bootstrap_started_at"] = NOW.isoformat()
            state["guest_poweroff_watchdog_armed"] = True
            state["host_ttl_remaining_seconds"] = 6 * 3600
            if location == "state":
                state[evidence] = "evidence"
            else:
                state["jobs"][0][evidence] = "worker evidence"
            controller._save(state)
            blocked(lambda: controller.run_workers(job_root=jobs, repo_root=repo))
            cleanup_calls: list[str] = []
            controller.cleanup = lambda *, confirm=False: (cleanup_calls.append("cleanup") or {"phase": "deleted"})  # type: ignore[method-assign]
            outcome = controller.supervise(job_root=jobs, repo_root=repo,
                output_dir=root / "results", poll_seconds=5)
            assert not outcome["complete"] and cleanup_calls == []

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider()
        controller = ctl(root, path, provider)
        state = controller.create(repo_root=repo, job_root=jobs, confirm=True)
        state.update({"phase": "bootstrap-started", "bootstrap_started_at": NOW.isoformat(),
                      "guest_poweroff_watchdog_armed": True, "host_ttl_remaining_seconds": 6 * 3600})
        controller._save(state)
        ssh_calls: list[tuple[str, ...]] = []

        def missing_watchdog(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            del timeout
            ssh_calls.append(args)
            return subprocess.CompletedProcess(args, 1 if "NextElapseUSecMonotonic" in " ".join(args) else 0, "", "")

        controller._ssh = missing_watchdog  # type: ignore[method-assign]
        blocked(lambda: controller.run_workers(job_root=jobs, repo_root=repo))
        assert len(ssh_calls) == 1 and "NextElapseUSecMonotonic" in " ".join(ssh_calls[0])


def test_failed_supervisor_bootstrap_state_can_resume_after_report_checkpoint() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider()
        controller = ctl(root, path, provider)
        controller.create(repo_root=repo, job_root=jobs, confirm=True)
        (root / "pilot_known_hosts").write_text(
            "198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")

        def fail_during_bootstrap(*, job_root: Path, repo_root: Path) -> dict[str, Any]:
            del job_root, repo_root
            state = controller._load_state()
            state.update({"phase": "bootstrap-started", "bootstrap_started_at": NOW.isoformat(),
                          "guest_poweroff_watchdog_armed": True, "host_ttl_remaining_seconds": 6 * 3600})
            controller._save(state)
            raise pilot.PilotError("simulated bootstrap failure")

        controller.run_workers = fail_during_bootstrap  # type: ignore[method-assign]
        controller.cleanup = lambda *, confirm=False: (_ for _ in ()).throw(
            pilot.PilotError("simulated cleanup refusal; retain host"))  # type: ignore[method-assign]
        first = controller.supervise(job_root=jobs, repo_root=repo, output_dir=root / "first", poll_seconds=5)
        assert not first["complete"] and first.get("cleanup_error")
        state = controller._load_state()
        assert state["phase"] == "bootstrap-started"
        assert state["supervisor_report"] == first
        legacy = dict(state, supervisor_report={"supervisor": "started"})
        assert pilot.ScalewayPilot._bootstrap_resume_is_safe(legacy)
        state["supervisor_report"] = {"supervisor": "started"}
        controller._save(state)
        del controller.run_workers

        ssh_calls: list[tuple[str, ...]] = []

        def ssh_fake(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            del timeout
            ssh_calls.append(args)
            command = " ".join(args)
            if "NOT_LAUNCHED" in command:
                return subprocess.CompletedProcess(args, 0, "NOT_LAUNCHED\n", "")
            if "nohup bash -lc" in command:
                return subprocess.CompletedProcess(args, 0, "RUNNING 4310\n", "")
            return subprocess.CompletedProcess(args, 0, "", "")

        controller._ssh = ssh_fake  # type: ignore[method-assign]

        def poll_finished() -> dict[str, Any]:
            current = controller._load_state(); current["phase"] = "workers-finished"; controller._save(current)
            return {"phase": "workers-finished", "jobs": []}

        def collect(*, output_dir: Path) -> dict[str, Any]:
            output_dir.mkdir(parents=True)
            current = controller._load_state(); current["phase"] = "collected"; controller._save(current)
            return current

        def cleanup(*, confirm: bool = False) -> dict[str, Any]:
            assert confirm
            current = controller._load_state(); current["phase"] = "deleted"; controller._save(current)
            return current

        controller.poll_workers = poll_finished  # type: ignore[method-assign]
        controller.collect_workers = collect  # type: ignore[method-assign]
        controller.cleanup = cleanup  # type: ignore[method-assign]
        resumed = controller.supervise(job_root=jobs, repo_root=repo, output_dir=root / "resumed", poll_seconds=5)
        assert resumed["complete"] and resumed["cleanup"]["phase"] == "deleted"
        assert any("NextElapseUSecMonotonic" in " ".join(args) for args in ssh_calls)
        assert any("git clone --no-checkout" in " ".join(args) for args in ssh_calls)


def test_ssh_accepts_plural_only_public_ip_and_rejects_state_or_record_mismatch() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root)
        provider = Provider(public_ip_shape="plural")
        controller = ctl(root, path, provider)
        state = controller.create(repo_root=repo, job_root=jobs, confirm=True)
        (root / "pilot_known_hosts").write_text(
            "198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")
        controller._ssh(state, "true", timeout=5)
        ssh_calls = [command for command in provider.external_commands if command[0] == "ssh"]
        assert len(ssh_calls) == 1 and "ubuntu@198.51.100.4" in ssh_calls[0]

        wrong_address = dict(state, public_ip_address="198.51.100.99")
        blocked(lambda: controller._ssh(wrong_address, "true", timeout=5))
        provider.bad_server_shape = "conflicting_ip_records"
        provider.public_ip_shape = "both"
        provider.server["public_ip"] = {"id": IP_ID, "address": "198.51.100.4", "family": "inet"}
        provider.server["public_ips"] = [{"id": IP_ID, "address": "198.51.100.4", "family": "inet"}]
        blocked(lambda: controller._ssh(state, "true", timeout=5))
        assert len([command for command in provider.external_commands if command[0] == "ssh"]) == 1


def test_created_server_image_group_key_root_volume_and_ip_must_match_policy() -> None:
    for mismatch in ("image", "server_type", "security_group", "ssh_key", "root_volume", "not_boot_volume",
                     "wrong_boot_volume_id", "dynamic_ip"):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider()
            provider.bad_server_shape = mismatch
            blocked(lambda: ctl(root, path, provider).create(repo_root=repo, job_root=jobs, confirm=True))
            assert provider.server is not None
            assert not any(command and command[0] in {"ssh", "scp"} for command in provider.commands)


def test_dispatch_reconciliation_is_idempotent_at_all_crash_points() -> None:
    cases = [
        # Crash after dispatching state is saved but before any launch.
        ({}, {}, 2, "workers-running"),
        # Remote job-000 started, but its local state update was lost.
        ({}, {"job-000": ("RUNNING", "4310")}, 1, "workers-running"),
        # Crash after the first per-job state save.
        ({"job-000": {"phase": "running", "pid": "4310"}},
         {"job-000": ("RUNNING", "4310")}, 1, "workers-running"),
        # Both remote starts and per-job saves landed; overall phase update did not.
        ({"job-000": {"phase": "running", "pid": "4310"},
          "job-001": {"phase": "running", "pid": "4311"}},
         {"job-000": ("RUNNING", "4310"), "job-001": ("RUNNING", "4311")}, 0, "workers-running"),
        # `dispatch-failed`: reconcile a live job and only start its untouched peer.
        ({}, {"job-000": ("RUNNING", "4310")}, 1, "workers-running"),
        # `dispatch-failed`: a completed first job is retained; start only peer.
        ({}, {"job-000": ("COMPLETE", json.dumps({"schema": 1, "exit_code": 0,
            "commit": COMMIT, "database_sha256": "a" * 64,
            "manifest_sha256": hashlib.sha256(b"Mathlib.Algebra.Group.Basic\n").hexdigest()}))},
         1, "workers-running"),
    ]
    for index, (local_jobs, remote_jobs, expected_launches, expected_phase) in enumerate(cases):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); repo, job_root, _, path = setup(root); provider = Provider()
            controller = ctl(root, path, provider)
            state = controller.create(repo_root=repo, job_root=job_root, confirm=True)
            policy, _ = controller.policy()
            checked = pilot.validate_policy(policy, NOW)
            state.update({"phase": "dispatch-failed" if index >= 4 else "dispatching",
                          "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
                          "worker_started_at": NOW.isoformat(), "worker_timeout_seconds": 36000,
                          "jobs": [{**item, **local_jobs.get(item["id"], {"phase": "starting"})}
                                   for item in state["jobs"]]})
            controller._save(state)
            launches: list[str] = []
            def ssh_fake(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
                del timeout
                command = " ".join(args)
                job_id = "job-000" if "job-000" in command else "job-001" if "job-001" in command else ""
                observed = remote_jobs.get(job_id)
                if "NOT_LAUNCHED" in command:
                    if observed is None:
                        output = "NOT_LAUNCHED\n"
                    elif observed[0] == "RUNNING":
                        output = f"RUNNING\t{observed[1]}\n"
                    else:
                        output = "COMPLETE\t" + observed[1] + "\n"
                elif "nohup bash -lc" in command:
                    launches.append(job_id)
                    remote_jobs[job_id] = ("RUNNING", str(4310 + len(launches)))
                    output = f"RUNNING {remote_jobs[job_id][1]}\n"
                else:
                    output = ""
                return subprocess.CompletedProcess(args, 0, output, "")
            controller._ssh = ssh_fake  # type: ignore[method-assign]
            resumed = controller._reconcile_dispatch(state, checked, checked)
            assert len(launches) == expected_launches, (index, launches)
            assert resumed["phase"] == expected_phase
            assert [item["phase"] for item in resumed["jobs"]].count("running") >= 1
            if index == 5:
                assert next(item for item in resumed["jobs"] if item["id"] == "job-000")["phase"] == "finished"

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, job_root, _, path = setup(root); provider = Provider()
        controller = ctl(root, path, provider); state = controller.create(repo_root=repo, job_root=job_root, confirm=True)
        policy, _ = controller.policy(); checked = pilot.validate_policy(policy, NOW)
        state.update({"phase": "dispatching", "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
                      "worker_started_at": NOW.isoformat(), "worker_timeout_seconds": 36000,
                      "jobs": [{**item, "phase": "starting"} for item in state["jobs"]]})
        controller._save(state); remote: dict[str, str] = {}; launched: list[str] = []
        def ambiguous_ssh(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            del timeout
            command = " ".join(args); job_id = "job-000" if "job-000" in command else "job-001"
            if "NOT_LAUNCHED" in command:
                return subprocess.CompletedProcess(args, 0, remote.get(job_id, "NOT_LAUNCHED") + "\n", "")
            if "nohup bash -lc" in command:
                launched.append(job_id); remote[job_id] = "RUNNING 4310"
                if job_id == "job-000" and launched.count(job_id) == 1:
                    return subprocess.CompletedProcess(args, 255, "", "connection reset")
                return subprocess.CompletedProcess(args, 0, "RUNNING 4311\n", "")
            return subprocess.CompletedProcess(args, 0, "", "")
        controller._ssh = ambiguous_ssh  # type: ignore[method-assign]
        blocked(lambda: controller._reconcile_dispatch(state, checked, checked))
        resumed = controller._reconcile_dispatch(controller._load_state(), checked, checked)
        assert launched.count("job-000") == 1 and launched.count("job-001") == 1
        assert resumed["phase"] == "workers-running"

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, job_root, _, path = setup(root); provider = Provider()
        controller = ctl(root, path, provider); state = controller.create(repo_root=repo, job_root=job_root, confirm=True)
        state.update({"phase": "dispatching", "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
                      "worker_started_at": NOW.isoformat(), "worker_timeout_seconds": 36000,
                      "jobs": [{**item, "phase": "starting"} for item in state["jobs"]]})
        controller._save(state); (root / "pilot_known_hosts").write_text(
            "198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")
        controller._ssh = lambda _state, *args, timeout: subprocess.CompletedProcess(args, 0,
            "RUNNING\t4310\n" if "NOT_LAUNCHED" in " ".join(args) else "", "")  # type: ignore[method-assign]
        actions: list[str] = []
        def poll_workers() -> dict[str, Any]:
            actions.append("poll")
            updated = controller._load_state(); updated["phase"] = "workers-finished"
            updated["jobs"] = [{**item, "phase": "finished", "exit_code": 0} for item in updated["jobs"]]
            controller._save(updated)
            return {"phase": "workers-finished", "jobs": updated["jobs"]}
        def collect_workers(*, output_dir: Path) -> dict[str, Any]:
            actions.append("collect"); output_dir.mkdir()
            updated = controller._load_state(); updated["phase"] = "collected"; controller._save(updated)
            return updated
        def cleanup(*, confirm: bool = False) -> dict[str, Any]:
            assert confirm and actions == ["poll", "collect"]
            actions.append("cleanup")
            return {"phase": "deleted"}
        controller.poll_workers = poll_workers  # type: ignore[method-assign]
        controller.collect_workers = collect_workers  # type: ignore[method-assign]
        controller.cleanup = cleanup  # type: ignore[method-assign]
        outcome = controller.supervise(job_root=job_root, repo_root=repo, output_dir=root / "results", poll_seconds=5)
        assert outcome["complete"] and actions == ["poll", "collect", "cleanup"]

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, job_root, _, path = setup(root); provider = Provider()
        controller = ctl(root, path, provider); state = controller.create(repo_root=repo, job_root=job_root, confirm=True)
        state.update({"phase": "dispatch-failed", "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
                      "worker_started_at": NOW.isoformat(), "worker_timeout_seconds": 36000,
                      "jobs": [{**item, "phase": "starting"} for item in state["jobs"]]})
        controller._save(state); attempts = 0; cleanup: list[str] = []
        def persistent_ambiguity(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            nonlocal attempts
            del timeout; attempts += 1
            return subprocess.CompletedProcess(args, 0, "AMBIGUOUS\n", "")
        controller._ssh = persistent_ambiguity  # type: ignore[method-assign]
        controller.cleanup = lambda *, confirm=False: (cleanup.append("cleanup") or {"phase": "deleted"})  # type: ignore[method-assign]
        old_monotonic, old_sleep = pilot.time.monotonic, pilot.time.sleep
        clock = [0.0]
        pilot.time.monotonic = lambda: clock[0]  # type: ignore[assignment]
        pilot.time.sleep = lambda _seconds: clock.__setitem__(0, clock[0] + 1_000_000)  # type: ignore[assignment]
        try:
            outcome = controller.supervise(job_root=job_root, repo_root=repo, output_dir=root / "expired", poll_seconds=5)
        finally:
            pilot.time.monotonic, pilot.time.sleep = old_monotonic, old_sleep  # type: ignore[assignment]
        assert not outcome["complete"] and "budget expired" in outcome["error"] and cleanup == ["cleanup"]
        assert attempts >= 2
        expired_state = controller._load_state()
        assert expired_state["remote_results_may_be_lost_after_cleanup"] is True
        assert expired_state["unrecovered_dispatch_reason"]

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, job_root, _, path = setup(root); provider = Provider()
        controller = ctl(root, path, provider); state = controller.create(repo_root=repo, job_root=job_root, confirm=True)
        reconcile_attempts = 0; launched: list[str] = []
        def interrupt_after_dispatch(*, job_root: Path, repo_root: Path) -> dict[str, Any]:
            del job_root, repo_root
            interrupted = controller._load_state()
            interrupted.update({"phase": "dispatch-failed", "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
                               "worker_started_at": NOW.isoformat(), "worker_timeout_seconds": 36000,
                               "jobs": [{**item, "phase": "starting"} for item in interrupted["jobs"]]})
            controller._save(interrupted)
            raise pilot.PilotError("simulated lost launch response")
        def transient_ssh(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            nonlocal reconcile_attempts
            command = " ".join(args); job_id = "job-000" if "job-000" in command else "job-001"
            if "NOT_LAUNCHED" in command:
                reconcile_attempts += 1
                if reconcile_attempts == 1:
                    return subprocess.CompletedProcess(args, 0, "AMBIGUOUS\n", "")
                if job_id == "job-000":
                    return subprocess.CompletedProcess(args, 0, "RUNNING\t4310\n", "")
                return subprocess.CompletedProcess(args, 0, "NOT_LAUNCHED\n", "")
            if "nohup bash -lc" in command:
                launched.append(job_id)
                return subprocess.CompletedProcess(args, 0, "RUNNING 4311\n", "")
            return subprocess.CompletedProcess(args, 0, "", "")
        controller._ssh = transient_ssh  # type: ignore[method-assign]
        controller.run_workers = interrupt_after_dispatch  # type: ignore[method-assign]
        actions: list[str] = []
        def poll_after_reconcile() -> dict[str, Any]:
            actions.append("poll")
            updated = controller._load_state(); updated["phase"] = "workers-finished"
            updated["jobs"] = [{**item, "phase": "finished", "exit_code": 0} for item in updated["jobs"]]
            controller._save(updated)
            return {"phase": "workers-finished", "jobs": updated["jobs"]}
        def collect_after_reconcile(*, output_dir: Path) -> dict[str, Any]:
            actions.append("collect"); output_dir.mkdir()
            updated = controller._load_state(); updated["phase"] = "collected"; controller._save(updated)
            return updated
        controller.poll_workers = poll_after_reconcile  # type: ignore[method-assign]
        controller.collect_workers = collect_after_reconcile  # type: ignore[method-assign]
        controller.cleanup = lambda *, confirm=False: (actions.append("cleanup") or {"phase": "deleted"})  # type: ignore[method-assign]
        old_sleep = pilot.time.sleep; pilot.time.sleep = lambda _seconds: None
        try:
            outcome = controller.supervise(job_root=job_root, repo_root=repo, output_dir=root / "recovered", poll_seconds=5)
        finally:
            pilot.time.sleep = old_sleep
        assert outcome["complete"] and reconcile_attempts >= 3
        assert launched == ["job-001"] and actions == ["poll", "collect", "cleanup"]


def test_collection_verifies_both_result_archives_and_hashes() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(); controller = ctl(root, path, provider)
        policy = json.loads(path.read_text())
        (root / "pilot_known_hosts").write_text("198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")
        source_archives: dict[str, Path] = {}
        download_commands: list[tuple[str, ...]] = []
        expected_hashes = {}
        for spec in policy["jobs"]:
            index = 0 if spec["id"] == "job-000" else 1
            db = f"updated-db-{index}".encode()
            marker = {"schema": 1, "exit_code": 0, "commit": COMMIT,
                      "database_sha256": hashlib.sha256(db).hexdigest(), "manifest_sha256": spec["manifest_sha256"]}
            items = {"mathlib-db.sqlite3": db, "worker.log": b"completed\n",
                     "complete.json": json.dumps(marker).encode(), "artifacts/report.json": b"{}"}
            archive_path = root / f"{spec['id']}.tar.gz"
            with tarfile.open(archive_path, "w:gz") as archive:
                for name, data in items.items():
                    leaf = root / (spec["id"] + "-" + name.replace("/", "-")); leaf.write_bytes(data)
                    archive.add(leaf, arcname=name)
            source_archives[spec["id"]] = archive_path
            expected_hashes[spec["id"]] = hashlib.sha256(db).hexdigest()
        provider.server = {"id": SERVER, "name": pilot.NAME_PREFIX + "mock", "project": PROJECT,
            "zone": "nl-ams-1", "commercial_type": "GP1-L", "tags": ["explicit-lean-simp-pilot"],
            "public_ips": [{"id": IP_ID, "address": "198.51.100.4", "family": "inet"}],
            "image": {"id": LOCAL_IMAGE}, "security_group": {"id": SG},
            "volumes": {"0": {"id": VOLUME_ID, "size": 559 * 1_000_000_000, "volume_type": "l_ssd"}}}
        original = provider
        def transfer(command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
            if command and command[0] == "scp":
                download_commands.append(tuple(command))
                source = next(k for k in source_archives if k in str(command[-2]))
                Path(command[-1]).write_bytes(source_archives[source].read_bytes())
                return subprocess.CompletedProcess(command, 0, "", "")
            return original(command, timeout)
        state = {"schema": 1, "phase": "workers-finished", "server_id": SERVER,
            "name": provider.server["name"], "zone": "nl-ams-1", "project_id": PROJECT,
            "public_ip_id": IP_ID, "public_ip_address": "198.51.100.4",
            "organization_id": ORG, "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
            "policy_sha256": pilot.sha256_file(path),
            "jobs": [{"id": spec["id"], "phase": "finished", "exit_code": 0} for spec in policy["jobs"]]}
        (root / "state.json").write_text(json.dumps(state))
        controller._ssh = lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0,
            f"job-000\t{source_archives['job-000'].stat().st_size}\n"
            f"job-001\t{source_archives['job-001'].stat().st_size}\n", "")  # type: ignore[method-assign]
        controller.runner = transfer
        output = root / "result"; got = controller.collect_workers(output_dir=output)
        assert got["phase"] == "collected" and len(got["artifact_file_hashes"]) == 8
        assert len(download_commands) == 2
        assert all("ubuntu@198.51.100.4:" in command[-2] for command in download_commands)
        for job_id, digest in expected_hashes.items():
            assert pilot.sha256_file(output / job_id / "mathlib-db.sqlite3") == digest


def collection_fixture(root: Path) -> tuple[pilot.ScalewayPilot, Provider, Path, dict[str, Any]]:
    repo, jobs, _, path = setup(root); provider = Provider()
    provider.server = {"id": SERVER, "name": pilot.NAME_PREFIX + "collection", "project": PROJECT,
        "zone": "nl-ams-1", "commercial_type": "GP1-L", "tags": ["explicit-lean-simp-pilot"],
        "public_ips": [{"id": IP_ID, "address": "198.51.100.4", "family": "inet"}],
        "image": {"id": LOCAL_IMAGE}, "security_group": {"id": SG},
        "volumes": {"0": {"id": VOLUME_ID, "size": 559 * 1_000_000_000, "volume_type": "l_ssd"}}}
    (root / "pilot_known_hosts").write_text("198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")
    policy = json.loads(path.read_text())
    state = {"schema": 1, "phase": "workers-finished", "server_id": SERVER,
        "name": provider.server["name"], "zone": "nl-ams-1", "project_id": PROJECT,
        "public_ip_id": IP_ID, "public_ip_address": "198.51.100.4",
        "organization_id": ORG, "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
        "policy_sha256": pilot.sha256_file(path),
        "jobs": [{"id": spec["id"], "phase": "finished", "exit_code": 0} for spec in policy["jobs"]]}
    (root / "state.json").write_text(json.dumps(state))
    return ctl(root, path, provider), provider, path, policy


def test_collection_rejects_oversized_remote_archives_and_low_free_space_before_scp() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); controller, provider, _, _ = collection_fixture(root)
        scp_calls: list[tuple[str, ...]] = []
        def runner(command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
            if command and command[0] == "scp":
                scp_calls.append(tuple(command))
            return provider(command, timeout)
        controller.runner = runner
        controller._ssh = lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0,
            f"job-000\t{pilot.MAX_RESULT_ARCHIVE_BYTES + 1}\njob-001\t100\n", "")  # type: ignore[method-assign]
        blocked(lambda: controller.collect_workers(output_dir=root / "too-large"))
        assert not scp_calls

        controller._ssh = lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0,
            "job-000\t100\njob-001\t100\n", "")  # type: ignore[method-assign]
        original_disk_usage = pilot.shutil.disk_usage
        pilot.shutil.disk_usage = lambda _path: SimpleNamespace(total=1024, used=900, free=124)  # type: ignore[assignment]
        try:
            blocked(lambda: controller.collect_workers(output_dir=root / "low-space"))
        finally:
            pilot.shutil.disk_usage = original_disk_usage  # type: ignore[assignment]
        assert not scp_calls


def test_collection_rejects_tar_expansion_bounds_before_extracting_any_entry() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); controller, provider, _, policy = collection_fixture(root)
        archives: dict[str, Path] = {}
        for spec in policy["jobs"]:
            marker = {"schema": 1, "exit_code": 0, "commit": COMMIT,
                      "database_sha256": "0" * 64, "manifest_sha256": spec["manifest_sha256"]}
            archive_path = root / f"{spec['id']}-bomb.tar.gz"
            with tarfile.open(archive_path, "w:gz") as archive:
                for name, data in (("mathlib-db.sqlite3", b"db"), ("worker.log", b"log"),
                                   ("complete.json", json.dumps(marker).encode()),
                                   ("artifacts/bomb.bin", b"x" * 11)):
                    leaf = root / (spec["id"] + "-" + name.replace("/", "-"))
                    leaf.write_bytes(data); archive.add(leaf, arcname=name)
            archives[spec["id"]] = archive_path
        def runner(command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
            if command and command[0] == "scp":
                job_id = next(key for key in archives if key in str(command[-2]))
                Path(command[-1]).write_bytes(archives[job_id].read_bytes())
                return subprocess.CompletedProcess(command, 0, "", "")
            return provider(command, timeout)
        controller.runner = runner
        controller._ssh = lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0,
            f"job-000\t{archives['job-000'].stat().st_size}\n"
            f"job-001\t{archives['job-001'].stat().st_size}\n", "")  # type: ignore[method-assign]
        old_limit = pilot.MAX_TAR_MEMBER_BYTES; pilot.MAX_TAR_MEMBER_BYTES = 10
        output = root / "tar-bomb"
        try:
            blocked(lambda: controller.collect_workers(output_dir=output))
        finally:
            pilot.MAX_TAR_MEMBER_BYTES = old_limit
        assert not (output / "job-000" / "mathlib-db.sqlite3").exists()


def test_status_marker_parsing_and_cleanup_idempotence() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); _, jobs, _, path = setup(root); provider = Provider(); controller = ctl(root, path, provider)
        created = controller.create(repo_root=root / "repo", job_root=jobs, confirm=True)
        state = {**created, "phase": "workers-running", "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
                 "jobs": [{"id": "job-000", "phase": "running"}, {"id": "job-001", "phase": "running"}]}
        (root / "state.json").write_text(json.dumps(state))
        markers = {"job-000": json.dumps({"commit": COMMIT, "exit_code": 0, "database_sha256": "b" * 64}),
                   "job-001": json.dumps({"commit": COMMIT, "exit_code": 2, "database_sha256": "c" * 64})}
        controller._ssh = lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0,
            "\n".join(f"{key}\t{value}" for key, value in markers.items()), "")  # type: ignore[method-assign]
        snapshot = controller.poll_workers()
        assert snapshot["phase"] == "workers-failed"
        deleted = controller.cleanup(confirm=True)
        assert deleted["phase"] == "deleted" and provider.server is None and provider.ips == []
        assert deleted["public_ip_id"] == IP_ID
        assert any(command[5:8] == ("instance", "ip", "list") for command in provider.commands)
        assert controller.cleanup(confirm=True)["phase"] == "deleted"

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(); controller = ctl(root, path, provider)
        created = controller.create(repo_root=repo, job_root=jobs, confirm=True)
        state = {**created, "phase": "workers-finished"}; (root / "state.json").write_text(json.dumps(state))
        provider.server = None; provider.volume_items = []
        blocked(lambda: controller.cleanup(confirm=True))
        assert json.loads((root / "state.json").read_text())["phase"] != "deleted"
        provider.ips = []
        assert controller.cleanup(confirm=True)["phase"] == "deleted"

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(); provider.retain_ip_on_delete = True
        controller = ctl(root, path, provider); controller.create(repo_root=repo, job_root=jobs, confirm=True)
        blocked(lambda: controller.cleanup(confirm=True))
        assert provider.server is None and provider.ips and controller._load_state()["phase"] != "deleted"


def test_sbs_cleanup_lists_and_removes_exact_block_volume() -> None:
    pop_type = "POP2-HM-16C-128G"

    def make_sbs(root: Path) -> tuple[pilot.ScalewayPilot, Provider]:
        repo, jobs, _, path = setup(root, machine_type=pop_type, minimum_memory_gib=128,
            minimum_local_disk_gib=100, root_volume="sbs:120GB:15000")
        provider = Provider(machine_type=pop_type, ram_gib=128, volume_type="sbs_volume",
            volume_size_gb=None, volume_detail_size_gb=120, volume_iops=15000,
            volume_boot=False, image_type="instance_sbs")
        controller = ctl(root, path, provider)
        controller.create(repo_root=repo, job_root=jobs, confirm=True)
        return controller, provider

    with tempfile.TemporaryDirectory() as temp:
        controller, provider = make_sbs(Path(temp))
        provider.retain_sbs_volume_after_server_delete = True
        deleted = controller.cleanup(confirm=True)
        assert deleted["phase"] == "deleted" and provider.server is None and provider.block_volumes == []
        assert deleted["attached_volume_ids"] == [VOLUME_ID]
        assert sum(command[5:8] == ("block", "volume", "list") for command in provider.commands) >= 2
        assert any(command[5:8] == ("block", "volume", "delete") and command[8] == VOLUME_ID
                   for command in provider.commands)

    with tempfile.TemporaryDirectory() as temp:
        controller, provider = make_sbs(Path(temp))
        provider.server = None; provider.volume_items = []; provider.ips = []
        deleted = controller.cleanup(confirm=True)
        assert deleted["phase"] == "deleted" and provider.block_volumes == []
        assert any(command[5:8] == ("block", "volume", "delete") and command[8] == VOLUME_ID
                   for command in provider.commands)

    with tempfile.TemporaryDirectory() as temp:
        controller, provider = make_sbs(Path(temp))
        provider.server = None; provider.volume_items = []; provider.ips = []
        provider.block_volumes.append({"id": IMAGE, "project_id": PROJECT, "zone": "nl-ams-1",
            "name": "explicit-lean-simp-unexpected", "tags": ["explicit-lean-simp-pilot"]})
        blocked(lambda: controller.cleanup(confirm=True))
        assert any(item["id"] == IMAGE for item in provider.block_volumes)


def test_ambiguous_create_never_retries_and_policy_default_is_disabled() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(); provider.fail_create_after_commit = True
        blocked(lambda: ctl(root, path, provider).create(repo_root=repo, job_root=jobs, confirm=True))
        assert json.loads((root / "state.json").read_text())["phase"] == "create-requested"
        assert sum("server" in command and "create" in command for command in provider.commands) == 1
    default = pilot._read_json(pilot.POLICY_PATH, "policy")
    assert default["launch_authorized"] is False
    assert pilot.ScalewayPilot(policy_path=pilot.POLICY_PATH, state_path=Path("/tmp/no-state.json")).plan()["mutation_count"] == 0


def test_supervisor_collects_and_cleans_even_when_dispatch_fails() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(); controller = ctl(root, path, provider)
        controller.create(repo_root=repo, job_root=jobs, confirm=True)
        actions: list[str] = []
        def run_workers(*, job_root: Path, repo_root: Path) -> dict[str, Any]:
            del job_root, repo_root
            actions.append("dispatch")
            state = controller._load_state(); state["phase"] = "workers-running"; controller._save(state)
            return state
        def poll_workers() -> dict[str, Any]:
            actions.append("poll")
            state = controller._load_state(); state["phase"] = "workers-finished"; controller._save(state)
            return {"phase": "workers-finished", "jobs": []}
        attempts = 0
        def collect_workers(*, output_dir: Path) -> dict[str, Any]:
            nonlocal attempts
            attempts += 1
            actions.append("collect")
            if attempts == 1:
                output_dir.mkdir()
                (output_dir / "partial-db").write_bytes(b"partial")
                raise pilot.PilotError("simulated transient SCP failure")
            output_dir.mkdir()
            state = controller._load_state(); state["phase"] = "collected"; controller._save(state)
            return state
        def cleanup(*, confirm: bool = False) -> dict[str, Any]:
            assert confirm
            actions.append("cleanup")
            state = controller._load_state(); state["phase"] = "deleted"; controller._save(state)
            return state
        controller.run_workers = run_workers  # type: ignore[method-assign]
        controller.poll_workers = poll_workers  # type: ignore[method-assign]
        controller.collect_workers = collect_workers  # type: ignore[method-assign]
        controller.cleanup = cleanup  # type: ignore[method-assign]
        old_sleep = pilot.time.sleep; pilot.time.sleep = lambda _seconds: None
        try:
            result = controller.supervise(job_root=jobs, repo_root=repo, output_dir=root / "collected", poll_seconds=5)
        finally:
            pilot.time.sleep = old_sleep
        assert result["complete"] and result["collection_attempts"] == 1
        assert actions == ["dispatch", "poll", "collect", "collect", "cleanup"]
        assert not list(root.glob("collected.attempt-*"))

        second = ctl(root, path, provider)
        failed: list[str] = []
        second.run_workers = lambda **_kwargs: (_ for _ in ()).throw(pilot.PilotError("simulated dispatch failure"))  # type: ignore[method-assign]
        second.cleanup = lambda *, confirm=False: (failed.append("cleanup") or {"phase": "deleted"})  # type: ignore[method-assign]
        state = second._load_state(); state["phase"] = "created"; second._save(state)
        outcome = second.supervise(job_root=jobs, repo_root=repo, output_dir=root / "failure", poll_seconds=5)
        assert not outcome["complete"] and outcome["error"] and failed == ["cleanup"]


def test_supervisor_resumes_terminal_workers_before_cleanup_and_rejects_unknown_phase_safely() -> None:
    for terminal_phase in ("workers-finished", "workers-failed"):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(); controller = ctl(root, path, provider)
            controller.create(repo_root=repo, job_root=jobs, confirm=True)
            state = controller._load_state(); state["phase"] = terminal_phase; controller._save(state)
            events: list[str] = []
            controller.run_workers = lambda **_kwargs: (_ for _ in ()).throw(AssertionError("workers relaunched"))  # type: ignore[method-assign]
            controller.poll_workers = lambda: (_ for _ in ()).throw(AssertionError("terminal workers repolled"))  # type: ignore[method-assign]
            def collect(*, output_dir: Path) -> dict[str, Any]:
                events.append("collect")
                output_dir.mkdir()
                state = controller._load_state(); state["phase"] = "collected" if terminal_phase == "workers-finished" else "collected-worker-failed"
                controller._save(state)
                return state
            def cleanup(*, confirm: bool = False) -> dict[str, Any]:
                assert confirm and events == ["collect"]
                events.append("cleanup")
                return {"phase": "deleted"}
            controller.collect_workers = collect  # type: ignore[method-assign]
            controller.cleanup = cleanup  # type: ignore[method-assign]
            outcome = controller.supervise(job_root=jobs, repo_root=repo, output_dir=root / "results", poll_seconds=5)
            assert events == ["collect", "cleanup"]
            assert outcome["cleanup"]["phase"] == "deleted"
            assert outcome["complete"] is (terminal_phase == "workers-finished")

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(); controller = ctl(root, path, provider)
        controller.create(repo_root=repo, job_root=jobs, confirm=True)
        state = controller._load_state(); state["phase"] = "unknown"; controller._save(state)
        called: list[str] = []
        controller.cleanup = lambda **_kwargs: (called.append("cleanup") or {"phase": "deleted"})  # type: ignore[method-assign]
        result = controller.supervise(job_root=jobs, repo_root=repo, output_dir=root / "results", poll_seconds=5)
        assert not result["complete"] and called == [] and provider.server is not None

    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider()
        later = NOW + timedelta(hours=7)
        controller = ctl(root, path, provider, now=later)
        created = ctl(root, path, provider).create(repo_root=repo, job_root=jobs, confirm=True)
        created["phase"] = "workers-finished"; (root / "state.json").write_text(json.dumps(created))
        called: list[str] = []
        controller.cleanup = lambda **_kwargs: (called.append("cleanup") or {"phase": "deleted"})  # type: ignore[method-assign]
        outcome = controller.supervise(job_root=jobs, repo_root=repo, output_dir=root / "results", poll_seconds=5)
        assert not outcome["complete"] and called == [] and provider.server is not None


def main() -> None:
    tests = [test_policy_cost_deadline_worker_count_and_job_hashes_fail_closed,
             test_machine_and_root_volume_policy_is_explicit_and_fail_closed,
             test_pop2_sbs_fallback_checks_type_ram_image_and_exact_boot_volume,
             test_read_only_preflight_uses_real_cli_response_shapes_and_two_hash_pins,
             test_job_root_rejects_overlap_missing_pending_modules_and_hardlinks,
             test_create_and_two_workers_launch_concurrently_with_remote_hash_check,
             test_bootstrap_started_can_resume_only_before_any_worker_dispatch_evidence,
             test_failed_supervisor_bootstrap_state_can_resume_after_report_checkpoint,
             test_ssh_accepts_plural_only_public_ip_and_rejects_state_or_record_mismatch,
             test_created_server_image_group_key_root_volume_and_ip_must_match_policy,
             test_dispatch_reconciliation_is_idempotent_at_all_crash_points,
             test_collection_verifies_both_result_archives_and_hashes,
             test_collection_rejects_oversized_remote_archives_and_low_free_space_before_scp,
             test_collection_rejects_tar_expansion_bounds_before_extracting_any_entry,
             test_status_marker_parsing_and_cleanup_idempotence,
             test_sbs_cleanup_lists_and_removes_exact_block_volume,
             test_ambiguous_create_never_retries_and_policy_default_is_disabled,
             test_supervisor_collects_and_cleans_even_when_dispatch_fails,
             test_supervisor_resumes_terminal_workers_before_cleanup_and_rejects_unknown_phase_safely]
    for test in tests:
        test()
    print(f"{len(tests)} Scaleway full-run mock checks passed")


if __name__ == "__main__":
    main()
