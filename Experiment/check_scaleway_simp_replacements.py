#!/usr/bin/env python3
"""Mock-only contract tests for the two-worker Scaleway controller."""

from __future__ import annotations

from copy import deepcopy
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
from typing import Any, Sequence

import scaleway_simp_replacements as pilot


NOW = datetime(2026, 9, 22, 12, 0, tzinfo=timezone.utc)
ORG = "11111111-1111-4111-8111-111111111111"
PROJECT = "22222222-2222-4222-8222-222222222222"
IMAGE = "33333333-3333-4333-8333-333333333333"
LOCAL_IMAGE = "33333333-3333-4333-8333-333333333334"
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


def setup(root: Path) -> tuple[Path, Path, Path, Path]:
    repo = root / "repo"; repo.mkdir()
    job_root = root / "jobs"; job_root.mkdir()
    jobs = []
    for index, module in enumerate(("Mathlib.Algebra.Group.Basic", "Mathlib.Data.Bool.Basic")):
        job = job_root / f"job-{index:03d}"; job.mkdir()
        manifest = job / "modules.txt"; database = job / "mathlib-db.sqlite3"
        manifest.write_text(module + "\n", encoding="utf-8")
        database.write_bytes(f"sqlite-fixture-{index}".encode())
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
        "machine": {"type": "GP1-L", "image_id": IMAGE, "security_group_id": SG,
            "ssh_key_id": KEY, "ssh_identity_file": str(identity), "known_hosts_file": str(known_hosts),
            "ssh_source_cidr": "192.0.2.0/24"},
        "repository": {"url": pilot.CANONICAL_REPO, "commit": COMMIT}, "jobs": jobs,
        "requirements": {"single_host": True, "worker_count": 2, "linux_x86_64": True,
            "minimum_memory_gib": 128, "minimum_local_disk_gib": 200,
            "root_volume": "local:559GB", "public_ipv4": True},
    }
    policy_path = root / "policy.json"; policy_path.write_text(json.dumps(policy), encoding="utf-8")
    return repo, job_root, identity, policy_path


class Provider:
    """Scaleway 2.61-shaped responses; never invokes the real CLI."""
    def __init__(self) -> None:
        self.commands: list[tuple[str, ...]] = []
        self.server: dict[str, Any] | None = None
        self.fail_create_after_commit = False
        self.wrong_account = False

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
            return self.json(args, [])
        if cmd[:3] == ("instance", "server-type", "get"):
            assert "zone=nl-ams-1" in cmd
            return self.json(args, {"servers": {"GP1-L": {"availability": "available"}}})
        if cmd[:3] == ("marketplace", "local-image", "list"):
            assert f"image-id={IMAGE}" in cmd
            return self.json(args, [{"id": LOCAL_IMAGE, "arch": "x86_64", "zone": "nl-ams-1",
                "label": "ubuntu_noble", "type": "instance_local", "compatible_commercial_types": ["GP1-L"]}])
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
            self.server = {"id": SERVER, "name": next(x.split("=", 1)[1] for x in cmd if x.startswith("name=")),
                "project_id": PROJECT, "zone": "nl-ams-1", "commercial_type": "GP1-L",
                "tags": ["explicit-lean-simp-pilot", "two-workers"],
                "public_ip": {"address": "198.51.100.4"}}
            assert f"image={LOCAL_IMAGE}" in cmd
            if self.fail_create_after_commit:
                return subprocess.CompletedProcess(args, 124, "", "ambiguous timeout")
            return self.json(args, {"server": self.server})
        if cmd[:3] == ("instance", "server", "get"):
            return self.json(args, {"server": self.server})
        if cmd[:3] == ("instance", "server", "delete"):
            self.server = None
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


def test_create_and_two_workers_launch_concurrently_with_remote_hash_check() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider()
        controller = ctl(root, path, provider)
        created = controller.create(repo_root=repo, job_root=jobs, confirm=True)
        assert created["phase"] == "created" and len(created["jobs"]) == 2
        (root / "pilot_known_hosts").write_text("198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")
        ssh_calls: list[tuple[str, ...]] = []
        def ssh_fake(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            del timeout
            ssh_calls.append(args)
            output = "4310\n" if "worker.pid" in " ".join(args) else ""
            return subprocess.CompletedProcess(args, 0, output, "")
        controller._ssh = ssh_fake  # type: ignore[method-assign]
        running = controller.run_workers(job_root=jobs, repo_root=repo)
        assert running["phase"] == "workers-running"
        launches = [args for args in ssh_calls if "nohup bash -lc" in " ".join(args)]
        assert len(launches) == 2
        assert all("timeout --signal=TERM" in " ".join(args) for args in launches)
        assert sum(command and command[0] == "scp" and "-r" in command for command in provider.commands) == 1
        assert any("UserKnownHostsFile=" in " ".join(command) for command in provider.commands if command and command[0] == "scp")
        state = json.loads((root / "state.json").read_text())
        assert [job["phase"] for job in state["jobs"]] == ["running", "running"]


def test_collection_verifies_both_result_archives_and_hashes() -> None:
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp); repo, jobs, _, path = setup(root); provider = Provider(); controller = ctl(root, path, provider)
        policy = json.loads(path.read_text())
        (root / "pilot_known_hosts").write_text("198.51.100.4 ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIverified\n")
        source_archives: dict[str, Path] = {}
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
        provider.server = {"id": SERVER, "name": pilot.NAME_PREFIX + "mock", "project_id": PROJECT,
            "zone": "nl-ams-1", "commercial_type": "GP1-L", "tags": ["explicit-lean-simp-pilot"],
            "public_ip": {"address": "198.51.100.4"}}
        original = provider
        def transfer(command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
            if command and command[0] == "scp":
                source = next(k for k in source_archives if k in str(command[-2]))
                Path(command[-1]).write_bytes(source_archives[source].read_bytes())
                return subprocess.CompletedProcess(command, 0, "", "")
            return original(command, timeout)
        state = {"schema": 1, "phase": "workers-finished", "server_id": SERVER,
            "name": provider.server["name"], "zone": "nl-ams-1", "project_id": PROJECT,
            "organization_id": ORG, "remote_job_directory": "/home/ubuntu/explicit-lean-simp-jobs",
            "policy_sha256": pilot.sha256_file(path),
            "jobs": [{"id": spec["id"], "phase": "finished", "exit_code": 0} for spec in policy["jobs"]]}
        (root / "state.json").write_text(json.dumps(state))
        output = root / "result"; got = pilot.ScalewayPilot(policy_path=path, state_path=root / "state.json",
            runner=transfer, now=lambda: NOW).collect_workers(output_dir=output)
        assert got["phase"] == "collected" and len(got["artifact_file_hashes"]) == 8
        for job_id, digest in expected_hashes.items():
            assert pilot.sha256_file(output / job_id / "mathlib-db.sqlite3") == digest


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
        assert deleted["phase"] == "deleted" and provider.server is None
        assert controller.cleanup(confirm=True)["phase"] == "deleted"


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


def main() -> None:
    tests = [test_policy_cost_deadline_worker_count_and_job_hashes_fail_closed,
             test_read_only_preflight_uses_real_cli_response_shapes_and_two_hash_pins,
             test_create_and_two_workers_launch_concurrently_with_remote_hash_check,
             test_collection_verifies_both_result_archives_and_hashes,
             test_status_marker_parsing_and_cleanup_idempotence,
             test_ambiguous_create_never_retries_and_policy_default_is_disabled,
             test_supervisor_collects_and_cleans_even_when_dispatch_fails]
    for test in tests:
        test()
    print(f"{len(tests)} Scaleway full-run mock checks passed")


if __name__ == "__main__":
    main()
