#!/usr/bin/env python3
"""Mock-only checks for the Scaleway single-host pilot controller."""

from __future__ import annotations

from copy import deepcopy
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import tarfile
from typing import Any, Sequence

import scaleway_simp_replacements as pilot


NOW = datetime(2026, 9, 22, 12, 0, tzinfo=timezone.utc)
ORG = "11111111-1111-4111-8111-111111111111"
PROJECT = "22222222-2222-4222-8222-222222222222"
IMAGE = "33333333-3333-4333-8333-333333333333"
SG = "44444444-4444-4444-8444-444444444444"
KEY = "55555555-5555-4555-8555-555555555555"
SERVER = "66666666-6666-4666-8666-666666666666"
COMMIT = "a" * 40


def require_blocked(function: Any, text: str) -> None:
    try:
        function()
    except pilot.PilotError:
        return
    raise AssertionError(text)


def make_policy(root: Path, job_dir: Path, identity: Path) -> dict[str, Any]:
    manifest = job_dir / "modules.txt"
    database = job_dir / "mathlib-db.sqlite3"
    return {
        "schema": 1,
        "provider": "scaleway",
        "launch_authorized": True,
        "cli_profile": "test-dedicated-pilot",
        "login_user": "ubuntu",
        "authorization": {
            "organization_id": ORG,
            "project_id": PROJECT,
            "zone": "nl-ams-1",
            "not_after": "2026-09-22T18:00:00Z",
            "max_instance_lifetime_seconds": 6 * 3600,
            "max_worker_runtime_seconds": 5 * 3600,
            "max_cost_eur": "12.00",
            "estimated_all_in_cost_eur": "10.50",
            "cost_checked_at": "2026-09-22T12:00:00Z",
            "cost_source": "Scaleway official pricing snapshot",
            "cost_components_eur": {"compute": "9.00", "public_ipv4": "1.00", "storage": "0.00", "egress_and_other": "0.50"},
        },
        "machine": {
            "type": pilot.EXPECTED_TYPE,
            "image_id": IMAGE,
            "security_group_id": SG,
            "ssh_key_id": KEY,
            "ssh_identity_file": str(identity),
            "ssh_source_cidr": "192.0.2.0/24",
        },
        "repository": {"url": pilot.CANONICAL_REPO, "commit": COMMIT},
        "job": {
            "directory": str(job_dir.resolve()),
            "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
            "database_sha256": pilot.sha256_file(database),
        },
        "requirements": {"single_host": True, "single_worker": True, "linux_x86_64": True,
                          "minimum_memory_gib": 128, "minimum_local_disk_gib": 200,
                          "root_volume": "local:559GB", "public_ipv4": True},
    }


class CliFixture:
    def __init__(self) -> None:
        self.commands: list[tuple[str, ...]] = []
        self.server: dict[str, Any] | None = None
        self.server_list: list[dict[str, Any]] = []
        self.volume_list: list[dict[str, Any]] = []
        self.bad_account = False
        self.bad_sg = False
        self.bad_image = False
        self.fail_delete = False

    def __call__(self, command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
        del timeout
        args = tuple(command)
        self.commands.append(args)
        if args and args[0] in {"scp", "ssh"}:
            return subprocess.CompletedProcess(args, 0, "", "")
        if args[:2] == ("scw", "version"):
            return subprocess.CompletedProcess(args, 0, "Version 2.fixture\n", "")
        if args[:4] == ("git", "rev-parse", "--verify", "HEAD"):
            return subprocess.CompletedProcess(args, 0, COMMIT + "\n", "")
        if args[:2] == ("git", "status"):
            return subprocess.CompletedProcess(args, 0, "", "")
        if args[:2] == ("git", "ls-remote"):
            return subprocess.CompletedProcess(args, 0, f"{COMMIT}\trefs/heads/main\n", "")
        if args[:3] == ("scw", "--output", "json"):
            cmd = args[5:]
            if cmd[:3] == ("account", "project", "list"):
                project = {"id": PROJECT, "organization_id": "99999999-9999-4999-8999-999999999999" if self.bad_account else ORG}
                return self.json(args, {"projects": [project]})
            if cmd[:3] == ("instance", "server", "list"):
                return self.json(args, {"servers": self.server_list})
            if cmd[:3] == ("instance", "volume", "list"):
                return self.json(args, {"volumes": self.volume_list})
            if cmd[:3] == ("instance", "server-type", "list"):
                return self.json(args, {"servers": [{"name": pilot.EXPECTED_TYPE, "ram": 128 * 1024**3, "ncpus": 32}]})
            if cmd[:3] == ("instance", "image", "list"):
                arch = "arm64" if self.bad_image else "x86_64"
                return self.json(args, {"images": [{"id": IMAGE, "arch": arch, "name": "ubuntu-jammy"}]})
            if cmd[:3] == ("instance", "security-group", "get"):
                ingress = "0.0.0.0/0" if self.bad_sg else "192.0.2.0/24"
                group = {"id": SG, "project_id": PROJECT, "inbound_default_policy": "drop", "rules": [
                    {"direction": "inbound", "protocol": "TCP", "dest_port_from": 22, "dest_port_to": 22, "ip_range": ingress}]}
                return self.json(args, {"security_group": group})
            if cmd[:3] == ("scw", "iam", "ssh-key"):
                raise AssertionError("bad command nesting")
            if cmd[:3] == ("iam", "ssh-key", "get"):
                return self.json(args, {"ssh_key": {"id": KEY, "project_id": PROJECT, "name": "pilot", "public_key": "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIE7fixture"}})
            if cmd[:3] == ("instance", "server", "create"):
                for arg in cmd:
                    if arg.startswith("cloud-init=@"):
                        cloud = Path(arg.removeprefix("cloud-init=@")).read_text()
                        assert "ssh_authorized_keys" in cloud
                        assert "OnCalendar=" in cloud and "Persistent=true" in cloud and "systemctl, enable, --now" in cloud
                tags = [arg.split("=", 1)[1] for arg in cmd if arg.startswith("tags.")]
                self.server = {"id": SERVER, "name": next(arg.split("=", 1)[1] for arg in cmd if arg.startswith("name=")),
                               "project_id": PROJECT, "zone": "nl-ams-1", "commercial_type": pilot.EXPECTED_TYPE, "tags": tags,
                               "public_ip": {"address": "198.51.100.4"}}
                return self.json(args, {"server": self.server})
            if cmd[:3] == ("instance", "server", "get"):
                return self.json(args, {"server": self.server})
            if cmd[:3] == ("instance", "server", "delete"):
                if self.fail_delete:
                    return subprocess.CompletedProcess(args, 1, "", "failure")
                self.server = None
                return self.json(args, {})
        raise AssertionError(f"unexpected command: {args}")

    @staticmethod
    def json(args: Sequence[str], payload: Any) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(args, 0, json.dumps(payload), "")


def setup(root: Path) -> tuple[Path, Path, Path, Path]:
    repo = root / "repo"; repo.mkdir()
    job = root / "job"; job.mkdir()
    (job / "modules.txt").write_text("Mathlib.Algebra.Group.Basic\n", encoding="utf-8")
    (job / "mathlib-db.sqlite3").write_bytes(b"sqlite-fixture")
    identity = root / "pilot_key"; identity.write_text("fake private key fixture", encoding="utf-8")
    identity.chmod(0o600)
    policy_path = root / "policy.json"
    policy_path.write_text(json.dumps(make_policy(root, job, identity)), encoding="utf-8")
    return repo, job, identity, policy_path


def controller(root: Path, policy: Path, fixture: CliFixture, now: datetime = NOW) -> pilot.ScalewayPilot:
    return pilot.ScalewayPilot(policy_path=policy, state_path=root / "state.json", runner=fixture,
                               now=lambda: now)


def test_inactive_default_plan_and_auth_profile_guards() -> None:
    policy = pilot._read_json(pilot.POLICY_PATH, "default policy")
    assert policy["launch_authorized"] is False
    assert controller(Path("."), pilot.POLICY_PATH, CliFixture()).plan()["mutation_count"] == 0
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); repo, job, identity, _ = setup(root)
        complete = make_policy(root, job, identity)
        for profile in ("default", "explicit-lean-cloud", ""):
            changed = deepcopy(complete); changed["cli_profile"] = profile
            require_blocked(lambda changed=changed: pilot.validate_policy(changed, NOW), "unsafe CLI profile accepted")
        for change in (
            lambda p: p["authorization"].update(not_after="2026-09-22T11:59:00Z"),
            lambda p: p["authorization"].update(cost_checked_at="2026-09-20T12:00:00Z"),
            lambda p: p["authorization"].update(estimated_all_in_cost_eur="12.01"),
            lambda p: p["authorization"].update(max_instance_lifetime_seconds=13 * 3600),
            lambda p: p["requirements"].update(single_worker=False),
        ):
            changed = deepcopy(complete); change(changed)
            require_blocked(lambda changed=changed: pilot.validate_policy(changed, NOW), "invalid authorization envelope accepted")


def test_preflight_is_read_only_and_checks_exact_identity_shape_network_and_job() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); repo, job, _, policy_path = setup(root)
        fixture = CliFixture(); ctl = controller(root, policy_path, fixture)
        result = ctl.preflight(repo_root=repo, job_dir=job)
        assert result["read_only"] and result["identity"]["project_id"] == PROJECT
        assert result["job"]["module_count"] == 1
        assert not any("create" in command or "delete" in command for command in fixture.commands)
        for mutation in ("bad_account", "bad_image", "bad_sg"):
            bad = CliFixture(); setattr(bad, mutation, True)
            require_blocked(lambda bad=bad: controller(root, policy_path, bad).preflight(repo_root=repo, job_dir=job), f"{mutation} passed preflight")
            assert not any("server" in command and "create" in command for command in bad.commands)
        altered = job / "modules.txt"; altered.write_text("Mathlib.Other.Module\n")
        require_blocked(lambda: controller(root, policy_path, CliFixture()).preflight(repo_root=repo, job_dir=job), "changed manifest accepted")


def test_unpublished_dirty_checkout_and_duplicate_block_before_creation() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); repo, job, _, policy_path = setup(root)
        for kind in ("dirty", "unpublished", "duplicate"):
            fixture = CliFixture()
            if kind == "duplicate": fixture.server_list = [{"id": SERVER, "name": pilot.NAME_PREFIX + "already", "tags": []}]
            if kind == "dirty":
                original = fixture
                def dirty_runner(command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
                    if tuple(command[:2]) == ("git", "status"):
                        return subprocess.CompletedProcess(command, 0, " M changed\n", "")
                    return original(command, timeout)
                fixture_call = dirty_runner
            elif kind == "unpublished":
                original = fixture
                def unpublished_runner(command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
                    if tuple(command[:2]) == ("git", "ls-remote"):
                        return subprocess.CompletedProcess(command, 0, "", "")
                    return original(command, timeout)
                fixture_call = unpublished_runner
            else: fixture_call = fixture
            ctl = pilot.ScalewayPilot(policy_path=policy_path, state_path=root / (kind + ".json"), runner=fixture_call, now=lambda: NOW)
            require_blocked(lambda ctl=ctl: ctl.create(repo_root=repo, job_dir=job, confirm=True), f"{kind} checkout/resource gate passed")
            assert not any("create" in command for command in fixture.commands)


def test_explicit_create_then_readonly_status_and_expired_cleanup() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); repo, job, _, policy_path = setup(root); fixture = CliFixture()
        ctl = controller(root, policy_path, fixture)
        require_blocked(lambda: ctl.create(repo_root=repo, job_dir=job), "create ran without explicit confirmation")
        created = ctl.create(repo_root=repo, job_dir=job, confirm=True)
        assert created["server_id"] == SERVER and created["phase"] == "created"
        mutations = [c for c in fixture.commands if any(token in c for token in ("create", "delete"))]
        assert len(mutations) == 1
        snapshot = json.loads((root / "state.json").read_text())
        fixture.server = {**fixture.server, "project_id": PROJECT}
        status = ctl.status()
        assert status["read_only"] and json.loads((root / "state.json").read_text()) == snapshot
        # Cleanup remains available after authorization expiry so TTL failures do not strand storage.
        later = NOW + timedelta(hours=7)
        cleanup_ctl = controller(root, policy_path, fixture, now=later)
        require_blocked(lambda: cleanup_ctl.cleanup(), "delete ran without confirmation")
        deleted = cleanup_ctl.cleanup(confirm=True)
        assert deleted["phase"] == "deleted" and fixture.server is None


def test_delete_failure_and_policy_mutation_fail_closed() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); repo, job, _, policy_path = setup(root); fixture = CliFixture(); ctl = controller(root, policy_path, fixture)
        ctl.create(repo_root=repo, job_dir=job, confirm=True)
        fixture.fail_delete = True
        require_blocked(lambda: ctl.cleanup(confirm=True), "failed delete reported success")
        fixture.fail_delete = False
        policy = json.loads(policy_path.read_text()); policy["authorization"]["project_id"] = ORG
        policy_path.write_text(json.dumps(policy))
        require_blocked(lambda: ctl.cleanup(confirm=True), "cleanup accepted changed identity/policy")


def test_collection_requires_marker_and_matching_hashes() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); repo, job, _, policy_path = setup(root)
        policy = json.loads(policy_path.read_text())
        marker_input = (job / "modules.txt").read_bytes()
        result_db_bytes = b"updated-sqlite-copy"
        marker = {"schema": 1, "exit_code": 0, "commit": COMMIT,
                  "database_sha256": hashlib.sha256(result_db_bytes).hexdigest(),
                  "manifest_sha256": hashlib.sha256(marker_input).hexdigest()}
        contents = {"mathlib-db.sqlite3": result_db_bytes, "worker.log": b"worker done\n",
                    "complete.json": json.dumps(marker).encode(), "artifacts/report.json": b"{}"}
        archive_path = root / "remote-result.tar.gz"
        with tarfile.open(archive_path, "w:gz") as archive:
            for name, data in contents.items():
                source = root / name; source.parent.mkdir(parents=True, exist_ok=True); source.write_bytes(data)
                archive.add(source, arcname=name)

        class TransferFixture(CliFixture):
            def __call__(self, command: Sequence[str], timeout: int = 60) -> subprocess.CompletedProcess[str]:
                args = tuple(command)
                if args and args[0] == "scp":
                    self.commands.append(args)
                    Path(args[-1]).write_bytes(archive_path.read_bytes())
                    return subprocess.CompletedProcess(args, 0, "", "")
                if args and args[0] == "scw":
                    if "server" in args and "get" in args:
                        self.commands.append(args)
                        return self.json(args, {"server": {"id": SERVER, "name": pilot.NAME_PREFIX + "hash",
                                                            "project_id": PROJECT, "zone": "nl-ams-1",
                                                            "commercial_type": pilot.EXPECTED_TYPE,
                                                            "tags": ["explicit-lean-simp-pilot"],
                                                            "public_ip": {"address": "198.51.100.4"}}})
                    return super().__call__(command, timeout)
                return super().__call__(command, timeout)

        fixture = TransferFixture()
        state = {"schema": 1, "phase": "worker-finished", "worker_exit_code": 0,
                 "server_id": SERVER, "name": pilot.NAME_PREFIX + "hash", "zone": "nl-ams-1",
                 "project_id": PROJECT, "organization_id": ORG,
                 "policy_sha256": hashlib.sha256(policy_path.read_bytes()).hexdigest()}
        state_path = root / "state.json"; state_path.write_text(json.dumps(state))
        output = root / "collected"
        collected = pilot.ScalewayPilot(policy_path=policy_path, state_path=state_path, runner=fixture, now=lambda: NOW).collect(output_dir=output)
        assert collected["phase"] == "collected" and collected["artifact_file_hashes"]["worker.log"] == hashlib.sha256(contents["worker.log"]).hexdigest()
        assert (output / "mathlib-db.sqlite3").read_bytes() == result_db_bytes

        # A second bundle has no completion marker and must not be accepted.
        bad_contents = {name: data for name, data in contents.items() if name != "complete.json"}
        with tarfile.open(archive_path, "w:gz") as archive:
            for name, data in bad_contents.items():
                source = root / name; source.write_bytes(data); archive.add(source, arcname=name)
        fresh_state = {**state, "phase": "worker-finished"}
        state_path.write_text(json.dumps(fresh_state))
        require_blocked(lambda: pilot.ScalewayPilot(policy_path=policy_path, state_path=state_path, runner=fixture, now=lambda: NOW).collect(output_dir=root / "bad"), "missing marker accepted")

        bad_marker = {**marker, "database_sha256": "0" * 64}
        bad_contents = {**contents, "complete.json": json.dumps(bad_marker).encode()}
        with tarfile.open(archive_path, "w:gz") as archive:
            for name, data in bad_contents.items():
                source = root / name; source.write_bytes(data); archive.add(source, arcname=name)
        require_blocked(lambda: pilot.ScalewayPilot(policy_path=policy_path, state_path=state_path, runner=fixture, now=lambda: NOW).collect(output_dir=root / "checksum"), "mismatched database checksum accepted")


def test_one_worker_dispatch_is_pinned_bounded_and_checkpointed() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); repo, job, _, policy_path = setup(root); fixture = CliFixture()
        ctl = controller(root, policy_path, fixture)
        created = ctl.create(repo_root=repo, job_dir=job, confirm=True)
        ssh_calls: list[tuple[str, ...]] = []
        def fake_ssh(_state: Any, *args: str, timeout: int) -> subprocess.CompletedProcess[str]:
            ssh_calls.append(args)
            return subprocess.CompletedProcess(args, 0, "", "")
        ctl._ssh = fake_ssh  # type: ignore[method-assign]
        finished = ctl.run_worker(job_dir=job, repo_root=repo)
        assert finished["server_id"] == created["server_id"] and finished["phase"] == "worker-finished"
        assert finished["guest_poweroff_watchdog_armed"] and finished["worker_timeout_seconds"] <= 5 * 3600
        watchdog = next(args for args in ssh_calls if "systemd-run" in args)
        assert "poweroff" in watchdog
        bootstrap = next(args[-1] for args in ssh_calls if "curl" in " ".join(args))
        assert COMMIT in bootstrap and pilot.ELAN_URL in bootstrap and pilot.ELAN_SHA256 in bootstrap
        remote_worker = next(args[-1] for args in ssh_calls if "simp_replacement_worker.py" in " ".join(args))
        assert "--database" in remote_worker and "--manifest" in remote_worker and "--artifacts" in remote_worker
        assert "timeout --signal=TERM" in remote_worker and "complete.json" in remote_worker
        assert not any("simp-disabled" in " ".join(args) for args in ssh_calls)


def main() -> None:
    tests = [value for name, value in sorted(globals().items()) if name.startswith("test_") and callable(value)]
    for test in tests: test()
    print(f"{len(tests)} Scaleway pilot mock checks passed")


if __name__ == "__main__":
    main()
