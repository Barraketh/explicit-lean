#!/usr/bin/env python3
"""Mock-only acceptance checks for the bounded CloudFormation pilot."""

from __future__ import annotations

from copy import deepcopy
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import tempfile
from typing import Any, Sequence

import aws_linux_pilot as pilot


NOW = datetime(2026, 9, 11, 21, 0, tzinfo=timezone.utc)
RUN_ID = "20260911T210000Z-" + "a" * 32
RUN_ID_2 = "20260911T210000Z-" + "b" * 32
AUTH_REF = pilot.EXPECTED_REVIEWED_COMMIT


def policy() -> dict[str, Any]:
    value, _ = pilot.load_policy()
    result = deepcopy(value)
    result["authorization"]["notAfter"] = "2026-09-12T09:00:00Z"
    result["costEstimate"]["checkedAt"] = NOW.isoformat()
    return result


def repo(root: Path) -> None:
    (root / "lean-toolchain").write_text(pilot.EXPECTED_LEAN_TOOLCHAIN + "\n", encoding="utf-8")
    (root / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": pilot.EXPECTED_MATHLIB_COMMIT}]}), encoding="utf-8")


def git_runner(_repo: Path, args: Sequence[str]) -> subprocess.CompletedProcess[str]:
    if list(args[:2]) == ["rev-parse", "--verify"]:
        return subprocess.CompletedProcess(args, 0, AUTH_REF + "\n", "")
    if args[:1] == ["status"]:
        return subprocess.CompletedProcess(args, 0, "", "")
    if args[:1] == ["ls-remote"]:
        assert list(args[1:]) == [pilot.CANONICAL_REPO_URL]
        return subprocess.CompletedProcess(args, 0, f"{AUTH_REF}\trefs/heads/pilot\n", "")
    if args[:1] == ["merge-base"]:
        return subprocess.CompletedProcess(args, 0, "", "")
    raise AssertionError(f"unexpected git fixture call: {args}")


class AwsFixture:
    def __init__(self, *, root: bool = False, quota: int = 16, stack_failure: bool = False,
                 create_error: bool = False, malformed_create: bool = False,
                 delete_error: bool = False, malformed_send: bool = False,
                 no_bucket_policy: bool = False, instance_type_shape: str = "valid",
                 auth_probe_failure: bool = False, auth_probe_not_found_once: bool = False) -> None:
        self.commands: list[tuple[str, ...]] = []
        self.stack: dict[str, Any] | None = None
        self.root, self.quota, self.stack_failure = root, quota, stack_failure
        self.create_error, self.malformed_create = create_error, malformed_create
        self.delete_error, self.malformed_send = delete_error, malformed_send
        self.no_bucket_policy, self.instance_type_shape = no_bucket_policy, instance_type_shape
        self.auth_probe_failure, self.auth_probe_not_found_once = auth_probe_failure, auth_probe_not_found_once

    @staticmethod
    def operation(command: Sequence[str]) -> tuple[str, str]:
        index = command.index("--region")
        return command[index + 2], command[index + 3]

    def _stack_from_create(self, command: Sequence[str]) -> dict[str, Any]:
        name = command[command.index("--stack-name") + 1]
        begin = command.index("--parameters") + 1
        end = command.index("--capabilities")
        parsed: list[dict[str, str]] = []
        for item in command[begin:end]:
            key, value = item.split(",ParameterValue=", 1)
            parsed.append({"ParameterKey": key.removeprefix("ParameterKey="), "ParameterValue": value})
        tags_arg = command[command.index("--tags") + 1]
        return {"StackName": name, "StackStatus": "CREATE_FAILED" if self.stack_failure else "CREATE_COMPLETE",
                "Parameters": parsed, "Tags": json.loads(tags_arg),
                "Outputs": [{"OutputKey": "InstanceId", "OutputValue": "i-0123456789abcdef0"},
                            {"OutputKey": "EvidencePrefix", "OutputValue": f"aws-linux-pilot/{next(x['ParameterValue'] for x in parsed if x['ParameterKey'] == 'RunId')}/"},
                            {"OutputKey": "NotAfter", "OutputValue": f"{next(x['ParameterValue'] for x in parsed if x['ParameterKey'] == 'NotAfter')}Z"}]}

    def __call__(self, command: Sequence[str]) -> dict[str, Any]:
        command = tuple(command)
        self.commands.append(command)
        service, operation = self.operation(command)
        if (service, operation) == ("sts", "get-caller-identity"):
            arn = f"arn:aws:iam::{pilot.ACCOUNT_ID}:root" if self.root else f"arn:aws:iam::{pilot.ACCOUNT_ID}:user/explicit-lean-operator"
            return {"Account": pilot.ACCOUNT_ID, "Arn": arn, "UserId": "fixture"}
        if (service, operation) == ("service-quotas", "get-service-quota"):
            return {"Quota": {"Value": self.quota}}
        if (service, operation) == ("pricing", "get-products"):
            if "volumeApiName,Value=gp3" in command: price = "0.096"
            elif "AmazonVPC" in command:
                assert any("usagetype,Value=USW1-PublicIPv4:InUseAddress" in item for item in command)
                price = "0.005"
            else: price = "1.176"
            return {"pricePerUnitUsd": price}
        if (service, operation) == ("ssm", "get-parameter"):
            return {"Parameter": {"Name": pilot.AMI_PARAMETER, "Value": "ami-0123456789abcdef0"}}
        if (service, operation) == ("ec2", "describe-images"):
            return {"Images": [{"ImageId": "ami-0123456789abcdef0", "State": "available", "Architecture": "x86_64", "VirtualizationType": "hvm", "RootDeviceType": "ebs", "RootDeviceName": "/dev/xvda"}]}
        if (service, operation) == ("ec2", "describe-instance-types"):
            if self.instance_type_shape == "malformed": return {"InstanceTypes": [{"InstanceType": pilot.INSTANCE_TYPE}]}
            size = 120 * 1024 if self.instance_type_shape == "undersized" else 131072
            architectures = ["arm64"] if self.instance_type_shape == "wrong-architecture" else ["x86_64"]
            return {"InstanceTypes": [{"InstanceType": pilot.INSTANCE_TYPE, "MemoryInfo": {"SizeInMiB": size}, "ProcessorInfo": {"SupportedArchitectures": architectures}}]}
        if (service, operation) == ("ec2", "describe-vpcs"):
            return {"Vpcs": [{"VpcId": "vpc-0123456789abcdef0", "CidrBlock": "10.0.0.0/16"}]}
        if (service, operation) == ("ec2", "describe-subnets"):
            return {"Subnets": [{"SubnetId": "subnet-0123456789abcdef0", "AvailabilityZone": "us-west-1a"}]}
        if (service, operation) == ("ec2", "describe-instance-type-offerings"):
            return {"InstanceTypeOfferings": [{"InstanceType": pilot.INSTANCE_TYPE, "Location": "us-west-1a"}]}
        if (service, operation) == ("s3api", "get-bucket-location"):
            return {"LocationConstraint": pilot.EVIDENCE_REGION}
        if (service, operation) == ("s3api", "get-bucket-versioning"):
            return {"Status": "Enabled"}
        if (service, operation) == ("s3api", "get-public-access-block"):
            return {"PublicAccessBlockConfiguration": {key: True for key in ("BlockPublicAcls", "IgnorePublicAcls", "BlockPublicPolicy", "RestrictPublicBuckets")}}
        if (service, operation) == ("s3api", "get-bucket-policy-status"):
            if self.no_bucket_policy:
                raise pilot.PilotError("AWS CLI failed (254): NoSuchBucketPolicy")
            return {"PolicyStatus": {"IsPublic": False}}
        if (service, operation) == ("s3api", "get-bucket-encryption"):
            return {"ServerSideEncryptionConfiguration": {"Rules": [{"ApplyServerSideEncryptionByDefault": {"SSEAlgorithm": "AES256"}}]}}
        if (service, operation) == ("s3api", "get-bucket-ownership-controls"):
            return {"OwnershipControls": {"Rules": [{"ObjectOwnership": "BucketOwnerEnforced"}]}}
        if (service, operation) == ("cloudformation", "describe-stacks"):
            return {"Stacks": [] if self.stack is None else [self.stack]}
        if (service, operation) == ("cloudformation", "create-stack"):
            if self.create_error: raise pilot.PilotError("simulated create timeout")
            self.stack = self._stack_from_create(command)
            if self.malformed_create: return {}
            return {"StackId": "arn:aws:cloudformation:us-west-1:538639825139:stack/fixture/id"}
        if (service, operation) == ("cloudformation", "delete-stack"):
            if self.delete_error: raise pilot.PilotError("simulated delete failure")
            return {}
        if (service, operation) == ("ec2", "describe-instances"):
            if "--filters" in command:
                if self.stack is None: return {"Reservations": []}
                return {"Reservations": [{"Instances": [{"InstanceId": "i-0123456789abcdef0", "InstanceState": {"Name": "running"}}]}]}
            return {"Reservations": [{"Instances": [{"InstanceId": "i-0123456789abcdef0", "InstanceType": pilot.INSTANCE_TYPE, "Placement": {"Tenancy": "default"}, "RootDeviceName": "/dev/xvda", "BlockDeviceMappings": [{"DeviceName": "/dev/xvda", "Ebs": {"VolumeId": "vol-0123456789abcdef0", "DeleteOnTermination": True}}], "NetworkInterfaces": [{}]}]}]}
        if (service, operation) == ("ec2", "describe-volumes"):
            return {"Volumes": [{"VolumeId": "vol-0123456789abcdef0", "VolumeType": "gp3", "Size": 200, "Encrypted": True}]}
        if (service, operation) == ("ssm", "describe-instance-information"):
            return {"InstanceInformationList": [{"InstanceId": "i-0123456789abcdef0", "PingStatus": "Online"}]}
        if (service, operation) == ("ssm", "send-command"):
            comment = command[command.index("--comment") + 1]
            if "auth-postcheck" in comment: return {"Command": {"CommandId": "cmd-auth-probe"}}
            if self.malformed_send: return {"Command": {}}
            return {"Command": {"CommandId": "cmd-1"}}
        if (service, operation) == ("s3api", "list-objects-v2"):
            return {"Contents": []}
        if (service, operation) == ("ssm", "get-command-invocation"):
            command_id = command[command.index("--command-id") + 1]
            if command_id == "cmd-auth-probe" and self.auth_probe_not_found_once:
                self.auth_probe_not_found_once = False
                raise pilot.PilotError("AWS CLI failed (254): An error occurred (InvocationDoesNotExist) when calling the GetCommandInvocation operation")
            if command_id == "cmd-auth-probe" and self.auth_probe_failure: return {"Status": "Failed", "ResponseCode": 1}
            return {"Status": "Success", "ResponseCode": 0}
        raise AssertionError(f"unexpected fixture call: {service} {operation}")


def write_policy(root: Path) -> Path:
    path = root / "policy.json"; path.write_text(json.dumps(policy()), encoding="utf-8"); return path


def controller(fixture: AwsFixture, root: Path, policy_path: Path, repo_path: Path) -> pilot.PilotController:
    return pilot.PilotController(policy_path=policy_path, repo_root=repo_path, state_root=root / "states", runner=fixture, git_runner=git_runner, now=lambda: NOW, sleep=lambda _seconds: None, budget_check=lambda: {"canDispatch": True, "decision": "continue"}, session_runner=lambda _command: subprocess.CompletedProcess([], 0, "", ""))


def ops(fixture: AwsFixture) -> list[str]:
    return [fixture.operation(command)[1] for command in fixture.commands]


def require_blocked(function: Any, message: str = "gate accepted") -> None:
    try: function()
    except pilot.PilotError: return
    raise AssertionError(message)


def proof(root: Path, *, run_id: str = RUN_ID, checked: datetime = NOW, instance: str = "i-0123456789abcdef0") -> Path:
    path = root / "remote-auth-proof.json"; path.write_text(json.dumps({"schema": 1, "strategy": pilot.REMOTE_AUTH_STRATEGY, "checkedAt": checked.isoformat(), "instanceId": instance, "codexLoginStatus": "logged_in", "campaignBudget": {"canDispatch": True, "decision": "continue"}, "runId": run_id}), encoding="utf-8"); return path


def test_static_guards() -> None:
    value = policy(); assert pilot.parse_not_after(value, NOW).hour == 9
    stale = deepcopy(value); stale["costEstimate"]["checkedAt"] = "2026-09-09T21:00:00Z"; require_blocked(lambda: pilot.validate_cost(stale, NOW), "stale price accepted")
    exact = deepcopy(value); exact["costEstimate"]["estimatedBoundedSubtotalUsd"] = 20; require_blocked(lambda: pilot.validate_cost(exact, NOW), "$20 bound accepted")
    for value in ("old", "20260911T200000Z-" + "a" * 32): require_blocked(lambda value=value: pilot.validate_run_id(value, NOW), "stale nonce accepted")
    assert pilot.validate_repo_url(pilot.CANONICAL_REPO_URL + "/") == pilot.CANONICAL_REPO_URL
    for value in ("github.com/a/b", "ssh://github.com/Barraketh/explicit-lean.git", "https://github.com/a/b.git", "https://www.github.com/Barraketh/explicit-lean.git"):
        require_blocked(lambda value=value: pilot.validate_repo_url(value), "noncanonical repository accepted")


def test_template_and_worker_invariants() -> None:
    result = pilot.validate_template_invariants(); template = pilot.load_template(); assert result["defaultTenancy"] and result["noIngress"] and result["oneTimeTtl"] and result["managedSsmPolicy"] and result["schedulerMode"] == "OFF" and result["schedulerActionAfterCompletion"] is False; assert "ActionAfterCompletion" not in template and "Mode: 'OFF'" in template and "Mode: OFF" not in template and "at(${NotAfter})" in template and "MaximumRetryAttempts: 0" in template and "OnCalendar=$(printf '%s\\n' '${NotAfter}' | tr 'T' ' ') UTC" in template and "OnCalendar=${NotAfter} UTC" not in template; require_blocked(lambda: pilot.validate_template_invariants(template.replace("Mode: 'OFF'", "Mode: OFF")), "bare scheduler OFF accepted"); require_blocked(lambda: pilot.validate_template_invariants(template + "\nActionAfterCompletion: DELETE\n"), "unsupported scheduler property accepted"); require_blocked(lambda: pilot.validate_template_invariants(template.replace("OnCalendar=$(printf '%s\\n' '${NotAfter}' | tr 'T' ' ') UTC", "OnCalendar=${NotAfter} UTC")), "T-separated guest timer accepted")
    commands = pilot.build_worker_commands(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, not_after=datetime(2026, 9, 12, 9, tzinfo=timezone.utc), input_root=f".lake/search-free-mathlib/aws-linux-pilot/{RUN_ID}", output_root=f".lake/boundary-materialization/aws-linux-pilot/{RUN_ID}", worker_id="worker")
    joined = "\n".join(commands)
    assert commands[0] == "set -Eeuo pipefail" and commands[1] == "export HOME=/root"
    home_use = next(index for index, command in enumerate(commands) if "$HOME" in command)
    assert home_use > commands.index("export HOME=/root")
    bootstrap = next(command for command in commands if command.startswith("dnf install -y"))
    assert "curl" not in bootstrap.split()[3:] and "curl-minimal" not in bootstrap.split()[3:] and 'test -x "$(command -v curl)"' in joined
    assert "git clone --no-checkout" in joined and "git ls-remote " + pilot.CANONICAL_REPO_URL in joined and "git ls-remote origin" not in joined
    assert "metadata_token=" in joined and "X-aws-ec2-metadata-token:" in joined and "${evidence_prefix}worker-started.json" in joined and f"-ge {pilot.MINIMUM_GUEST_MEMORY_BYTES}" in joined and f"-ge {pilot.REQUIRED_MEMORY_BYTES}" not in joined
    assert "sha256sum -c -" in joined and pilot.ELAN_URL in joined and pilot.ELAN_SHA256 in joined and "v4.1.2" not in joined and "libzstd-devel" in joined
    assert "codex login status" in joined and "campaign_budget.py check" in joined and "auth.json" not in joined and "test ! -e \"$output_root/evidence.tar.gz\"" in joined
    assert "--retry-failed" not in joined and "--if-none-match '*'" in joined and joined.count("--module ") == len(pilot.PILOT_MODULES)
    with tempfile.TemporaryDirectory() as directory:
        shell = Path(directory) / "worker.sh"; shell.write_text(joined + "\n", encoding="utf-8")
        assert subprocess.run(["bash", "-n", str(shell)], check=False).returncode == 0


def test_read_only_plan_and_dry_run() -> None:
    fixture = AwsFixture()
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root); ctl = controller(fixture, root, policy_path, checkout)
        plan = ctl.plan(); assert plan["readOnly"] and any("full --authorization-ref" in x for x in plan["blockers"]) and not any(x in {"create-stack", "send-command", "delete-stack"} for x in ops(fixture))
        fixture.commands.clear(); dry = ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, dry_run=True); assert dry["dryRun"] and dry["readOnly"] and not any(x in {"create-stack", "send-command", "delete-stack"} for x in ops(fixture))
        no_policy = AwsFixture(no_bucket_policy=True)
        no_policy_plan = controller(no_policy, root, policy_path, checkout).plan()
        assert "error" not in no_policy_plan and any("full --authorization-ref" in x for x in no_policy_plan["blockers"])


def test_invalid_checkout_and_confirmation_are_pre_mutation() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root)
        def dirty(_path: Path, args: Sequence[str]) -> subprocess.CompletedProcess[str]:
            value = git_runner(_path, args); return subprocess.CompletedProcess(args, 0, " M dirty\n", "") if args[:1] == ["status"] else value
        def unpublished(_path: Path, args: Sequence[str]) -> subprocess.CompletedProcess[str]:
            value = git_runner(_path, args); return subprocess.CompletedProcess(args, 0, "", "") if args[:1] == ["ls-remote"] else value
        for url, git in (("github.com/Barraketh/explicit-lean.git", git_runner), (pilot.CANONICAL_REPO_URL, dirty), (pilot.CANONICAL_REPO_URL, unpublished)):
            fixture = AwsFixture(); ctl = controller(fixture, root, policy_path, checkout); ctl.git_runner = git; require_blocked(lambda url=url, ctl=ctl: ctl.launch(repo_url=url, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True)); assert not any(x in {"create-stack", "send-command", "delete-stack"} for x in ops(fixture))
        fixture = AwsFixture(); require_blocked(lambda: controller(fixture, root, policy_path, checkout).launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID)); assert fixture.commands == []


def test_launch_stops_for_auth_then_one_worker_dispatch() -> None:
    fixture = AwsFixture(auth_probe_not_found_once=True)
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root); ctl = controller(fixture, root, policy_path, checkout)
        launched = ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True); assert launched["phase"] == "awaiting-codex-auth" and ops(fixture).count("create-stack") == 1 and ops(fixture).count("send-command") == 0
        session_commands: list[tuple[str, ...]] = []
        ctl.session_runner = lambda command: (session_commands.append(tuple(command)) or subprocess.CompletedProcess([], 0, "", ""))
        auth_result = ctl.auth(run_id=RUN_ID, confirm_auth=True); assert auth_result["kind"] == "aws_linux_pilot_auth" and auth_result["authProbeCommandId"] == "cmd-auth-probe" and ops(fixture).count("send-command") == 1; assert sum(1 for command in fixture.commands if "get-command-invocation" in command and command[command.index("--command-id") + 1] == "cmd-auth-probe") == 2; probe_command = next(x for x in fixture.commands if "send-command" in x and any("auth-postcheck" in part for part in x)); probe_script = "\n".join(json.loads(probe_command[probe_command.index("--parameters") + 1])["commands"]); assert "systemctl is-active --quiet explicit-lean-pilot-shutdown.timer" in probe_script and "campaign_budget.py check" in probe_script and "campaign_worker.py" not in probe_script
        assert session_commands and "cloud-init status --wait" in session_commands[0][-1] and "sudo -H /usr/local/bin/codex login --device-auth" in session_commands[0][-1] and "sudo -H /usr/local/bin/codex login status" in session_commands[0][-1] and "campaign_budget.py check" in session_commands[0][-1] and "auth-budget.json" in session_commands[0][-1] and "jq -e" in session_commands[0][-1]
        proof_path = Path(auth_result["remoteAuthProof"]); assert proof_path.is_file(); generated = json.loads(proof_path.read_text()); assert generated["runId"] == RUN_ID and generated["instanceId"] == "i-0123456789abcdef0"; assert pilot.validate_remote_auth_proof(proof_path, instance_id="i-0123456789abcdef0", run_id=RUN_ID, now=NOW)["codexLoginStatus"] == "verified"; require_blocked(lambda: pilot.validate_remote_auth_proof(proof_path, instance_id="i-0123456789abcdef0", run_id=RUN_ID_2, now=NOW))
        started = ctl.start_worker(run_id=RUN_ID, remote_auth_proof=proof_path, confirm_start_worker=True); assert started["phase"] == "worker-started" and started["workerCommandId"] == "cmd-1"; assert ops(fixture).count("create-stack") == 1 and ops(fixture).count("send-command") == 2 and ops(fixture).count("delete-stack") == 0
        command = next(x for x in fixture.commands if "send-command" in x and any("bounded-worker" in part for part in x)); script = json.loads(command[command.index("--parameters") + 1])["commands"]; joined = "\n".join(script); assert "codex login status" in joined and "campaign_budget.py check" in joined
        duplicate = ctl.start_worker(run_id=RUN_ID, remote_auth_proof=proof_path, confirm_start_worker=True); assert duplicate["idempotent"] and ops(fixture).count("send-command") == 2


def test_auth_transport_zero_postcheck_failure_emits_no_proof() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root); fixture = AwsFixture(auth_probe_failure=True); ctl = controller(fixture, root, policy_path, checkout)
        ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True); require_blocked(lambda: ctl.auth(run_id=RUN_ID, confirm_auth=True)); state = json.loads((root / "states" / f"{RUN_ID}.json").read_text()); assert state["phase"] == "awaiting-codex-auth" and state["authRetryRequired"] is True and state["authProbe"]["commandId"] == "cmd-auth-probe" and state["authProbe"]["status"] == "Failed" and not list((root / "states").glob(f"{RUN_ID}.remote-auth-proof.json")); assert ops(fixture).count("send-command") == 1 and not any(any("bounded-worker" in part for part in command) for command in fixture.commands)


def test_preworker_cleanup_and_cleanup_failure_are_distinct() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root)
        fixture = AwsFixture(stack_failure=True); ctl = controller(fixture, root, policy_path, checkout); require_blocked(lambda: ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True)); assert ops(fixture).count("delete-stack") == 1 and json.loads((root / "states" / f"{RUN_ID}.json").read_text())["stackCleanup"]["requested"] is True
        failed_cleanup = AwsFixture(stack_failure=True, delete_error=True); other = root / "other"; other.mkdir(); ctl = controller(failed_cleanup, other, policy_path, checkout); require_blocked(lambda: ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True)); state = json.loads((other / "states" / f"{RUN_ID}.json").read_text()); assert state["stackCleanup"]["requested"] is False and "error" in state["stackCleanup"]


def test_ambiguous_create_and_duplicate_nonce() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root); ambiguous = AwsFixture(create_error=True); ctl = controller(ambiguous, root, policy_path, checkout); require_blocked(lambda: ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True)); state = json.loads((root / "states" / f"{RUN_ID}.json").read_text()); assert state["phase"] == "create-ambiguous" and state["manualAttention"] and ops(ambiguous).count("delete-stack") == 0
        fixture = AwsFixture(malformed_create=True); good = root / "good"; good.mkdir(); ctl = controller(fixture, good, policy_path, checkout); result = ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True); assert result["idempotent"] and ops(fixture).count("create-stack") == 1
        second = ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID_2, confirm_launch=True); assert second["idempotent"] and second["runId"] == RUN_ID and not (good / "states" / f"{RUN_ID_2}.json").exists() and ops(fixture).count("create-stack") == 1


def test_nominal_instance_capacity_and_guest_sanity_gate() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root)
        valid = AwsFixture(); planned = controller(valid, root, policy_path, checkout).plan(); shape = planned["checks"]["instanceType"]; assert shape["memorySizeMiB"] == 131072 and shape["nominalMemoryBytes"] == pilot.REQUIRED_MEMORY_BYTES and shape["guestMemorySanityBytes"] == pilot.MINIMUM_GUEST_MEMORY_BYTES
        for invalid in ("undersized", "wrong-architecture", "malformed"):
            fixture = AwsFixture(instance_type_shape=invalid); ctl = controller(fixture, root, policy_path, checkout); require_blocked(lambda ctl=ctl: ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True)); assert not any(x in {"create-stack", "send-command", "delete-stack"} for x in ops(fixture))


def test_root_quota_deadline_cost_and_status_are_safe() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root)
        for fixture in (AwsFixture(root=True), AwsFixture(quota=8), AwsFixture()):
            ctl = controller(fixture, root, policy_path, checkout)
            if fixture.quota == 16 and not fixture.root: ctl.pricing_check = lambda: {"checkedAt": "2026-09-09T21:00:00Z", "ec2OnDemandUsdPerHour": 1.176, "gp3UsdPerGbMonth": .096, "publicIpv4UsdPerHour": .005, "estimatedBoundedSubtotalUsd": 14.492, "unallocatedSpendHeadroomUsd": 5.508, "tenancy": "default"}
            result = ctl.plan(); assert not result["ready"]; assert not any(x in {"create-stack", "send-command", "delete-stack"} for x in ops(fixture))
        expired = policy(); expired["authorization"]["notAfter"] = "2026-09-11T20:59:59Z"; expired_path = root / "expired.json"; expired_path.write_text(json.dumps(expired), encoding="utf-8"); fixture = AwsFixture(); result = pilot.PilotController(policy_path=expired_path, runner=fixture, now=lambda: NOW).plan(); assert not result["ready"] and not any(x in {"create-stack", "send-command", "delete-stack"} for x in ops(fixture))
        fixture = AwsFixture(); status = controller(fixture, root, policy_path, checkout).status(); assert status["readOnly"] and not any(x in {"create-stack", "send-command", "delete-stack"} for x in ops(fixture))


def test_remote_proof_and_ambiguous_send_retain_stack() -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory); checkout = root / "checkout"; checkout.mkdir(); repo(checkout); policy_path = write_policy(root); fixture = AwsFixture(); ctl = controller(fixture, root, policy_path, checkout); ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True); require_blocked(lambda: ctl.start_worker(run_id=RUN_ID, confirm_start_worker=True)); assert ops(fixture).count("send-command") == 0
        bad = proof(root, checked=datetime(2026, 9, 11, 20, 0, tzinfo=timezone.utc)); require_blocked(lambda: ctl.start_worker(run_id=RUN_ID, remote_auth_proof=bad, confirm_start_worker=True)); assert ops(fixture).count("send-command") == 0
        malformed = AwsFixture(malformed_send=True); second = root / "second"; second.mkdir(); ctl = controller(malformed, second, policy_path, checkout); ctl.launch(repo_url=pilot.CANONICAL_REPO_URL, authorization_ref=AUTH_REF, run_id=RUN_ID, confirm_launch=True); require_blocked(lambda: ctl.start_worker(run_id=RUN_ID, remote_auth_proof=proof(second), confirm_start_worker=True)); state = json.loads((second / "states" / f"{RUN_ID}.json").read_text()); assert state["phase"] == "dispatch-ambiguous" and state["manualAttention"] and ops(malformed).count("delete-stack") == 0


def main() -> None:
    tests = [test_static_guards, test_template_and_worker_invariants, test_read_only_plan_and_dry_run, test_invalid_checkout_and_confirmation_are_pre_mutation, test_launch_stops_for_auth_then_one_worker_dispatch, test_auth_transport_zero_postcheck_failure_emits_no_proof, test_preworker_cleanup_and_cleanup_failure_are_distinct, test_ambiguous_create_and_duplicate_nonce, test_nominal_instance_capacity_and_guest_sanity_gate, test_root_quota_deadline_cost_and_status_are_safe, test_remote_proof_and_ambiguous_send_retain_stack]
    for test in tests: test()
    print(f"aws linux pilot: {len(tests)} mock-only tests passed")


if __name__ == "__main__": main()
