#!/usr/bin/env python3
"""Run schema-16 full closure in parallel on verified Vast.ai CPU capacity."""

from __future__ import annotations

import argparse
import ast
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time
from typing import Any
from urllib.parse import urlparse


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_QUERY = (
    "verified=true rentable=true cpu_arch=amd64 cpu_cores_effective>=12 "
    "cpu_ram>=30 disk_space>=80 disk_bw>=500 direct_port_count>=1 "
    "reliability>=0.995 inet_down>=200 inet_up>=100"
)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def run(command: list[str], *, timeout: int | None = None, check: bool = True) -> str:
    result = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )
    if check and result.returncode != 0:
        raise RuntimeError(f"command failed ({result.returncode}): {shlex.join(command)}\n{result.stdout}")
    return result.stdout


def json_command(command: list[str], *, timeout: int | None = None) -> Any:
    output = run(command, timeout=timeout)
    return parse_jsonish(output, command)


def parse_jsonish(output: str, command: list[str] | None = None) -> Any:
    try:
        return json.loads(output)
    except json.JSONDecodeError:
        try:
            value = ast.literal_eval(output)
        except (SyntaxError, ValueError) as error:
            label = shlex.join(command) if command else "value"
            raise RuntimeError(f"command did not return structured data: {label}\n{output}") from error
        if not isinstance(value, (dict, list)):
            raise RuntimeError("command returned an unsupported structured value")
        return value


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def current_commit() -> str:
    return run(["git", "rev-parse", "HEAD"]).strip()


def assert_clean_commit(commit: str) -> None:
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise RuntimeError("commit must be a full SHA-1")
    if current_commit() != commit:
        raise RuntimeError("requested commit is not HEAD")
    if run(["git", "status", "--porcelain"]).strip():
        raise RuntimeError("Vast closure requires a clean worktree")
    remote = run(["git", "ls-remote", "origin"], timeout=30)
    if not any(line.startswith(commit + "\t") for line in remote.splitlines()):
        raise RuntimeError("commit is not the tip of a remote ref")


def offer_score(offer: dict[str, Any]) -> float:
    effective = max(float(offer.get("cpu_cores_effective") or 0), 0.1)
    ghz = min(max(float(offer.get("cpu_ghz") or 0), 1.0), 5.0)
    return float(offer["dph_total"]) / (effective * ghz)


def select_offers(
    offers: list[dict[str, Any]],
    count: int,
    max_offer_hourly: float,
    max_total_hourly: float,
) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    machines: set[int] = set()
    for offer in sorted(offers, key=lambda value: (offer_score(value), value["dph_total"])):
        machine = int(offer.get("machine_id", -1))
        price = float(offer.get("dph_total") or float("inf"))
        if machine < 0 or machine in machines or price > max_offer_hourly:
            continue
        if sum(float(item["dph_total"]) for item in selected) + price > max_total_hourly:
            continue
        selected.append(offer)
        machines.add(machine)
        if len(selected) == count:
            return selected
    raise RuntimeError(
        f"only {len(selected)}/{count} unique offers fit the hourly price guards"
    )


def search_offers(args: argparse.Namespace, extra: int = 0) -> list[dict[str, Any]]:
    raw = json_command([
        "vastai", "search", "offers", args.offer_query,
        "--raw", "--limit", str(max(100, args.workers + extra)),
        "--storage", str(args.disk_gb), "-o", "dph_total",
    ], timeout=60)
    offers = raw if isinstance(raw, list) else raw.get("offers", [])
    planned = select_offers(
        offers,
        args.workers,
        args.max_offer_hourly,
        args.max_total_hourly,
    )
    if extra <= 0:
        return planned
    selected_machines = {int(offer["machine_id"]) for offer in planned}
    extras: list[dict[str, Any]] = []
    for offer in sorted(offers, key=lambda value: (offer_score(value), value["dph_total"])):
        machine = int(offer.get("machine_id", -1))
        if machine < 0 or machine in selected_machines:
            continue
        if float(offer.get("dph_total") or float("inf")) > args.max_offer_hourly:
            continue
        extras.append(offer)
        selected_machines.add(machine)
        if len(extras) == extra:
            break
    return planned + extras


def public_offer(offer: dict[str, Any]) -> dict[str, Any]:
    fields = (
        "id", "machine_id", "dph_total", "cpu_cores_effective", "cpu_ghz",
        "cpu_name", "cpu_ram", "disk_bw", "reliability", "gpu_name",
        "geolocation", "inet_down", "inet_up",
    )
    return {field: offer.get(field) for field in fields}


def parse_ssh_url(value: str) -> tuple[str, int]:
    parsed = urlparse(value.strip())
    if parsed.scheme != "ssh" or not parsed.hostname or not parsed.port:
        raise ValueError(f"invalid Vast SSH URL: {value!r}")
    return parsed.hostname, parsed.port


def ssh_base(instance: dict[str, Any], known_hosts: Path) -> list[str]:
    return [
        "ssh", "-p", str(instance["sshPort"]),
        "-i", str(instance["sshPrivateKey"]), "-o", "IdentitiesOnly=yes",
        "-o", "BatchMode=yes", "-o", "ConnectTimeout=15",
        "-o", "ServerAliveInterval=15", "-o", "ServerAliveCountMax=4",
        "-o", "StrictHostKeyChecking=accept-new",
        "-o", f"UserKnownHostsFile={known_hosts}",
        f"root@{instance['sshHost']}",
    ]


def ssh(instance: dict[str, Any], known_hosts: Path, script: str, timeout: int) -> str:
    return run(
        ssh_base(instance, known_hosts) + ["bash -lc " + shlex.quote(script)],
        timeout=timeout,
    )


def scp_to(
    instance: dict[str, Any], known_hosts: Path, source: Path, destination: str
) -> None:
    command = [
        "scp", "-P", str(instance["sshPort"]),
        "-i", str(instance["sshPrivateKey"]), "-o", "IdentitiesOnly=yes",
        "-o", "BatchMode=yes", "-o", "ConnectTimeout=15",
        "-o", "StrictHostKeyChecking=accept-new",
        "-o", f"UserKnownHostsFile={known_hosts}",
        str(source), f"root@{instance['sshHost']}:{destination}",
    ]
    run(command, timeout=120)


def create_instance(offer: dict[str, Any], index: int, args: argparse.Namespace) -> dict[str, Any]:
    label = f"simp16-{args.commit[:8]}-{index:02d}"
    result = json_command([
        "vastai", "create", "instance", str(offer["id"]),
        "--image", args.image, "--disk", str(args.disk_gb),
        "--label", label, "--ssh", "--direct", "--cancel-unavail", "--raw",
    ], timeout=60)
    contract = result.get("new_contract")
    if not result.get("success") or contract is None:
        raise RuntimeError(f"Vast failed to create offer {offer['id']}: {result}")
    try:
        json_command([
            "vastai", "attach", "ssh", str(contract), str(args.ssh_public_key), "--raw",
        ], timeout=60)
    except Exception:
        run(
            ["vastai", "destroy", "instance", str(contract), "-y", "--raw"],
            timeout=60, check=False,
        )
        raise
    return {
        "workerIndex": index,
        "contractId": int(contract),
        "offer": public_offer(offer),
        "label": label,
        "sshHost": None,
        "sshPort": None,
        "sshPrivateKey": str(args.ssh_private_key),
        "status": "created",
    }


def show_instances() -> dict[int, dict[str, Any]]:
    raw = json_command(["vastai", "show", "instances", "--raw"], timeout=30)
    values = raw if isinstance(raw, list) else raw.get("instances", [])
    return {int(value["id"]): value for value in values}


def wait_for_ssh(
    instances: list[dict[str, Any]], timeout: int, known_hosts: Path,
) -> None:
    deadline = time.monotonic() + timeout
    pending = {instance["contractId"] for instance in instances}
    while pending and time.monotonic() < deadline:
        current = show_instances()
        for instance in instances:
            contract = instance["contractId"]
            value = current.get(contract, {})
            if value.get("cur_state") == "running":
                try:
                    host, port = parse_ssh_url(
                        run(["vastai", "ssh-url", str(contract), "--raw"], timeout=30)
                    )
                except (RuntimeError, ValueError):
                    continue
                instance["sshHost"] = host
                instance["sshPort"] = port
                try:
                    ssh(instance, known_hosts, "true", 30)
                except RuntimeError:
                    continue
                else:
                    instance["status"] = "running"
                    pending.discard(contract)
        if pending:
            time.sleep(10)
    if pending:
        raise RuntimeError(f"Vast instances did not become SSH-ready: {sorted(pending)}")


def setup_script(commit: str) -> str:
    return f"""set -euo pipefail
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y ca-certificates curl git rsync zstd
if [ ! -x /root/.elan/bin/elan ]; then
  curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain none
fi
export PATH=/root/.elan/bin:$PATH
if [ ! -d /workspace/explicit-lean/.git ]; then
  git clone --filter=blob:none https://github.com/Barraketh/explicit-lean.git /workspace/explicit-lean
fi
cd /workspace/explicit-lean
git fetch --depth=1 origin {commit}
git checkout --detach {commit}
lake exe cache get
lake build ExplicitLean
mkdir -p .cloud/vast-worker
"""


def setup_instance(
    instance: dict[str, Any], args: argparse.Namespace, output: Path, known_hosts: Path,
) -> None:
    log_path = output / "controller-logs" / f"setup-{instance['workerIndex']:02d}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        setup_output = ssh(instance, known_hosts, setup_script(args.commit), args.setup_timeout)
        log_path.write_text(setup_output, encoding="utf-8")
        scp_to(
            instance, known_hosts, output / "inventory.json",
            "/workspace/explicit-lean/.cloud/inventory.json",
        )
        command = f"""set -euo pipefail
export PATH=/root/.elan/bin:$PATH
cd /workspace/explicit-lean
setsid sh -c 'exec python3 Experiment/simp_engine_vast_worker.py --inventory .cloud/inventory.json --worker-index {instance['workerIndex']} --worker-count {args.workers} --shard-count {args.shard_count} --concurrency {args.concurrency} --module-timeout {args.module_timeout} --output-dir .cloud/vast-worker > .cloud/vast-worker/worker.log 2>&1' </dev/null >/dev/null 2>&1 &
echo $! > .cloud/vast-worker/worker.pid
"""
        ssh(instance, known_hosts, command, 60)
        instance["status"] = "working"
    except Exception as error:
        instance["status"] = "setup_failure"
        log_path.write_text(f"{type(error).__name__}: {error}\n", encoding="utf-8")
        raise


def rsync_from(instance: dict[str, Any], known_hosts: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    ssh_transport = shlex.join(ssh_base(instance, known_hosts)[:-1])
    run([
        "rsync", "-az", "--partial", "--timeout=45", "-e", ssh_transport,
        f"root@{instance['sshHost']}:/workspace/explicit-lean/.cloud/vast-worker/",
        str(destination) + "/",
    ], timeout=120)


def stop_worker(instance: dict[str, Any], known_hosts: Path) -> None:
    script = """if [ -f /workspace/explicit-lean/.cloud/vast-worker/worker.pid ]; then
pid=$(cat /workspace/explicit-lean/.cloud/vast-worker/worker.pid)
kill -- -$pid 2>/dev/null || true
fi
"""
    try:
        ssh(instance, known_hosts, script, 30)
    except Exception:
        pass


def destroy_instances(instances: list[dict[str, Any]]) -> None:
    for instance in instances:
        contract = instance.get("contractId")
        if contract is None or instance.get("status") == "destroyed":
            continue
        run(
            ["vastai", "destroy", "instance", str(contract), "-y", "--raw"],
            timeout=60, check=False,
        )
        instance["status"] = "destroyed"


def inventory(args: argparse.Namespace, output: Path) -> None:
    run([
        sys.executable, "Experiment/simp_engine_cloud.py", "inventory",
        "--commit", args.commit, "--output", str(output / "inventory.json"),
    ], timeout=args.inventory_timeout)


def reduce(output: Path, args: argparse.Namespace) -> int:
    result = subprocess.run([
        sys.executable, "Experiment/simp_engine_cloud.py", "reduce",
        "--inventory", str(output / "inventory.json"),
        "--reports-dir", str(output / "workers"),
        "--shard-count", str(args.shard_count),
        "--output-dir", str(output / "final"),
    ], cwd=ROOT, check=False)
    return result.returncode


def run_closure(args: argparse.Namespace) -> int:
    args.commit = args.commit or current_commit()
    args.ssh_private_key = Path(args.ssh_private_key).expanduser().resolve()
    args.ssh_public_key = Path(args.ssh_public_key).expanduser().resolve()
    if min(args.workers, args.concurrency, args.shard_count) <= 0:
        raise RuntimeError("worker, concurrency, and shard counts must be positive")
    if args.workers > args.shard_count:
        raise RuntimeError("worker count cannot exceed shard count")
    if args.max_total_hourly <= 0 or args.max_runtime_hours <= 0:
        raise RuntimeError("price and runtime guards must be positive")
    if not args.ssh_private_key.is_file() or not args.ssh_public_key.is_file():
        raise RuntimeError("Vast SSH private/public key pair is missing")
    assert_clean_commit(args.commit)
    output = Path(args.output_dir).resolve()
    if output.exists() and any(output.iterdir()):
        raise RuntimeError(f"output directory is not empty: {output}")
    output.mkdir(parents=True, exist_ok=True)
    known_hosts = output / "known_hosts"
    offers = search_offers(args, extra=min(8, args.workers))
    planned = offers[:args.workers]
    total_hourly = sum(float(offer["dph_total"]) for offer in planned)
    plan = {
        "schema": 1,
        "kind": "simp_engine_vast_run",
        "commit": args.commit,
        "createdAt": utc_now(),
        "status": "planned",
        "workerCount": args.workers,
        "concurrencyPerWorker": args.concurrency,
        "shardCount": args.shard_count,
        "totalModuleConcurrency": args.workers * args.concurrency,
        "totalHourlyUsd": total_hourly,
        "maximumRuntimeHours": args.max_runtime_hours,
        "maximumComputeUsd": total_hourly * args.max_runtime_hours,
        "offers": [public_offer(offer) for offer in planned],
        "instances": [],
    }
    state_path = output / "run-state.json"
    atomic_json(state_path, plan)
    print(
        f"Vast plan: {args.workers} hosts x {args.concurrency} processes = "
        f"{args.workers * args.concurrency} concurrent shards; "
        f"${total_hourly:.3f}/hour, <=${plan['maximumComputeUsd']:.2f}",
        flush=True,
    )
    if not args.execute:
        return 0

    inventory(args, output)
    instances: list[dict[str, Any]] = []
    plan["status"] = "launching"
    atomic_json(state_path, plan)
    deadline = time.monotonic() + args.max_runtime_hours * 3600
    try:
        candidates = iter(offers)
        while len(instances) < args.workers:
            offer = next(candidates, None)
            if offer is None:
                raise RuntimeError("Vast offers were exhausted during launch")
            if sum(float(item["offer"]["dph_total"]) for item in instances) + \
                    float(offer["dph_total"]) > args.max_total_hourly:
                continue
            try:
                instance = create_instance(offer, len(instances), args)
            except Exception as error:
                print(f"offer {offer['id']} unavailable: {error}", flush=True)
                continue
            instances.append(instance)
            plan["instances"] = instances
            atomic_json(state_path, plan)
            print(
                f"launched worker {instance['workerIndex']}: contract "
                f"{instance['contractId']} at ${offer['dph_total']:.3f}/hour",
                flush=True,
            )
        plan["totalHourlyUsd"] = sum(
            float(instance["offer"]["dph_total"]) for instance in instances
        )
        plan["maximumComputeUsd"] = plan["totalHourlyUsd"] * args.max_runtime_hours
        wait_for_ssh(instances, args.boot_timeout, known_hosts)
        plan["status"] = "setting_up"
        atomic_json(state_path, plan)
        with ThreadPoolExecutor(max_workers=min(args.workers, 8)) as executor:
            futures = {
                executor.submit(setup_instance, instance, args, output, known_hosts): instance
                for instance in instances
            }
            for future in as_completed(futures):
                future.result()
                print(f"worker {futures[future]['workerIndex']} started", flush=True)
                atomic_json(state_path, plan)
        plan["status"] = "running"
        atomic_json(state_path, plan)

        while time.monotonic() < deadline:
            states: list[dict[str, Any]] = []
            with ThreadPoolExecutor(max_workers=min(args.workers, 8)) as executor:
                futures = {
                    executor.submit(
                        rsync_from, instance, known_hosts,
                        output / "workers" / f"worker-{instance['workerIndex']:02d}",
                    ): instance
                    for instance in instances
                }
                for future in as_completed(futures):
                    instance = futures[future]
                    try:
                        future.result()
                    except Exception as error:
                        print(f"worker {instance['workerIndex']} sync warning: {error}", flush=True)
            for instance in instances:
                local = output / "workers" / f"worker-{instance['workerIndex']:02d}" / "worker-state.json"
                if local.exists():
                    states.append(json.loads(local.read_text(encoding="utf-8")))
            completed = sum(len(state.get("completedShards", [])) for state in states)
            failed = sum(len(state.get("failedShards", [])) for state in states)
            print(
                f"Vast progress: {completed}/{args.shard_count} shards complete, "
                f"{failed} failed, {len(states)}/{args.workers} workers reporting",
                flush=True,
            )
            if failed:
                plan["status"] = "worker_failure"
                atomic_json(state_path, plan)
                for instance in instances:
                    stop_worker(instance, known_hosts)
                break
            if len(states) == args.workers and all(state.get("status") == "success" for state in states):
                plan["status"] = "reducing"
                atomic_json(state_path, plan)
                code = reduce(output, args)
                plan["status"] = "success" if code == 0 else "reducer_failure"
                atomic_json(state_path, plan)
                return code
            time.sleep(args.poll_seconds)
        else:
            plan["status"] = "timeout"
            atomic_json(state_path, plan)
            for instance in instances:
                stop_worker(instance, known_hosts)

        with ThreadPoolExecutor(max_workers=min(args.workers, 8)) as executor:
            futures = [
                executor.submit(
                    rsync_from, instance, known_hosts,
                    output / "workers" / f"worker-{instance['workerIndex']:02d}",
                )
                for instance in instances
            ]
            for future in as_completed(futures):
                try:
                    future.result()
                except Exception as error:
                    print(f"final sync warning: {error}", flush=True)
        reduce(output, args)
        return 1
    except Exception as error:
        plan["status"] = "controller_failure"
        plan["error"] = f"{type(error).__name__}: {error}"
        atomic_json(state_path, plan)
        print(plan["error"], file=sys.stderr, flush=True)
        return 1
    finally:
        if not args.keep_instances:
            destroy_instances(instances)
            plan["instances"] = instances
            plan["destroyedAt"] = utc_now()
            atomic_json(state_path, plan)


def destroy_from_state(args: argparse.Namespace) -> None:
    state_path = Path(args.state)
    state = json.loads(state_path.read_text(encoding="utf-8"))
    destroy_instances(state.get("instances", []))
    state["destroyedAt"] = utc_now()
    atomic_json(state_path, state)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    subparsers = result.add_subparsers(dest="command", required=True)
    run_parser = subparsers.add_parser("run")
    run_parser.add_argument("--commit", default="")
    run_parser.add_argument("--output-dir", required=True)
    run_parser.add_argument("--workers", type=int, default=16)
    run_parser.add_argument("--concurrency", type=int, default=4)
    run_parser.add_argument("--shard-count", type=int, default=256)
    run_parser.add_argument("--disk-gb", type=int, default=40)
    run_parser.add_argument("--image", default="ubuntu:24.04")
    run_parser.add_argument("--ssh-private-key", default="~/.ssh/id_rsa")
    run_parser.add_argument("--ssh-public-key", default="~/.ssh/id_rsa.pub")
    run_parser.add_argument("--offer-query", default=DEFAULT_QUERY)
    run_parser.add_argument("--max-offer-hourly", type=float, default=0.20)
    run_parser.add_argument("--max-total-hourly", type=float, default=2.50)
    run_parser.add_argument("--max-runtime-hours", type=float, default=5.0)
    run_parser.add_argument("--module-timeout", type=int, default=900)
    run_parser.add_argument("--inventory-timeout", type=int, default=3600)
    run_parser.add_argument("--boot-timeout", type=int, default=900)
    run_parser.add_argument("--setup-timeout", type=int, default=1800)
    run_parser.add_argument("--poll-seconds", type=int, default=30)
    run_parser.add_argument("--execute", action="store_true")
    run_parser.add_argument("--keep-instances", action="store_true")
    run_parser.set_defaults(function=run_closure)
    destroy = subparsers.add_parser("destroy")
    destroy.add_argument("--state", required=True)
    destroy.set_defaults(function=destroy_from_state)
    return result


if __name__ == "__main__":
    arguments = parser().parse_args()
    value = arguments.function(arguments)
    raise SystemExit(value if isinstance(value, int) else 0)
