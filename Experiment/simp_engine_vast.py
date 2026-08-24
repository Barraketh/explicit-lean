#!/usr/bin/env python3
"""Run schema-18 full closure in parallel on verified Vast.ai CPU capacity."""

from __future__ import annotations

import argparse
import ast
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, as_completed, wait
from datetime import datetime, timezone
import gzip
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

import simp_engine_cloud as cloud


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_QUERY = (
    "verified=true rentable=true cpu_arch=amd64 cpu_cores_effective>=16 "
    "cpu_ram>=96 disk_space>=80 disk_bw>=300 direct_port_count>=1 "
    "reliability>=0.99 inet_down>=100 inet_up>=50"
)
# The report schema versions Python-side inventory assembly.  Byte discovery
# itself depends on these Lean sources and dependency pins; materializer and
# scheduler fixes must not invalidate an otherwise identical 83k-site census.
INVENTORY_INPUT_PATHS = (
    "Experiment/SimpEngineInventory.lean",
    "ExplicitLean/SimpEngine/Inventory.lean",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
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


def current_mathlib_commit() -> str:
    return run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]).strip()


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


def offer_score(offer: dict[str, Any], concurrency: int = 1) -> float:
    effective = max(float(offer.get("cpu_cores_effective") or 0), 0.1)
    ghz = min(max(float(offer.get("cpu_ghz") or 0), 1.0), 5.0)
    # Lean module compilation cannot use an arbitrary number of cores.  Cap the
    # useful CPU allocation per process so a large, expensive host does not win
    # merely because it exposes idle cores.
    useful_cores = min(effective, max(4, concurrency * 4))
    return float(offer["dph_total"]) / (useful_cores * ghz)


def offer_ram_mb(offer: dict[str, Any]) -> float:
    return float(offer.get("cpu_ram") or 0)


def offer_effective_cores(offer: dict[str, Any]) -> float:
    return float(offer.get("cpu_cores_effective") or 0)


def select_offers(
    offers: list[dict[str, Any]],
    count: int,
    max_offer_hourly: float,
    max_total_hourly: float,
    minimum_ram_mb: float = 0,
    concurrency: int = 1,
    minimum_effective_cores: float = 0,
) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    machines: set[int] = set()
    for offer in sorted(
        offers,
        key=lambda value: (offer_score(value, concurrency), value["dph_total"]),
    ):
        machine = int(offer.get("machine_id", -1))
        price = float(offer.get("dph_total") or float("inf"))
        if (
            machine < 0
            or machine in machines
            or price > max_offer_hourly
            or offer_ram_mb(offer) < minimum_ram_mb
            or offer_effective_cores(offer) < minimum_effective_cores
        ):
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


def market_offers(args: argparse.Namespace) -> list[dict[str, Any]]:
    raw = json_command([
        "vastai", "search", "offers", args.offer_query,
        "--raw", "--limit", "200",
        "--storage", str(args.disk_gb), "-o", "dph_total",
    ], timeout=60)
    return raw if isinstance(raw, list) else raw.get("offers", [])


def replacement_offers(
    offers: list[dict[str, Any]],
    args: argparse.Namespace,
    excluded_machines: set[int],
) -> list[dict[str, Any]]:
    minimum_ram_mb = args.minimum_ram_gb_per_process * args.concurrency * 1000
    minimum_effective_cores = args.minimum_cpu_cores_per_process * args.concurrency
    result: list[dict[str, Any]] = []
    machines = set(excluded_machines)
    for offer in sorted(
        offers,
        key=lambda value: (offer_score(value, args.concurrency), value["dph_total"]),
    ):
        machine = int(offer.get("machine_id", -1))
        if machine < 0 or machine in machines:
            continue
        if float(offer.get("dph_total") or float("inf")) > args.max_offer_hourly:
            continue
        if offer_ram_mb(offer) < minimum_ram_mb:
            continue
        if offer_effective_cores(offer) < minimum_effective_cores:
            continue
        result.append(offer)
        machines.add(machine)
    return result


def search_offers(args: argparse.Namespace, extra: int = 0) -> list[dict[str, Any]]:
    offers = market_offers(args)
    planned = select_offers(
        offers,
        args.workers,
        args.max_offer_hourly,
        args.max_total_hourly,
        args.minimum_ram_gb_per_process * args.concurrency * 1000,
        args.concurrency,
        args.minimum_cpu_cores_per_process * args.concurrency,
    )
    if extra <= 0:
        return planned
    selected_machines = {int(offer["machine_id"]) for offer in planned}
    extras = replacement_offers(offers, args, selected_machines)[:extra]
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
    instance: dict[str, Any], known_hosts: Path, source: Path, destination: str,
    *, timeout: int = 180,
) -> None:
    command = [
        "scp", "-P", str(instance["sshPort"]),
        "-i", str(instance["sshPrivateKey"]), "-o", "IdentitiesOnly=yes",
        "-o", "BatchMode=yes", "-o", "ConnectTimeout=15",
        "-o", "StrictHostKeyChecking=accept-new",
        "-o", f"UserKnownHostsFile={known_hosts}",
        str(source), f"root@{instance['sshHost']}:{destination}",
    ]
    run(command, timeout=timeout)


def create_instance(offer: dict[str, Any], index: int, args: argparse.Namespace) -> dict[str, Any]:
    label = f"simp17-{args.commit[:8]}-candidate-{index:02d}"
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
        "candidateIndex": index,
        "workerIndex": None,
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
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    deadline = time.monotonic() + timeout
    ready: dict[int, dict[str, Any]] = {}
    pending = {instance["contractId"]: instance for instance in instances}
    while pending and time.monotonic() < deadline:
        current = show_instances()
        probe: list[dict[str, Any]] = []
        for contract, instance in pending.items():
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
                probe.append(instance)
        with ThreadPoolExecutor(max_workers=min(len(probe), 16) or 1) as executor:
            futures = {
                executor.submit(ssh, instance, known_hosts, "true", 30): instance
                for instance in probe
            }
            for future in as_completed(futures):
                instance = futures[future]
                try:
                    future.result()
                except Exception:
                    continue
                else:
                    instance["status"] = "running"
                    contract = instance["contractId"]
                    ready[contract] = instance
                    pending.pop(contract, None)
        if pending:
            time.sleep(5)
    rejected = list(pending.values())
    for instance in rejected:
        instance["status"] = "ssh_rejected"
    return list(ready.values()), rejected


def setup_script(commit: str) -> str:
    return f"""set -euo pipefail
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y ca-certificates curl git rsync zstd
ulimit -n 65536
test "$(ulimit -n)" -ge 65536
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
lake build ExplicitLean ExplicitLean:shared
mkdir -p .cloud/vast-worker
"""


def compressed_inventory(output: Path) -> Path:
    source = output / "inventory.json"
    destination = output / "inventory.json.gz"
    with source.open("rb") as input_stream, gzip.open(
        destination, "wb", compresslevel=6
    ) as stream:
        while block := input_stream.read(1024 * 1024):
            stream.write(block)
    return destination


def transfer_inventory(
    instance: dict[str, Any], output: Path, known_hosts: Path,
) -> None:
    archive = output / "inventory.json.gz"
    error: Exception | None = None
    for attempt in range(1, 4):
        try:
            scp_to(
                instance,
                known_hosts,
                archive,
                "/workspace/explicit-lean/.cloud/inventory.json.gz",
            )
            ssh(
                instance,
                known_hosts,
                "cd /workspace/explicit-lean && "
                "gzip -dc .cloud/inventory.json.gz > .cloud/inventory.json.tmp && "
                "mv .cloud/inventory.json.tmp .cloud/inventory.json",
                120,
            )
            return
        except Exception as current:
            error = current
            if attempt < 3:
                time.sleep(2 * attempt)
    assert error is not None
    raise error


def setup_instance(
    instance: dict[str, Any], args: argparse.Namespace, output: Path, known_hosts: Path,
) -> None:
    log_path = output / "controller-logs" / f"setup-{instance['workerIndex']:02d}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        setup_output = ssh(instance, known_hosts, setup_script(args.commit), args.setup_timeout)
        log_path.write_text(setup_output, encoding="utf-8")
        transfer_inventory(instance, output, known_hosts)
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
        with log_path.open("a", encoding="utf-8") as stream:
            stream.write(f"\nSETUP_FAILURE: {type(error).__name__}: {error}\n")
        raise


def rsync_from(instance: dict[str, Any], known_hosts: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    ssh_transport = shlex.join(ssh_base(instance, known_hosts)[:-1])
    run([
        "rsync", "-az", "--partial", "--timeout=45", "--exclude=work/", "-e", ssh_transport,
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


def sync_worker_states(
    instances: list[dict[str, Any]], known_hosts: Path, output: Path,
) -> list[dict[str, Any]]:
    if not instances:
        return []
    with ThreadPoolExecutor(max_workers=len(instances)) as executor:
        futures = {
            executor.submit(
                rsync_from,
                instance,
                known_hosts,
                output / "workers" / f"worker-{instance['workerIndex']:02d}",
            ): instance
            for instance in instances
        }
        for future in as_completed(futures):
            instance = futures[future]
            try:
                future.result()
            except Exception as error:
                print(
                    f"worker {instance['workerIndex']} sync warning: {error}",
                    flush=True,
                )
    states: list[dict[str, Any]] = []
    for instance in instances:
        local = (
            output / "workers" / f"worker-{instance['workerIndex']:02d}"
            / "worker-state.json"
        )
        if local.exists():
            states.append(json.loads(local.read_text(encoding="utf-8")))
    return states


def stop_workers(instances: list[dict[str, Any]], known_hosts: Path) -> None:
    if not instances:
        return
    with ThreadPoolExecutor(max_workers=len(instances)) as executor:
        futures = [
            executor.submit(stop_worker, instance, known_hosts)
            for instance in instances
        ]
        for future in as_completed(futures):
            future.result()


def state_progress(states: list[dict[str, Any]]) -> tuple[int, int]:
    return (
        sum(len(state.get("completedShards", [])) for state in states),
        sum(len(state.get("failedShards", [])) for state in states),
    )


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


def validate_reusable_inventory(
    value: object, expected_commit: str, expected_mathlib_commit: str
) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise RuntimeError("reusable inventory must be a JSON object")
    if value.get("kind") != "simp_engine_inventory" or value.get("reportSchema") != 1:
        raise RuntimeError("reusable inventory has an unsupported format")
    if value.get("commit") != expected_commit:
        raise RuntimeError(
            f"reusable inventory commit mismatch: {value.get('commit')} != {expected_commit}"
        )
    if value.get("mathlibCommit") != expected_mathlib_commit:
        raise RuntimeError(
            "reusable inventory Mathlib commit mismatch: "
            f"{value.get('mathlibCommit')} != {expected_mathlib_commit}"
        )
    engine = value.get("engine")
    if not isinstance(engine, dict) or any(
        engine.get(field) != cloud.ENGINE_ID[field]
        for field in ("leanVersion", "leanCommit")
    ):
        raise RuntimeError("reusable inventory does not target the pinned Lean engine")
    modules = value.get("modules")
    if not isinstance(modules, list) or len(modules) != value.get("moduleFileCount"):
        raise RuntimeError("reusable inventory module count is inconsistent")
    occurrence_count = sum(
        len(module.get("occurrences", []))
        for module in modules
        if isinstance(module, dict)
    )
    if occurrence_count != value.get("occurrenceCount"):
        raise RuntimeError("reusable inventory occurrence count is inconsistent")
    return value


def inventory_inputs_unchanged(source_commit: str, target_commit: str) -> bool:
    if source_commit == target_commit:
        return True
    result = subprocess.run(
        ["git", "diff", "--quiet", source_commit, target_commit, "--", *INVENTORY_INPUT_PATHS],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    if result.returncode not in (0, 1):
        raise RuntimeError(
            f"cannot compare reusable inventory inputs ({result.returncode}): {result.stdout}"
        )
    return result.returncode == 0


def reuse_inventory(args: argparse.Namespace, output: Path) -> None:
    source = Path(args.reuse_inventory).expanduser().resolve()
    if not source.is_file():
        raise RuntimeError(f"reusable inventory does not exist: {source}")
    try:
        value = json.loads(source.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"cannot read reusable inventory {source}: {error}") from error
    if not isinstance(value, dict) or not isinstance(value.get("commit"), str):
        raise RuntimeError("reusable inventory has no source commit")
    source_commit = value["commit"]
    validate_reusable_inventory(value, source_commit, current_mathlib_commit())
    if not inventory_inputs_unchanged(source_commit, args.commit):
        raise RuntimeError(
            f"reusable inventory inputs changed between {source_commit} and {args.commit}"
        )
    rebound = dict(value)
    rebound["commit"] = args.commit
    # The syntax census is independent of certificate serialization.  Once its
    # declared inputs are unchanged, bind the reused census to the current
    # engine identity rather than carrying the source run's schema forward.
    rebound["engine"] = dict(cloud.ENGINE_ID)
    rebound["reusedFromCommit"] = source_commit
    rebound["reusedAt"] = utc_now()
    validate_reusable_inventory(rebound, args.commit, current_mathlib_commit())
    atomic_json(output / "inventory.json", rebound)


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
    if args.minimum_ram_gb_per_process <= 0:
        raise RuntimeError("minimum RAM per concurrent Lean process must be positive")
    if args.minimum_cpu_cores_per_process <= 0:
        raise RuntimeError("minimum effective CPU cores per Lean process must be positive")
    if args.market_refreshes < 0:
        raise RuntimeError("market refresh count cannot be negative")
    if not args.ssh_private_key.is_file() or not args.ssh_public_key.is_file():
        raise RuntimeError("Vast SSH private/public key pair is missing")
    assert_clean_commit(args.commit)
    output = Path(args.output_dir).resolve()
    if output.exists() and any(output.iterdir()):
        raise RuntimeError(f"output directory is not empty: {output}")
    output.mkdir(parents=True, exist_ok=True)
    known_hosts = output / "known_hosts"
    offers = search_offers(args, extra=max(32, args.workers * 2))
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
        "minimumRamGbPerProcess": args.minimum_ram_gb_per_process,
        "minimumEffectiveCpuCoresPerProcess": args.minimum_cpu_cores_per_process,
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

    if args.reuse_inventory:
        reuse_inventory(args, output)
        print(f"reused inventory: {args.reuse_inventory}", flush=True)
    else:
        inventory(args, output)
    archive = compressed_inventory(output)
    print(
        f"compressed inventory: {archive.stat().st_size / (1024 * 1024):.1f} MiB",
        flush=True,
    )
    instances: list[dict[str, Any]] = []
    ready_instances: list[dict[str, Any]] = []
    plan["status"] = "launching"
    atomic_json(state_path, plan)
    deadline = time.monotonic() + args.max_runtime_hours * 3600
    try:
        candidate_queue = list(offers)
        attempted_machines: set[int] = set()
        market_refreshes = 0
        candidate_index = 0

        def next_candidate_offer(active_cost: float) -> dict[str, Any]:
            nonlocal market_refreshes
            while True:
                while candidate_queue:
                    offer = candidate_queue.pop(0)
                    machine = int(offer.get("machine_id", -1))
                    if machine < 0 or machine in attempted_machines:
                        continue
                    attempted_machines.add(machine)
                    if active_cost + float(offer["dph_total"]) > args.max_total_hourly:
                        continue
                    return offer
                if market_refreshes >= args.market_refreshes:
                    raise RuntimeError(
                        "Vast offers were exhausted after bounded market refreshes"
                    )
                market_refreshes += 1
                print(
                    f"refreshing Vast fallback market "
                    f"({market_refreshes}/{args.market_refreshes})",
                    flush=True,
                )
                refreshed = replacement_offers(
                    market_offers(args), args, attempted_machines
                )
                candidate_queue.extend(refreshed)
                if not refreshed:
                    time.sleep(10)

        while len(ready_instances) < args.workers:
            batch: list[dict[str, Any]] = []
            vacancy = args.workers - len(ready_instances)
            while len(batch) < vacancy:
                active_cost = sum(
                    float(item["offer"]["dph_total"])
                    for item in ready_instances + batch
                )
                offer = next_candidate_offer(active_cost)
                try:
                    instance = create_instance(offer, candidate_index, args)
                except Exception as error:
                    print(f"offer {offer['id']} unavailable: {error}", flush=True)
                    continue
                candidate_index += 1
                instances.append(instance)
                batch.append(instance)
                plan["instances"] = instances
                atomic_json(state_path, plan)
                print(
                    f"launched candidate {instance['candidateIndex']}: contract "
                    f"{instance['contractId']} at ${offer['dph_total']:.3f}/hour",
                    flush=True,
                )
            qualified, rejected = wait_for_ssh(batch, args.boot_timeout, known_hosts)
            ready_instances.extend(qualified)
            if rejected:
                print(
                    "replacing SSH-rejected contracts: "
                    + ",".join(str(instance["contractId"]) for instance in rejected),
                    flush=True,
                )
                destroy_instances(rejected)
            print(
                f"Vast SSH qualification: {len(ready_instances)}/{args.workers} ready",
                flush=True,
            )
            atomic_json(state_path, plan)
        ready_instances = ready_instances[:args.workers]
        for index, instance in enumerate(ready_instances):
            instance["workerIndex"] = index
            instance["label"] = f"simp17-{args.commit[:8]}-{index:02d}"
        slots = {int(instance["workerIndex"]): instance for instance in ready_instances}

        def launch_replacement(worker_index: int) -> dict[str, Any]:
            nonlocal candidate_index
            while True:
                active_cost = sum(
                    float(item["offer"]["dph_total"])
                    for item in slots.values()
                    if item.get("status") != "destroyed"
                )
                offer = next_candidate_offer(active_cost)
                try:
                    replacement = create_instance(offer, candidate_index, args)
                except Exception as error:
                    print(f"offer {offer['id']} unavailable: {error}", flush=True)
                    continue
                candidate_index += 1
                replacement["workerIndex"] = worker_index
                replacement["label"] = f"simp17-{args.commit[:8]}-{worker_index:02d}"
                instances.append(replacement)
                plan["instances"] = instances
                atomic_json(state_path, plan)
                qualified, rejected = wait_for_ssh(
                    [replacement], args.boot_timeout, known_hosts
                )
                if rejected:
                    print(
                        f"replacement contract {replacement['contractId']} rejected SSH",
                        flush=True,
                    )
                    destroy_instances(rejected)
                    continue
                print(
                    f"replacement worker {worker_index}: contract "
                    f"{replacement['contractId']} at ${offer['dph_total']:.3f}/hour",
                    flush=True,
                )
                return qualified[0]

        plan["totalHourlyUsd"] = sum(
            float(instance["offer"]["dph_total"]) for instance in ready_instances
        )
        plan["maximumComputeUsd"] = plan["totalHourlyUsd"] * args.max_runtime_hours
        plan["status"] = "setting_up"
        atomic_json(state_path, plan)
        setup_executor = ThreadPoolExecutor(max_workers=args.workers)
        setup_futures = {
            setup_executor.submit(
                setup_instance, instance, args, output, known_hosts
            ): instance
            for instance in ready_instances
        }
        while setup_futures:
            if time.monotonic() >= deadline:
                plan["status"] = "timeout"
                atomic_json(state_path, plan)
                setup_executor.shutdown(wait=False, cancel_futures=True)
                working = [
                    instance for instance in slots.values()
                    if instance.get("status") == "working"
                ]
                stop_workers(working, known_hosts)
                sync_worker_states(working, known_hosts, output)
                reduce(output, args)
                return 1
            done, _ = wait(
                setup_futures,
                timeout=args.poll_seconds,
                return_when=FIRST_COMPLETED,
            )
            failed_setups: list[int] = []
            for future in done:
                instance = setup_futures.pop(future)
                worker_index = int(instance["workerIndex"])
                try:
                    future.result()
                except Exception as error:
                    print(
                        f"worker {worker_index} setup failed; replacing host: {error}",
                        flush=True,
                    )
                    destroy_instances([instance])
                    failed_setups.append(worker_index)
                else:
                    print(f"worker {worker_index} started", flush=True)

            working = [
                instance for instance in slots.values()
                if instance.get("status") == "working"
            ]
            states = sync_worker_states(working, known_hosts, output)
            completed, failed = state_progress(states)
            if working:
                print(
                    f"Vast setup/progress: {len(working)}/{args.workers} workers active, "
                    f"{completed}/{args.shard_count} shards complete, {failed} failed",
                    flush=True,
                )
            if failed:
                plan["status"] = "worker_failure"
                atomic_json(state_path, plan)
                setup_executor.shutdown(wait=False, cancel_futures=True)
                stop_workers(working, known_hosts)
                sync_worker_states(working, known_hosts, output)
                reduce(output, args)
                return 1
            for worker_index in failed_setups:
                replacement = launch_replacement(worker_index)
                slots[worker_index] = replacement
                setup_futures[
                    setup_executor.submit(
                        setup_instance,
                        replacement,
                        args,
                        output,
                        known_hosts,
                    )
                ] = replacement
            plan["instances"] = instances
            plan["totalHourlyUsd"] = sum(
                float(item["offer"]["dph_total"])
                for item in slots.values()
                if item.get("status") != "destroyed"
            )
            plan["maximumComputeUsd"] = (
                plan["totalHourlyUsd"] * args.max_runtime_hours
            )
            atomic_json(state_path, plan)
        setup_executor.shutdown(wait=True)
        ready_instances = [slots[index] for index in range(args.workers)]
        plan["status"] = "running"
        atomic_json(state_path, plan)

        while time.monotonic() < deadline:
            states = sync_worker_states(ready_instances, known_hosts, output)
            completed, failed = state_progress(states)
            print(
                f"Vast progress: {completed}/{args.shard_count} shards complete, "
                f"{failed} failed, {len(states)}/{args.workers} workers reporting",
                flush=True,
            )
            if failed:
                plan["status"] = "worker_failure"
                atomic_json(state_path, plan)
                stop_workers(ready_instances, known_hosts)
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
            stop_workers(ready_instances, known_hosts)

        sync_worker_states(ready_instances, known_hosts, output)
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
    run_parser.add_argument("--minimum-ram-gb-per-process", type=float, default=24.0)
    run_parser.add_argument("--minimum-cpu-cores-per-process", type=float, default=4.0)
    run_parser.add_argument("--shard-count", type=int, default=256)
    run_parser.add_argument("--disk-gb", type=int, default=40)
    run_parser.add_argument("--image", default="ubuntu:24.04")
    run_parser.add_argument("--ssh-private-key", default="~/.ssh/id_rsa")
    run_parser.add_argument("--ssh-public-key", default="~/.ssh/id_rsa.pub")
    run_parser.add_argument("--offer-query", default=DEFAULT_QUERY)
    run_parser.add_argument("--max-offer-hourly", type=float, default=0.50)
    run_parser.add_argument("--max-total-hourly", type=float, default=4.00)
    run_parser.add_argument("--max-runtime-hours", type=float, default=3.0)
    run_parser.add_argument("--module-timeout", type=int, default=900)
    run_parser.add_argument("--inventory-timeout", type=int, default=3600)
    run_parser.add_argument("--reuse-inventory", default="")
    run_parser.add_argument("--boot-timeout", type=int, default=180)
    run_parser.add_argument("--setup-timeout", type=int, default=1800)
    run_parser.add_argument("--poll-seconds", type=int, default=30)
    run_parser.add_argument("--market-refreshes", type=int, default=3)
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
