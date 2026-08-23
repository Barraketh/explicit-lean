#!/usr/bin/env python3
"""Run schema-16 shards concurrently on one Vast.ai worker."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import threading
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def assigned_shards(worker_index: int, worker_count: int, shard_count: int) -> list[int]:
    if worker_count <= 0 or not 0 <= worker_index < worker_count:
        raise ValueError("invalid worker assignment")
    if shard_count <= 0:
        raise ValueError("invalid shard count")
    return list(range(worker_index, shard_count, worker_count))


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def run_worker(args: argparse.Namespace) -> int:
    output = Path(args.output_dir).resolve()
    output.mkdir(parents=True, exist_ok=True)
    shards = assigned_shards(args.worker_index, args.worker_count, args.shard_count)
    state: dict[str, Any] = {
        "schema": 1,
        "kind": "simp_engine_vast_worker",
        "workerIndex": args.worker_index,
        "workerCount": args.worker_count,
        "shardCount": args.shard_count,
        "concurrency": args.concurrency,
        "startedAt": utc_now(),
        "completedAt": None,
        "status": "running",
        "assignedShards": shards,
        "inProgress": [],
        "completedShards": [],
        "failedShards": [],
        "skippedShards": [],
    }
    state_path = output / "worker-state.json"
    lock = threading.Lock()
    stop = threading.Event()
    atomic_json(state_path, state)

    def update() -> None:
        state["inProgress"] = sorted(state["inProgress"])
        state["completedShards"] = sorted(state["completedShards"])
        state["failedShards"] = sorted(state["failedShards"])
        state["skippedShards"] = sorted(state["skippedShards"])
        atomic_json(state_path, state)

    def run_shard(index: int) -> tuple[int, int | None]:
        with lock:
            if stop.is_set():
                state["skippedShards"].append(index)
                update()
                return index, None
            state["inProgress"].append(index)
            update()
        shard_output = output / "shards" / f"shard-{index:04d}"
        log_path = output / "worker-logs" / f"shard-{index:04d}.log"
        log_path.parent.mkdir(parents=True, exist_ok=True)
        command = [
            sys.executable,
            "Experiment/simp_engine_cloud.py",
            "shard",
            "--inventory", str(Path(args.inventory).resolve()),
            "--shard-index", str(index),
            "--shard-count", str(args.shard_count),
            "--module-timeout", str(args.module_timeout),
            "--stop-after-failure",
            "--output-dir", str(shard_output),
        ]
        with log_path.open("w", encoding="utf-8") as log:
            result = subprocess.run(
                command,
                cwd=ROOT,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
            )
        with lock:
            state["inProgress"].remove(index)
            if result.returncode == 0:
                state["completedShards"].append(index)
            else:
                state["failedShards"].append(index)
                stop.set()
            update()
        return index, result.returncode

    with ThreadPoolExecutor(max_workers=args.concurrency) as executor:
        futures = [executor.submit(run_shard, index) for index in shards]
        for future in as_completed(futures):
            future.result()

    state["completedAt"] = utc_now()
    state["status"] = "success" if not state["failedShards"] else "failure"
    update()
    return 0 if state["status"] == "success" else 1


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--inventory", required=True)
    result.add_argument("--worker-index", type=int, required=True)
    result.add_argument("--worker-count", type=int, required=True)
    result.add_argument("--shard-count", type=int, default=256)
    result.add_argument("--concurrency", type=int, default=4)
    result.add_argument("--module-timeout", type=int, default=900)
    result.add_argument("--output-dir", required=True)
    return result


if __name__ == "__main__":
    raise SystemExit(run_worker(parser().parse_args()))
