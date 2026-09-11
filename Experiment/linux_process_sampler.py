#!/usr/bin/env python3
"""Run one Linux command and record Python and Lean RSS separately.

The sampler is intentionally independent of campaign acceptance.  It observes
the launched process tree through /proc, writes an immutable combined log and
JSON measurement, and returns the wrapped command's exit status.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from typing import Iterable

from process_runner import run_process


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class ProcessRecord:
    pid: int
    ppid: int
    rss_bytes: int
    executable: str


def _status_fields(path: Path) -> dict[str, str]:
    fields: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        key, separator, value = line.partition(":")
        if separator:
            fields[key] = value.strip()
    return fields


def read_processes(proc_root: Path = Path("/proc")) -> list[ProcessRecord]:
    """Read a race-tolerant snapshot of Linux process identity and RSS."""
    records: list[ProcessRecord] = []
    for entry in proc_root.iterdir():
        if not entry.name.isdigit():
            continue
        try:
            fields = _status_fields(entry / "status")
            pid = int(fields["Pid"])
            ppid = int(fields["PPid"])
            rss_text = fields.get("VmRSS", "0 kB").split()
            rss_bytes = int(rss_text[0]) * 1024
            command = (entry / "cmdline").read_bytes().split(b"\0", 1)[0]
            executable = os.path.basename(os.fsdecode(command)) if command else fields.get("Name", "")
        except (FileNotFoundError, PermissionError, KeyError, ValueError, OSError):
            continue
        records.append(ProcessRecord(pid, ppid, rss_bytes, executable))
    return records


def _descendants(root_pid: int, records: Iterable[ProcessRecord]) -> list[ProcessRecord]:
    records = list(records)
    selected = {root_pid}
    changed = True
    while changed:
        changed = False
        for record in records:
            if record.ppid in selected and record.pid not in selected:
                selected.add(record.pid)
                changed = True
    return [record for record in records if record.pid in selected]


def _category(executable: str) -> str | None:
    name = executable.lower()
    if name == "lean" or name.startswith("lean-"):
        return "lean"
    if name.startswith("python") or name == "pypy" or name.startswith("pypy"):
        return "python"
    return None


class ProcessTreeSampler:
    def __init__(self, proc_root: Path = Path("/proc")) -> None:
        self.proc_root = proc_root
        self.samples = 0
        self.overall_peak = 0
        self.categories = {
            "python": {"peakAggregateRssBytes": 0, "peakSingleProcessRssBytes": 0, "observedPids": set()},
            "lean": {"peakAggregateRssBytes": 0, "peakSingleProcessRssBytes": 0, "observedPids": set()},
        }

    def observe(self, root_pid: int) -> None:
        tree = _descendants(root_pid, read_processes(self.proc_root))
        self.samples += 1
        self.overall_peak = max(self.overall_peak, sum(record.rss_bytes for record in tree))
        for category, metrics in self.categories.items():
            selected = [record for record in tree if _category(record.executable) == category]
            metrics["peakAggregateRssBytes"] = max(
                metrics["peakAggregateRssBytes"], sum(record.rss_bytes for record in selected)
            )
            metrics["peakSingleProcessRssBytes"] = max(
                metrics["peakSingleProcessRssBytes"],
                max((record.rss_bytes for record in selected), default=0),
            )
            metrics["observedPids"].update(record.pid for record in selected)

    def guard(self, root_pid: int) -> None:
        self.observe(root_pid)
        return None

    def result(self) -> dict[str, object]:
        categories = {
            name: {**metrics, "observedPids": sorted(metrics["observedPids"])}
            for name, metrics in self.categories.items()
        }
        return {
            "sampleCount": self.samples,
            "processTreePeakAggregateRssBytes": self.overall_peak,
            "categories": categories,
        }


def _exclusive_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        view = memoryview(payload)
        while view:
            view = view[os.write(descriptor, view):]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metrics", required=True)
    parser.add_argument("--log", required=True)
    parser.add_argument("--timeout", type=float, required=True)
    parser.add_argument("--interval", type=float, default=0.25)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not sys.platform.startswith("linux"):
        parser.error("linux_process_sampler requires Linux /proc")
    if not command or args.timeout <= 0 or args.interval <= 0:
        parser.error("a command and positive timeout/interval are required")
    metrics_path = Path(args.metrics).resolve()
    log_path = Path(args.log).resolve()
    if metrics_path == log_path or metrics_path.exists() or log_path.exists():
        parser.error("metrics and log paths must be distinct and unused")

    sampler = ProcessTreeSampler()
    started_wall = datetime.now(timezone.utc)
    started = time.monotonic()
    timed_out = False
    try:
        completed = run_process(
            command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=args.timeout,
            resource_guard=sampler.guard, resource_poll_interval=args.interval,
            check=False,
        )
        exit_code = completed.returncode
        output = completed.stdout or ""
    except subprocess.TimeoutExpired as error:
        timed_out = True
        exit_code = 124
        output = error.output or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
    finished_wall = datetime.now(timezone.utc)
    log_bytes = output.encode("utf-8", errors="replace")
    result = {
        "schema": 1,
        "kind": "linux_process_tree_rss_measurement",
        "command": command,
        "cwd": str(ROOT),
        "startedAt": started_wall.isoformat(),
        "finishedAt": finished_wall.isoformat(),
        "elapsedSeconds": time.monotonic() - started,
        "timeoutSeconds": args.timeout,
        "sampleIntervalSeconds": args.interval,
        "exitCode": exit_code,
        "timedOut": timed_out,
        "log": {"path": str(log_path), "sha256": hashlib.sha256(log_bytes).hexdigest()},
        "rss": sampler.result(),
    }
    _exclusive_write(log_path, log_bytes)
    _exclusive_write(metrics_path, (json.dumps(result, indent=2, sort_keys=True) + "\n").encode())
    print(json.dumps({"metrics": str(metrics_path), "log": str(log_path), "exitCode": exit_code}, sort_keys=True))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
