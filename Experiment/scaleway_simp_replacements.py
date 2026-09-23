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
import gzip
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
MAX_INITIAL_WORKERS = 8
MAX_RESULT_ARCHIVE_BYTES = 8 * 1024**3
MAX_TOTAL_ARCHIVE_BYTES = 32 * 1024**3
MAX_TAR_MEMBERS = 100_000
MAX_TAR_MEMBER_BYTES = 8 * 1024**3
MAX_TOTAL_EXTRACTED_BYTES = 32 * 1024**3
COLLECTION_DISK_RESERVE_BYTES = 4 * 1024**3
REMOTE_OPERATIONAL_RESERVE_BYTES = 16 * 1024**3
WORKER_LOG_MAX_BYTES = 64 * 1024**2
COMPLETE_MARKER_MAX_BYTES = 1024**2
REMOTE_WORKER_OUTPUT_DIRECTORY = ".worker-output"
NAME_PREFIX = "explicit-lean-simp-"
ELAN_URL = "https://github.com/leanprover/elan/releases/download/v4.2.3/elan-x86_64-unknown-linux-gnu.tar.gz"
ELAN_SHA256 = "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2"
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
ID_RE = re.compile(r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$")
SHA_RE = re.compile(r"^[0-9a-f]{64}$")
MODULE_RE = re.compile(r"^[A-Za-z0-9_.]+$")
DEFAULT_WORKER_ARGV = [
    "python3", "-B", "Experiment/simp_replacement_worker.py",
    "--database", "{database}", "--manifest", "{manifest}", "--artifacts", "{artifacts}",
]
WORKER_TEMPLATE_FIELDS = {"job_dir", "database", "manifest", "artifacts", "scratch"}


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


def module_set_sha256(modules: Sequence[str]) -> str:
    """Hash a canonical, sorted, newline-terminated module-name set."""
    if len(set(modules)) != len(modules) or any(not MODULE_RE.fullmatch(name) for name in modules):
        raise PilotError("module workset must contain unique Lean module names")
    return sha256(("\n".join(sorted(modules)) + "\n").encode("utf-8"))


def _safe_input_relative_path(value: object) -> Path:
    if type(value) is not str or not value or "\\" in value:
        raise PilotError("job input path must be a nonempty relative POSIX path")
    path = Path(value)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        raise PilotError("job input path must stay beneath its job directory")
    if path.as_posix() != value or value in {"modules.txt", "mathlib-db.sqlite3"}:
        raise PilotError("job input path is noncanonical or overlaps a standard job input")
    if path.parts[0] in {"artifacts", "scratch", REMOTE_WORKER_OUTPUT_DIRECTORY}:
        raise PilotError("immutable job inputs may not overlap a worker output directory")
    return path


def _input_tree_digest(path: Path) -> str:
    """Hash one regular file or a symlink-free directory tree deterministically."""
    if path.is_symlink():
        raise PilotError(f"job input is a symlink: {path.name}")
    try:
        mode = path.stat(follow_symlinks=False).st_mode
    except OSError as error:
        raise PilotError(f"job input is missing: {path.name}") from error
    if stat.S_ISREG(mode):
        entries: list[dict[str, str]] = [{"path": "", "kind": "file", "sha256": sha256_file(path)}]
    elif stat.S_ISDIR(mode):
        entries = []
        for parent, dirs, files in os.walk(path, topdown=True, followlinks=False):
            parent_path = Path(parent)
            dirs.sort()
            files.sort()
            for name in list(dirs):
                child = parent_path / name
                if child.is_symlink() or not stat.S_ISDIR(child.stat(follow_symlinks=False).st_mode):
                    raise PilotError(f"job input tree contains a symlink or non-directory: {name}")
                entries.append({"path": child.relative_to(path).as_posix(), "kind": "directory"})
            for name in files:
                child = parent_path / name
                if child.is_symlink() or not stat.S_ISREG(child.stat(follow_symlinks=False).st_mode):
                    raise PilotError(f"job input tree contains a symlink or non-regular file: {name}")
                entries.append({"path": child.relative_to(path).as_posix(), "kind": "file",
                                "sha256": sha256_file(child)})
        entries.sort(key=lambda entry: entry["path"])
    else:
        raise PilotError(f"job input is not a regular file or directory: {path.name}")
    encoded = json.dumps(entries, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return sha256(encoded)


def _validate_job_input_specs(value: object) -> list[dict[str, str]]:
    if not isinstance(value, list):
        raise PilotError("job inputs must be a list of path/hash objects")
    specs: list[dict[str, str]] = []
    seen: list[Path] = []
    for item in value:
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise PilotError("each job input must contain exactly path and sha256")
        relative = _safe_input_relative_path(item["path"])
        digest = item["sha256"]
        if type(digest) is not str or not SHA_RE.fullmatch(digest):
            raise PilotError("job input hash must be lowercase SHA-256")
        if any(relative == prior or relative in prior.parents or prior in relative.parents for prior in seen):
            raise PilotError("job input paths overlap")
        seen.append(relative)
        specs.append({"path": relative.as_posix(), "sha256": digest})
    if specs != sorted(specs, key=lambda item: item["path"]):
        raise PilotError("job input specifications must be sorted by path")
    return specs


def job_inputs_sha256(specs: Sequence[Mapping[str, str]]) -> str:
    encoded = json.dumps(list(specs), sort_keys=True, separators=(",", ":")).encode("utf-8")
    return sha256(encoded)


def _path_size_bytes(path: Path) -> int:
    if path.is_symlink():
        raise PilotError("job inputs may not contain symlinks")
    mode = path.stat(follow_symlinks=False).st_mode
    if stat.S_ISREG(mode):
        return path.stat(follow_symlinks=False).st_size
    if not stat.S_ISDIR(mode):
        raise PilotError("job input is not a regular file or directory")
    size = 0
    for parent, dirs, files in os.walk(path, topdown=True, followlinks=False):
        parent_path = Path(parent)
        for name in [*dirs, *files]:
            child = parent_path / name
            if child.is_symlink():
                raise PilotError("job inputs may not contain symlinks")
            child_mode = child.stat(follow_symlinks=False).st_mode
            if stat.S_ISREG(child_mode):
                size += child.stat(follow_symlinks=False).st_size
            elif not stat.S_ISDIR(child_mode):
                raise PilotError("job input tree contains a non-regular entry")
    return size


def aggregate_archive_limit_bytes(worker_count: int) -> int:
    if type(worker_count) is not int or not 2 <= worker_count <= MAX_INITIAL_WORKERS:
        raise PilotError("worker count is outside the supported archive bound")
    return min(worker_count * MAX_RESULT_ARCHIVE_BYTES, MAX_TOTAL_ARCHIVE_BYTES)


def worker_output_limit_bytes(worker_count: int) -> int:
    """Per-job extracted payload cap, including the bounded log and marker."""
    if type(worker_count) is not int or not 2 <= worker_count <= MAX_INITIAL_WORKERS:
        raise PilotError("worker count is outside the supported output bound")
    return min(MAX_TOTAL_EXTRACTED_BYTES // worker_count, MAX_TAR_MEMBER_BYTES)


def worker_output_mount_bytes(worker_count: int) -> int:
    """tmpfs cap for DB, scratch, copied artifacts and worker temporary files."""
    return worker_output_limit_bytes(worker_count) - WORKER_LOG_MAX_BYTES - COMPLETE_MARKER_MAX_BYTES


def worker_archive_limit_bytes(worker_count: int) -> int:
    return aggregate_archive_limit_bytes(worker_count) // worker_count


def worker_output_inode_limit(worker_count: int) -> int:
    if type(worker_count) is not int or not 2 <= worker_count <= MAX_INITIAL_WORKERS:
        raise PilotError("worker count is outside the supported inode bound")
    return MAX_TAR_MEMBERS // worker_count - 2  # worker.log and complete.json are outside the tmpfs


def worker_log_drain_code() -> str:
    """Python pipe sink that drains all worker output but persists at most its cap."""
    return ("import sys; p=sys.argv[1]; cap=int(sys.argv[2]); kept=0; truncated=False; f=open(p,'wb')\n"
            "while True:\n b=sys.stdin.buffer.read(65536)\n if not b: break\n n=max(0,min(len(b),cap-kept-96))\n if n: f.write(b[:n]); kept+=n\n if n<len(b): truncated=True\n"
            "if truncated: f.write(b'\\n[worker log truncated at configured 64 MiB limit]\\n')\nf.flush()\n")


def output_reserve_bytes(worker_count: int) -> int:
    return worker_count * worker_output_limit_bytes(worker_count)


def remote_output_reserve_bytes(worker_count: int) -> int:
    """Reserve tmpfs output caps, compressed results, and an operational margin."""
    return output_reserve_bytes(worker_count) + aggregate_archive_limit_bytes(worker_count) + REMOTE_OPERATIONAL_RESERVE_BYTES


def expected_remote_job_directory(checked: Mapping[str, Any]) -> str:
    if checked["generic_worker"]:
        return "/opt/explicit-lean/.lake/private/T77-error-fix-20260923/remote-jobs"
    return "/home/ubuntu/explicit-lean-simp-jobs"


def _worker_output_tree(job_dir: Path) -> tuple[int, int]:
    output = job_dir / REMOTE_WORKER_OUTPUT_DIRECTORY
    if output.is_symlink() or not output.is_dir():
        raise PilotError("worker output must be a real directory")
    size = entries = 0
    for parent, dirs, files in os.walk(output, topdown=True, followlinks=False):
        parent_path = Path(parent)
        for name in [*dirs, *files]:
            child = parent_path / name
            entries += 1
            if child.is_symlink():
                raise PilotError(f"worker output contains a symlink: {child.relative_to(output)}")
            mode = child.stat(follow_symlinks=False).st_mode
            if stat.S_ISREG(mode):
                size += child.stat(follow_symlinks=False).st_size
            elif not stat.S_ISDIR(mode):
                raise PilotError(f"worker output contains a non-regular entry: {child.relative_to(output)}")
    return size, entries


class _CappedWriter:
    """A seek-free file writer that makes the compressed archive cap hard."""
    def __init__(self, stream: Any, limit: int) -> None:
        self.stream = stream
        self.limit = limit
        self.written = 0

    def write(self, data: bytes) -> int:
        if self.written + len(data) > self.limit:
            raise PilotError("result archive exceeded its per-job compressed-size cap")
        count = self.stream.write(data)
        self.written += count
        return count

    def flush(self) -> None:
        self.stream.flush()

    def tell(self) -> int:
        return self.written


def _write_worker_archive(job_dir: Path, archive_path: Path, archive_limit: int,
                          marker_path: Path, *, diagnostic: bool = False) -> int:
    import tarfile

    output = job_dir / REMOTE_WORKER_OUTPUT_DIRECTORY
    database_path = job_dir / "mathlib-db.sqlite3" if diagnostic else output / "mathlib-db.sqlite3"
    paths = [(database_path, "mathlib-db.sqlite3"),
             (job_dir / "worker.log", "worker.log"), (marker_path, "complete.json")]
    if not diagnostic:
        paths.extend(((output / "artifacts", "artifacts"), (output / "scratch", "scratch")))
    temp = archive_path.with_name(archive_path.name + ".tmp")
    temp.unlink(missing_ok=True)
    try:
        with temp.open("wb") as raw:
            capped = _CappedWriter(raw, archive_limit)
            with gzip.GzipFile(fileobj=capped, mode="wb", mtime=0) as compressed:
                with tarfile.open(fileobj=compressed, mode="w") as archive:
                    for path, name in paths:
                        if path.is_symlink() or not path.exists():
                            raise PilotError(f"worker archive input is missing or a symlink: {name}")
                        archive.add(path, arcname=name, recursive=True)
                compressed.flush()
            raw.flush()
            os.fsync(raw.fileno())
        temp.replace(archive_path)
        return archive_path.stat().st_size
    except Exception:
        temp.unlink(missing_ok=True)
        raise


def finalize_worker_result(job_dir: Path, specs: object, worker_count: int, *,
                           commit: str, exit_code: int, argv_sha256: str,
                           inputs_sha256: str) -> dict[str, Any]:
    """Bound, authenticate, archive and publish one terminal worker result."""
    if type(exit_code) is not int or not 0 <= exit_code <= 255:
        raise PilotError("worker exit code is invalid")
    output = job_dir / REMOTE_WORKER_OUTPUT_DIRECTORY
    canonical_specs = _validate_job_input_specs(specs)
    inputs_hash = job_inputs_sha256(canonical_specs)
    if inputs_sha256 != inputs_hash or not SHA_RE.fullmatch(argv_sha256) or not COMMIT_RE.fullmatch(commit):
        raise PilotError("worker finalizer command or immutable-input identity is invalid")
    try:
        verify_job_inputs(job_dir, canonical_specs, allow_worker_outputs=True)
    except PilotError as error:
        inputs_error = str(error)
    else:
        inputs_error = ""
    marker: dict[str, Any] = {"schema": 1, "exit_code": exit_code, "commit": commit,
                              "manifest_sha256": sha256_file(job_dir / "modules.txt"),
                              "worker_argv_sha256": argv_sha256,
                              "inputs_sha256": inputs_hash, "archive_kind": "result"}
    log = job_dir / "worker.log"
    if log.is_symlink() or not log.is_file() or log.stat().st_size > WORKER_LOG_MAX_BYTES:
        marker["exit_code"] = 86
        marker["archive_kind"] = "diagnostic"
        marker["archive_error"] = "worker log missing or exceeded bound"
    marker_tmp = job_dir / "complete.json.tmp"
    marker_tmp.write_text(json.dumps(marker, sort_keys=True, separators=(",", ":")) + "\n",
                          encoding="utf-8")
    try:
        if inputs_error:
            raise PilotError("immutable input verification failed: " + inputs_error)
        if marker["archive_kind"] == "result":
            verify_worker_output(job_dir, specs, worker_count)
            marker["database_sha256"] = sha256_file(output / "mathlib-db.sqlite3")
        else:
            raise PilotError(marker["archive_error"])
    except (PilotError, OSError) as error:
        marker["exit_code"] = 86
        marker["archive_kind"] = "diagnostic"
        marker["archive_error"] = str(error)[:1000]
        marker["database_sha256"] = sha256_file(job_dir / "mathlib-db.sqlite3")
    marker_tmp.write_text(json.dumps(marker, sort_keys=True, separators=(",", ":")) + "\n",
                          encoding="utf-8")

    archive = job_dir / "result.tar.gz"
    archive_cap = worker_archive_limit_bytes(worker_count)
    operational_margin = max(128 * 1024**2, REMOTE_OPERATIONAL_RESERVE_BYTES // worker_count)
    try:
        if shutil.disk_usage(job_dir).free < archive_cap + operational_margin:
            raise PilotError("insufficient remote free space for a bounded result archive")
        _write_worker_archive(job_dir, archive, archive_cap, marker_tmp,
                              diagnostic=marker["archive_kind"] == "diagnostic")
    except (PilotError, OSError, EOFError) as error:
        archive.unlink(missing_ok=True)
        marker["exit_code"] = 86
        marker["archive_kind"] = "diagnostic"
        marker["archive_error"] = str(error)[:1000]
        marker["database_sha256"] = sha256_file(job_dir / "mathlib-db.sqlite3")
        marker_tmp.write_text(json.dumps(marker, sort_keys=True, separators=(",", ":")) + "\n",
                              encoding="utf-8")
        try:
            diagnostic_cap = min(128 * 1024**2, archive_cap)
            if shutil.disk_usage(job_dir).free < diagnostic_cap + 64 * 1024**2:
                raise PilotError("insufficient remote space for bounded diagnostic archive")
            _write_worker_archive(job_dir, archive, diagnostic_cap, marker_tmp, diagnostic=True)
        except (PilotError, OSError, EOFError):
            archive.unlink(missing_ok=True)
    marker_tmp.replace(job_dir / "complete.json")
    return marker


def verify_worker_output(job_dir: Path, specs: object, worker_count: int) -> tuple[int, int]:
    """Recheck authenticated inputs and enforce archive byte/member ceilings."""
    verify_job_inputs(job_dir, specs, allow_worker_outputs=True)
    output = job_dir / REMOTE_WORKER_OUTPUT_DIRECTORY
    size, entries = _worker_output_tree(job_dir)
    for name, bound in (("worker.log", WORKER_LOG_MAX_BYTES),
                        ("complete.json", COMPLETE_MARKER_MAX_BYTES)):
        path = job_dir / name
        if name == "complete.json" and not path.exists():
            path = job_dir / "complete.json.tmp"
        if path.is_symlink() or not path.is_file() or not stat.S_ISREG(path.stat(follow_symlinks=False).st_mode):
            raise PilotError(f"worker {name} must be a regular file")
        actual = path.stat(follow_symlinks=False).st_size
        if actual > bound:
            raise PilotError(f"worker {name} exceeds its configured bound")
        size += actual
        entries += 1
    if size > worker_output_limit_bytes(worker_count):
        raise PilotError("worker result exceeds its per-job extracted-output limit")
    if entries > worker_output_inode_limit(worker_count) + 2:
        raise PilotError("worker result exceeds its per-job archive-entry limit")
    for name in ("mathlib-db.sqlite3", "scratch", "artifacts"):
        path = output / name
        if path.is_symlink() or not (path.is_file() if name == "mathlib-db.sqlite3" else path.is_dir()):
            raise PilotError(f"worker output lacks a valid {name} entry")
    database = output / "mathlib-db.sqlite3"
    if database.stat(follow_symlinks=False).st_nlink != 1:
        raise PilotError("worker database copy must have exactly one hard link")
    if any((output / (database.name + suffix)).exists() for suffix in ("-wal", "-shm", "-journal")):
        raise PilotError("worker database has an uncheckpointed SQLite sidecar")
    return size, entries


def verify_job_inputs(job_dir: Path, specs: object, *, allow_worker_outputs: bool = False) -> str:
    """Verify immutable extra job inputs and return their authenticated manifest digest."""
    if job_dir.is_symlink() or not job_dir.is_dir():
        raise PilotError("job directory must be a real directory")
    canonical = _validate_job_input_specs(specs)
    root = job_dir.resolve()
    relative_inputs = [_safe_input_relative_path(item["path"]) for item in canonical]
    for item in canonical:
        relative = _safe_input_relative_path(item["path"])
        candidate = root / relative
        cursor = root
        for part in relative.parts:
            cursor = cursor / part
            if cursor.is_symlink():
                raise PilotError(f"job input path traverses a symlink: {item['path']}")
        resolved = candidate.resolve()
        if resolved != candidate.absolute() or root not in resolved.parents:
            raise PilotError("job input resolves outside its job directory")
        if _input_tree_digest(candidate) != item["sha256"]:
            raise PilotError(f"job input hash differs from policy: {item['path']}")
    for parent, dirs, files in os.walk(root, topdown=True, followlinks=False):
        parent_path = Path(parent)
        for name in [*dirs, *files]:
            child = parent_path / name
            relative = child.relative_to(root)
            if child.is_symlink():
                raise PilotError(f"job directory contains an unpinned symlink: {relative.as_posix()}")
            mode = child.stat(follow_symlinks=False).st_mode
            if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                raise PilotError(f"job directory contains a non-regular entry: {relative.as_posix()}")
            if relative.as_posix() in {"modules.txt", "mathlib-db.sqlite3"}:
                if not stat.S_ISREG(mode):
                    raise PilotError(f"standard job input is not a regular file: {relative.as_posix()}")
                continue
            worker_controls = {".launch-claim", "worker.pid", "launcher.log", "worker.log",
                               "complete.json", "complete.json.tmp", "result.tar.gz",
                               "result.tar.gz.tmp"}
            if allow_worker_outputs and (relative == Path(REMOTE_WORKER_OUTPUT_DIRECTORY)
                                         or Path(REMOTE_WORKER_OUTPUT_DIRECTORY) in relative.parents
                                         or relative.parts[0] in worker_controls):
                continue
            if not any(relative == item or relative in item.parents or item in relative.parents
                       for item in relative_inputs):
                raise PilotError(f"job directory contains an unpinned input: {relative.as_posix()}")
    return job_inputs_sha256(canonical)


def _worker_argv_template(value: object, *, require_scratch: bool = False) -> list[str]:
    if not isinstance(value, list) or len(value) < 4 or any(type(part) is not str or not part for part in value):
        raise PilotError("worker_argv must be a nonempty argv array")
    if value[0:2] != ["python3", "-B"]:
        raise PilotError("worker_argv must invoke python3 -B")
    script = Path(value[2])
    if (script.is_absolute() or script.as_posix() != value[2] or script.suffix != ".py"
            or not script.parts or script.parts[0] != "Experiment"
            or any(part in {".", ".."} for part in script.parts)):
        raise PilotError("worker_argv must name a repository-relative Experiment/*.py script")
    joined = "\0".join(value)
    fields = re.findall(r"\{([a-z_]+)\}", joined)
    if re.search(r"\{[^}]*\}", re.sub(r"\{[a-z_]+\}", "", joined)):
        raise PilotError("worker_argv contains a malformed template field")
    if (set(fields) - WORKER_TEMPLATE_FIELDS or fields.count("database") != 1
            or fields.count("manifest") != 1 or fields.count("scratch") > 1
            or require_scratch and fields.count("scratch") != 1):
        raise PilotError("worker_argv has unsupported fields or missing required database, manifest, or scratch paths")
    return list(value)


def expand_worker_argv(template: Sequence[str], remote_job: str) -> list[str]:
    output = remote_job + "/" + REMOTE_WORKER_OUTPUT_DIRECTORY
    values = {"job_dir": remote_job, "database": output + "/mathlib-db.sqlite3",
              "manifest": remote_job + "/modules.txt", "artifacts": output + "/artifacts",
              "scratch": output + "/scratch"}
    return [part.format_map(values) for part in template]


def worker_argv_sha256(template: Sequence[str], remote_job: str) -> str:
    encoded = json.dumps(expand_worker_argv(template, remote_job), separators=(",", ":")).encode("utf-8")
    return sha256(encoded)


def expected_job_ids(count: int) -> tuple[str, ...]:
    return tuple(f"job-{index:03d}" for index in range(count))


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
    for key, expected in {"single_host": True, "linux_x86_64": True, "public_ipv4": True}.items():
        if type(requirements.get(key)) is not type(expected) or requirements.get(key) != expected:
            raise PilotError(f"requirements.{key} does not match the one-host envelope")
    worker_count = requirements.get("worker_count")
    if type(worker_count) is not int or not 2 <= worker_count <= MAX_INITIAL_WORKERS:
        raise PilotError(f"requirements.worker_count must be between 2 and {MAX_INITIAL_WORKERS}")
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
    generic_worker = "worker_argv" in policy
    worker_argv = _worker_argv_template(policy.get("worker_argv", DEFAULT_WORKER_ARGV),
                                        require_scratch=generic_worker)
    workset: dict[str, Any] | None = None
    if generic_worker:
        raw_workset = _dict(policy.get("workset"), "workset")
        if (set(raw_workset) != {"module_count", "modules_sha256"}
                or type(raw_workset.get("module_count")) is not int or raw_workset["module_count"] < 1
                or type(raw_workset.get("modules_sha256")) is not str
                or not SHA_RE.fullmatch(raw_workset["modules_sha256"])):
            raise PilotError("generic workers require a module-count and SHA-256 pinned workset")
        workset = raw_workset
    jobs = policy.get("jobs")
    if not isinstance(jobs, list) or len(jobs) != worker_count:
        raise PilotError("policy jobs must match requirements.worker_count")
    seen: set[str] = set()
    allowed_ids = set(expected_job_ids(worker_count))
    for index, value in enumerate(jobs):
        job = _dict(value, f"jobs[{index}]")
        if job.get("id") not in allowed_ids or job["id"] in seen:
            raise PilotError("job identifiers must be unique contiguous job-NNN values")
        seen.add(job["id"])
        for key in ("directory", "manifest_sha256", "database_sha256"):
            if type(job.get(key)) is not str or not job[key].strip():
                raise PilotError(f"jobs[{index}].{key} must be explicitly set")
        if not SHA_RE.fullmatch(job["manifest_sha256"]) or not SHA_RE.fullmatch(job["database_sha256"]):
            raise PilotError("job hashes must be lowercase SHA-256 digests")
        if generic_worker or "inputs" in job:
            _validate_job_input_specs(job.get("inputs"))
    if seen != allowed_ids:
        raise PilotError("policy jobs must pin every contiguous job id")
    return {"deadline": not_after, "lifetime": lifetime, "runtime": runtime, "cost_cap_eur": cap,
            "organization_id": auth["organization_id"], "project_id": auth["project_id"], "zone": zone,
            "machine": machine, "repository": repo, "jobs": jobs, "cli_profile": profile,
            "requirements": requirements, "worker_count": worker_count, "worker_argv": worker_argv,
            "generic_worker": generic_worker, "workset": workset, "cost_source": auth["cost_source"],
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
    if "inputs" in policy_job:
        verify_job_inputs(job_dir, policy_job["inputs"])
    try:
        lines = manifest_bytes.decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        raise PilotError("modules.txt is not UTF-8") from error
    modules = [line.strip() for line in lines if line.strip()]
    if not modules or any(not MODULE_RE.fullmatch(name) for name in modules) or len(set(modules)) != len(modules):
        raise PilotError("modules.txt must contain unique Lean module names, one per line")
    return manifest, database, modules


def validate_job_root(job_root: Path, policy_jobs: Sequence[Mapping[str, Any]], *,
                      workset: Mapping[str, Any] | None = None) -> list[dict[str, Any]]:
    """Check authenticated job copies form a disjoint exact work partition."""
    if job_root.is_symlink() or not job_root.is_dir():
        raise PilotError("job root must be a real directory")
    root = job_root.resolve()
    result = []
    ids = expected_job_ids(len(policy_jobs))
    for expected_id in ids:
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
                       "manifest_sha256": sha256_file(manifest), "database_sha256": sha256_file(database),
                       "inputs": _validate_job_input_specs(item.get("inputs", [])),
                       "inputs_sha256": job_inputs_sha256(_validate_job_input_specs(item.get("inputs", []))),
                       "input_bytes": (_path_size_bytes(manifest) + _path_size_bytes(database)
                                       + sum(_path_size_bytes(directory / spec["path"])
                                             for spec in _validate_job_input_specs(item.get("inputs", []))))})
    database_stats = [item["database"].stat(follow_symlinks=False) for item in result]
    identities = {(item.st_dev, item.st_ino) for item in database_stats}
    if len(identities) != len(result):
        raise PilotError("job databases must be distinct regular files, not hard links")
    if len({item["database_sha256"] for item in result}) != 1:
        raise PilotError("job databases do not match the same approved baseline bytes")
    if workset is not None and any(_path_size_bytes(item["database"]) > worker_output_mount_bytes(len(result))
                                   for item in result):
        raise PilotError("generic-worker baseline database exceeds the per-job writable-output cap")
    assigned_sets = [set(job["modules"]) for job in result]
    for index, assigned in enumerate(assigned_sets):
        if any(assigned.intersection(other) for other in assigned_sets[index + 1:]):
            raise PilotError("job manifests overlap")
    assigned = set().union(*assigned_sets)
    if workset is not None:
        if len(assigned) != workset["module_count"] or module_set_sha256(sorted(assigned)) != workset["modules_sha256"]:
            raise PilotError("job manifests do not exactly match the policy-pinned module workset")
        job = result[0]
        uri = f"file:{job['database'].resolve().as_posix()}?mode=ro"
        try:
            con = sqlite3.connect(uri, uri=True)
            try:
                existing = {str(row[0]) for row in con.execute(
                    "SELECT DISTINCT r.module_name FROM simp_replacements AS r "
                    "JOIN modules AS m ON m.name=r.module_name")}
            finally:
                con.close()
        except sqlite3.Error as error:
            raise PilotError("job database lacks a readable simp replacement baseline") from error
        if not assigned <= existing:
            raise PilotError("policy-pinned workset includes modules absent from the job database")
        return result
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
        jobs = validate_job_root(job_root, checked["jobs"], workset=checked["workset"])
        worker_script = repo_root / checked["worker_argv"][2]
        if worker_script.is_symlink() or not worker_script.is_file():
            raise PilotError("policy-pinned worker script is not a regular file in the approved checkout")
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
                          "database_sha256": job["database_sha256"],
                          "inputs_sha256": job["inputs_sha256"],
                          "input_bytes": job["input_bytes"],
                          "worker_argv_sha256": worker_argv_sha256(
                              checked["worker_argv"], expected_remote_job_directory(checked) + "/" + job["id"])}
                         for job in jobs], "worker_count": checked["worker_count"],
                "aggregate_archive_limit_bytes": aggregate_archive_limit_bytes(checked["worker_count"]),
                "remote_output_reserve_bytes": remote_output_reserve_bytes(checked["worker_count"]),
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
        remote_job_directory = expected_remote_job_directory(checked)
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
                           "inputs_sha256": job["inputs_sha256"],
                           "worker_argv_sha256": worker_argv_sha256(
                               checked["worker_argv"], remote_job_directory + "/" + job["id"]),
                           "phase": "pending"}
                          for job in validate_job_root(job_root, checked["jobs"], workset=checked["workset"])],
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
                                "tags.0=explicit-lean-simp-pilot",
                                f"tags.1=workers-{checked['worker_count']}", "--wait"], policy=checked, timeout=300)
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

    def _remote_free_bytes(self, state: Mapping[str, Any], remote_path: str,
                           checked: Mapping[str, Any]) -> int:
        if remote_path != expected_remote_job_directory(checked):
            raise PilotError("remote disk check path is not the pinned jobs directory")
        command = ("set -eu; n=$(df --output=avail -B1 " + shlex.quote(remote_path)
                   + " | tail -n 1 | tr -d '[:space:]'); case \"$n\" in ''|*[!0-9]*) exit 42;; esac; "
                   "printf 'REMOTE_FREE_BYTES=%s\\n' \"$n\"")
        result = self._ssh(state, "sh", "-lc", shlex.quote(command), timeout=60)
        if result.returncode:
            raise PilotError("remote disk free-space check failed")
        match = re.fullmatch("REMOTE_FREE_BYTES=([0-9]+)\\n?", result.stdout)
        if match is None:
            raise PilotError("remote disk free-space response is malformed")
        return int(match.group(1))

    @staticmethod
    def _remote_input_check(remote_job: str, specs: Sequence[Mapping[str, str]], *,
                            allow_worker_outputs: bool = False) -> str:
        artifact_option = ", allow_worker_outputs=True" if allow_worker_outputs else ""
        snippet = ("import json,sys; from pathlib import Path; "
                   "from Experiment.scaleway_simp_replacements import verify_job_inputs; "
                   "verify_job_inputs(Path(sys.argv[1]), json.loads(sys.argv[2])" + artifact_option + ")")
        encoded_specs = json.dumps(list(specs), sort_keys=True, separators=(",", ":"))
        return ("cd /opt/explicit-lean && python3 -B -c " + shlex.quote(snippet) + " " + shlex.quote(remote_job) + " "
                + shlex.quote(encoded_specs))

    @staticmethod
    def _remote_output_check(remote_job: str, specs: Sequence[Mapping[str, str]], worker_count: int) -> str:
        snippet = ("import json,sys; from pathlib import Path; "
                   "from Experiment.scaleway_simp_replacements import verify_worker_output; "
                   "verify_worker_output(Path(sys.argv[1]), json.loads(sys.argv[2]), int(sys.argv[3]))")
        encoded_specs = json.dumps(list(specs), sort_keys=True, separators=(",", ":"))
        return ("cd /opt/explicit-lean && python3 -B -c " + shlex.quote(snippet) + " " + shlex.quote(remote_job) + " "
                + shlex.quote(encoded_specs) + " " + str(worker_count))

    def _launch_worker_once(self, state: Mapping[str, Any], job: Mapping[str, Any],
                            policy_job: Mapping[str, Any], checked: Mapping[str, Any],
                            worker_timeout: int, commit: str, launch_token: str) -> subprocess.CompletedProcess[str]:
        """Atomically claim a job before launch; an existing claim is never relaunched."""
        remote_job = state["remote_job_directory"] + "/" + job["id"]
        argv = expand_worker_argv(checked["worker_argv"], remote_job)
        argv_digest = worker_argv_sha256(checked["worker_argv"], remote_job)
        inputs = _validate_job_input_specs(policy_job.get("inputs", []))
        inputs_digest = job_inputs_sha256(inputs)
        command = shlex.join(argv)
        input_check = self._remote_input_check(remote_job, inputs)
        baseline_check = ("test \"$(sha256sum " + remote_job + "/modules.txt | awk '{print $1}')\" = " +
                          shlex.quote(str(job["manifest_sha256"])) + "; test \"$(sha256sum " + remote_job +
                          "/mathlib-db.sqlite3 | awk '{print $1}')\" = " + shlex.quote(str(job["database_sha256"])) +
                          "; " + input_check)
        out = remote_job + "/" + REMOTE_WORKER_OUTPUT_DIRECTORY
        output_size = worker_output_mount_bytes(checked["worker_count"])
        output_inodes = MAX_TAR_MEMBERS // checked["worker_count"]
        specs_json = json.dumps(inputs, sort_keys=True, separators=(",", ":"))
        drain = worker_log_drain_code()
        finalize = ("python3 -B Experiment/scaleway_simp_replacements.py finalize-worker "
                    "--job-dir \"$d\" --inputs-json " + shlex.quote(specs_json) +
                    " --worker-count " + str(checked["worker_count"]) + " --commit " + shlex.quote(commit) +
                    " --exit-code \"$rc\" --argv-sha256 " + shlex.quote(argv_digest) +
                    " --inputs-sha256 " + shlex.quote(inputs_digest))
        sources = " ".join(shlex.quote(remote_job + "/" + Path(item["path"]).as_posix()) for item in inputs)
        copy_inputs = ("for source in " + sources + "; do if test -d \"$source\"; then "
                       "cp -a \"$source/.\" \"$out/artifacts/\" || setup_rc=1; "
                       "elif test -f \"$source\"; then cp \"$source\" \"$out/artifacts/\" || setup_rc=1; fi; done; ")
        worker = "".join([
            "set +e; d=" + shlex.quote(remote_job) + "; out=" + shlex.quote(out) + "; rc=86; ",
            "mkdir -p \"$out\"; uid=$(id -u); gid=$(id -g); ",
            "if sudo mount -t tmpfs -o size=" + str(output_size) + ",nr_inodes=" + str(output_inodes) +
            ",mode=0770,uid=$uid,gid=$gid,nosuid,nodev tmpfs \"$out\"; then ",
            "setup_rc=0; mkdir -p \"$out/tmp\" \"$out/scratch\" \"$out/artifacts\" || setup_rc=1; ",
            "cp \"$d/mathlib-db.sqlite3\" \"$out/mathlib-db.sqlite3\" || setup_rc=1; ", copy_inputs,
            "if test \"$setup_rc\" = 0 && ", baseline_check, "; then ",
            "export TMPDIR=\"$out/tmp\" TMP=\"$out/tmp\" TEMP=\"$out/tmp\"; ",
            "timeout --signal=TERM --kill-after=30 " + str(worker_timeout) + " " + command,
            " 2>&1 | python3 -B -c " + shlex.quote(drain) + " \"$d/worker.log\" " +
            str(WORKER_LOG_MAX_BYTES) + "; rc=${PIPESTATUS[0]}; ",
            "else printf 'worker setup or pinned input verification failed\\n' > \"$d/worker.log\"; rc=86; fi; ",
            "else printf 'per-job bounded tmpfs mount failed\\n' > \"$d/worker.log\"; rc=86; fi; ",
            finalize, "; sudo umount \"$out\" 2>/dev/null || true",
        ])
        script = ("set -eu; d=" + shlex.quote(remote_job) + "; token=" + shlex.quote(launch_token) + "; "
                  "if test -f \"$d/complete.json\"; then printf 'COMPLETE\\n'; exit 0; fi; "
                  "if ! mkdir \"$d/.launch-claim\" 2>/dev/null; then "
                  "p=$(cat \"$d/worker.pid\" 2>/dev/null || true); "
                  "case \"$p\" in ''|*[!0-9]*) printf 'AMBIGUOUS\\n'; exit 42;; esac; "
                  "expected=$(cat \"$d/.launch-claim/token\" 2>/dev/null || true); "
                  "if test \"$expected\" = \"$token\" && kill -0 \"$p\" 2>/dev/null "
                  "&& tr '\\000' '\\n' < \"/proc/$p/environ\" | grep -Fx \"EXPLICIT_LEAN_WORKER_TOKEN=$token\" >/dev/null "
                  "&& tr '\\000' '\\n' < \"/proc/$p/environ\" | grep -Fx " +
                  shlex.quote("EXPLICIT_LEAN_WORKER_ARGV_SHA256=" + argv_digest) + " >/dev/null "
                  "&& tr '\\000' ' ' < \"/proc/$p/cmdline\" | grep -F -- " + shlex.quote(command) + " >/dev/null; "
                  "then printf 'RUNNING %s\\n' \"$p\"; exit 0; fi; "
                  "printf 'AMBIGUOUS\\n'; exit 42; fi; "
                  "printf '%s\\n' \"$token\" > \"$d/.launch-claim/token.tmp\"; "
                  "mv \"$d/.launch-claim/token.tmp\" \"$d/.launch-claim/token\"; "
                  "cd /opt/explicit-lean; . \"$HOME/.elan/env\"; "
                  "EXPLICIT_LEAN_WORKER_TOKEN=\"$token\" EXPLICIT_LEAN_WORKER_ARGV_SHA256=" +
                  shlex.quote(argv_digest) + " nohup bash -lc " + shlex.quote(worker) +
                  " > \"$d/launcher.log\" 2>&1 < /dev/null & "
                  "p=$!; printf '%s\\n' \"$p\" > \"$d/worker.pid.tmp\"; "
                  "mv \"$d/worker.pid.tmp\" \"$d/worker.pid\"; printf 'RUNNING %s\\n' \"$p\"")
        return self._ssh(state, "sh", "-lc", shlex.quote(script), timeout=60)

    @staticmethod
    def _bootstrap_resume_is_safe(state: Mapping[str, Any]) -> bool:
        """Only retry bootstrap while state proves dispatch has not begun."""
        if state.get("phase") != "bootstrap-started":
            return False
        allowed_state_keys = {
            "schema", "phase", "server_id", "name", "remote_job_directory", "zone", "project_id",
            "organization_id", "created_at", "deadline", "lifetime_seconds", "worker_runtime_seconds",
            "policy_sha256", "preflight", "local_image_id", "ssh_key_id", "ssh_public_key_sha256", "jobs",
            "mutation", "public_ip_id", "public_ip_address", "volume_ids", "guest_poweroff_watchdog_armed",
            "host_ttl_remaining_seconds", "bootstrap_started_at", "supervisor_report",
        }
        if set(state) - allowed_state_keys:
            return False
        required_state_keys = allowed_state_keys - {"supervisor_report"}
        if not required_state_keys <= set(state):
            return False
        if state.get("guest_poweroff_watchdog_armed") is not True:
            return False
        if type(state.get("host_ttl_remaining_seconds")) is not int or state["host_ttl_remaining_seconds"] <= 0:
            return False
        if type(state.get("bootstrap_started_at")) is not str:
            return False
        report = state.get("supervisor_report")
        if report is not None:
            if report == {"supervisor": "started"}:
                pass  # Legacy finally-checkpoint written before the report was finalized.
            elif (not isinstance(report, dict)
                  or set(report) - {"supervisor", "error", "elapsed_seconds", "complete",
                                    "cleanup_error", "state_checkpoint_error"}
                  or not {"supervisor", "error", "elapsed_seconds", "complete"} <= set(report)
                  or report.get("supervisor") != "started" or report.get("complete") is not False
                  or type(report.get("error")) is not str
                  or type(report.get("elapsed_seconds")) is not int or report["elapsed_seconds"] < 0
                  or any(type(report.get(key)) is not str for key in ("cleanup_error", "state_checkpoint_error")
                         if key in report)):
                return False
        jobs = state.get("jobs")
        if not isinstance(jobs, list) or not 2 <= len(jobs) <= MAX_INITIAL_WORKERS:
            return False
        job_ids = [job.get("id") for job in jobs if isinstance(job, dict)]
        if (len(job_ids) != len(jobs) or any(type(job_id) is not str for job_id in job_ids)
                or job_ids != list(expected_job_ids(len(jobs)))):
            return False
        base_job_keys = {"id", "manifest_sha256", "database_sha256", "module_count", "phase"}
        pinned_job_keys = base_job_keys | {"inputs_sha256", "worker_argv_sha256"}
        return all(isinstance(job, dict) and frozenset(job) in {frozenset(base_job_keys), frozenset(pinned_job_keys)}
                   and job.get("phase") == "pending" for job in jobs)

    @staticmethod
    def _parse_systemd_utc_timestamp(value: object) -> datetime:
        if type(value) is not str:
            raise PilotError("systemd timer deadline is missing")
        match = re.fullmatch(r"(Mon|Tue|Wed|Thu|Fri|Sat|Sun) (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}) UTC", value)
        if match is None:
            raise PilotError("systemd timer deadline has an unsupported timestamp format")
        try:
            parsed = datetime.strptime(match.group(2), "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
        except ValueError as error:
            raise PilotError("systemd timer deadline is malformed") from error
        if parsed.strftime("%a") != match.group(1):
            raise PilotError("systemd timer weekday does not match its date")
        return parsed

    def _reconcile_dispatch(self, state: dict[str, Any], policy: Mapping[str, Any],
                            checked: Mapping[str, Any]) -> dict[str, Any]:
        """Resume a partial dispatch without duplicating any potentially launched worker."""
        remote = state.get("remote_job_directory")
        if remote != expected_remote_job_directory(checked):
            raise PilotError("saved remote jobs directory is invalid")
        jobs = {item["id"]: item for item in state.get("jobs", [])}
        ids = expected_job_ids(len(jobs))
        if not 2 <= len(jobs) <= MAX_INITIAL_WORKERS or set(jobs) != set(ids):
            raise PilotError("saved dispatch job set is incomplete")
        created = datetime.fromisoformat(state["created_at"]).astimezone(timezone.utc)
        hard_end = min(created + timedelta(seconds=checked["lifetime"]), checked["deadline"])
        worker_end = datetime.fromisoformat(state["worker_started_at"]).astimezone(timezone.utc) + timedelta(
            seconds=int(state["worker_timeout_seconds"]))
        now = self.now().astimezone(timezone.utc)
        worker_timeout = int((min(hard_end, worker_end) - now).total_seconds())
        policy_jobs = {str(item["id"]): item for item in checked["jobs"]}
        if set(policy_jobs) != set(ids):
            raise PilotError("policy and saved dispatch job sets differ")
        commit = str(_dict(policy.get("repository"), "repository")["commit"])
        for job_id in ids:
            if not jobs[job_id].get("launch_token"):
                jobs[job_id] = {**jobs[job_id], "launch_token": uuid.uuid4().hex}
                state["jobs"] = [jobs[key] for key in ids]
                self._save(state)
            launch_token = jobs[job_id]["launch_token"]
            if not re.fullmatch(r"[0-9a-f]{32}", str(launch_token)):
                raise PilotError(f"{job_id} launch token is malformed")
            remote_job = remote + "/" + job_id
            argv = expand_worker_argv(checked["worker_argv"], remote_job)
            argv_digest = worker_argv_sha256(checked["worker_argv"], remote_job)
            worker_command = shlex.join(argv)
            status_shell = ("set -eu; d=" + shlex.quote(remote_job) + "; "
                            "if test -f \"$d/complete.json\"; then printf 'COMPLETE\\t'; cat \"$d/complete.json\"; "
                            "elif test -d \"$d/.launch-claim\"; then p=$(cat \"$d/worker.pid\" 2>/dev/null || true); "
                            "token=$(cat \"$d/.launch-claim/token\" 2>/dev/null || true); expected=EXPECTED_TOKEN; "
                            "case \"$p\" in ''|*[!0-9]*) printf 'AMBIGUOUS\\n';; *) "
                            "if test \"$token\" = \"$expected\" && kill -0 \"$p\" 2>/dev/null "
                            "&& tr '\\000' '\\n' < \"/proc/$p/environ\" | grep -Fx \"EXPLICIT_LEAN_WORKER_TOKEN=$expected\" >/dev/null "
                            "&& tr '\\000' '\\n' < \"/proc/$p/environ\" | grep -Fx " +
                            shlex.quote("EXPLICIT_LEAN_WORKER_ARGV_SHA256=" + argv_digest) + " >/dev/null "
                            "&& tr '\\000' ' ' < \"/proc/$p/cmdline\" | grep -F -- " +
                            shlex.quote(worker_command) + " >/dev/null; "
                            "then printf 'RUNNING\\t%s\\n' \"$p\"; "
                            "else printf 'AMBIGUOUS\\n'; fi;; esac; "
                            "elif test -e \"$d/worker.pid\" || test -e \"$d/complete.json.tmp\" "
                            "|| test -e \"$d/result.tar.gz.tmp\" || test -e \"$d/result.tar.gz\"; then printf 'AMBIGUOUS\\n'; "
                            "else printf 'NOT_LAUNCHED\\n'; fi")
            command = status_shell.replace("EXPECTED_TOKEN", shlex.quote(str(launch_token)))
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
                launched = self._launch_worker_once(state, jobs[job_id], policy_jobs[job_id], checked,
                                                    worker_timeout, commit, str(launch_token))
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
                expected_argv_sha256 = worker_argv_sha256(checked["worker_argv"], remote + "/" + job_id)
                expected_inputs_sha256 = job_inputs_sha256(_validate_job_input_specs(
                    policy_jobs[job_id].get("inputs", [])))
                generic_marker_mismatch = checked["generic_worker"] and (
                    marker.get("worker_argv_sha256") != expected_argv_sha256
                    or marker.get("inputs_sha256") != expected_inputs_sha256)
                if (marker.get("commit") != commit or marker.get("manifest_sha256") != jobs[job_id].get("manifest_sha256")
                        or type(marker.get("exit_code")) is not int or not re.fullmatch(r"[0-9a-f]{64}", str(marker.get("database_sha256")))):
                    raise PilotError(f"{job_id} completion marker does not match its pinned job")
                if generic_marker_mismatch:
                    raise PilotError(f"{job_id} completion marker does not authenticate its worker command and inputs")
                jobs[job_id] = {**jobs[job_id], "phase": "finished" if marker["exit_code"] == 0 else "failed",
                                "exit_code": marker["exit_code"], "database_result_sha256": marker["database_sha256"]}
            else:
                state.update({"phase": "dispatch-failed", "jobs": [jobs[key] for key in ids],
                              "dispatch_error": f"{job_id} launch state is ambiguous; refusing to start another worker"})
                self._save(state)
                raise PilotError(state["dispatch_error"])
            state["jobs"] = [jobs[key] for key in ids]
            self._save(state)
        phases = [jobs[key]["phase"] for key in ids]
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
        jobs = validate_job_root(job_root, checked["jobs"], workset=checked["workset"])
        created = datetime.fromisoformat(state["created_at"])
        now = self.now().astimezone(timezone.utc)
        age = (now - created.astimezone(timezone.utc)).total_seconds()
        if age >= checked["lifetime"] or now >= checked["deadline"]:
            raise PilotError("host TTL or authorization deadline reached")
        if state.get("phase") != "created" and not self._bootstrap_resume_is_safe(state):
            raise PilotError("worker dispatch may occur only once per server")
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
        watchdog_unit = f"explicit-lean-simp-ttl-{state['server_id']}"
        if state.get("guest_poweroff_watchdog_armed") is True:
            previous_ttl = state.get("host_ttl_remaining_seconds")
            if type(previous_ttl) is not int or previous_ttl <= 0 or ttl_remaining > previous_ttl:
                raise PilotError("saved guest TTL watchdog budget is inconsistent with remaining host TTL")
            expected_deadline = min(checked["deadline"], created.astimezone(timezone.utc)
                                    + timedelta(seconds=checked["lifetime"]))
            if parse_utc(state.get("deadline"), "state.deadline") != expected_deadline:
                raise PilotError("saved host deadline differs from the immutable policy TTL")
            timer = self._ssh(state, "systemctl", "show", "explicit-lean-simp-pilot-ttl.timer",
                              "--property=ActiveState", "--property=NextElapseUSecRealtime", timeout=60)
            if timer.returncode:
                raise PilotError("persistent guest TTL timer could not be verified")
            timer_properties: dict[str, str] = {}
            for line in timer.stdout.splitlines():
                key, separator, value = line.partition("=")
                if not separator or key not in {"ActiveState", "NextElapseUSecRealtime"} or key in timer_properties:
                    raise PilotError("persistent guest TTL timer response is malformed")
                timer_properties[key] = value
            if set(timer_properties) != {"ActiveState", "NextElapseUSecRealtime"} or timer_properties["ActiveState"] != "active":
                raise PilotError("persistent guest TTL timer is not active")
            timer_deadline = self._parse_systemd_utc_timestamp(timer_properties["NextElapseUSecRealtime"])
            if timer_deadline <= now or timer_deadline > expected_deadline:
                raise PilotError("persistent guest TTL timer does not expire within the immutable policy deadline")
        else:
            watchdog = self._ssh(state, "sudo", "systemd-run", f"--unit={watchdog_unit}",
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
                    "curl --fail --location --silent --show-error " + ELAN_URL + " -o /tmp/elan.tar.gz; " \
                    "echo " + ELAN_SHA256 + "'  /tmp/elan.tar.gz' | sha256sum -c -; " \
                    "tar -xzf /tmp/elan.tar.gz -C /tmp elan-init; /tmp/elan-init -y --default-toolchain none; " \
                    ". \"$HOME/.elan/env\"; cd /opt/explicit-lean; lake --no-cache exe cache get; " \
                    "lake build ExplicitLean.SimpTrace ExplicitLean.ExplicitRw; " \
                    "test -s .lake/build/lib/lean/ExplicitLean/SimpTrace.olean; " \
                    "test -s .lake/build/lib/lean/ExplicitLean/ExplicitRw.olean"
        state.update({"phase": "bootstrap-started", "bootstrap_started_at": now.isoformat()}); self._save(state)
        boot = self._ssh(state, "sh", "-lc", shlex.quote(bootstrap), timeout=min(1800, checked["runtime"]))
        if boot.returncode:
            raise PilotError(f"remote pinned checkout/dependency bootstrap failed (exit {boot.returncode})")
        remote = state.get("remote_job_directory")
        if remote != expected_remote_job_directory(checked):
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
        if checked["generic_worker"]:
            # Bootstrap may take minutes; rehash the exact upload tree immediately
            # before sizing it so the remote-space estimate does not rely only on
            # the earlier preflight snapshot.
            jobs = validate_job_root(job_root, checked["jobs"], workset=checked["workset"])
            uploaded_bytes = sum(job["input_bytes"] for job in jobs)
            reserve = remote_output_reserve_bytes(checked["worker_count"])
            free_before_upload = self._remote_free_bytes(state, remote, checked)
            if free_before_upload < uploaded_bytes + reserve:
                raise PilotError("remote free disk is below uploaded inputs plus the bounded worker/result reserve")
        target = f"{policy.get('login_user', 'ubuntu')}@{address}:{remote}/"
        scp_base = ["scp", "-r", "-i", str(Path(machine["ssh_identity_file"]).expanduser()), "-o", "BatchMode=yes",
                    "-o", "StrictHostKeyChecking=yes", "-o", f"UserKnownHostsFile={machine['known_hosts_file']}"]
        copied = self._run([*scp_base, *(str(job["directory"]) for job in jobs), target], min(600, checked["runtime"]))
        if copied.returncode:
            raise PilotError("job transfer failed")
        if checked["generic_worker"] and self._remote_free_bytes(state, remote, checked) < remote_output_reserve_bytes(checked["worker_count"]):
            raise PilotError("remote free disk fell below the bounded worker/result reserve after upload")
        for job in jobs:
            remote_job = remote + "/" + job["id"]
            verify = ("set -eu; test \"$(sha256sum " + remote_job + "/modules.txt | awk '{print $1}')\" = " +
                      shlex.quote(job["manifest_sha256"]) + "; test \"$(sha256sum " + remote_job +
                      "/mathlib-db.sqlite3 | awk '{print $1}')\" = " + shlex.quote(job["database_sha256"]) + "; " +
                      self._remote_input_check(remote_job, job["inputs"]))
            checked_remote = self._ssh(state, "sh", "-lc", shlex.quote(verify), timeout=60)
            if checked_remote.returncode:
                raise PilotError(f"uploaded {job['id']} input hashes differ from policy")
            if checked["generic_worker"]:
                readonly_paths = [remote_job + "/modules.txt", remote_job + "/mathlib-db.sqlite3"]
                readonly_paths.extend(remote_job + "/" + Path(item["path"]).as_posix()
                                      for item in job["inputs"])
                chmod = "chmod a-w " + " ".join(shlex.quote(path) for path in readonly_paths)
                readonly_trees = [shlex.quote(remote_job + "/" + Path(item["path"]).as_posix())
                                  for item in job["inputs"]
                                  if (Path(job["directory"]) / item["path"]).is_dir()]
                if readonly_trees:
                    chmod += " && chmod -R a-w " + " ".join(readonly_trees)
                readonly = self._ssh(state, "sh", "-lc", shlex.quote(chmod), timeout=60)
                if readonly.returncode:
                    raise PilotError(f"uploaded {job['id']} immutable inputs could not be made read-only")
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
                                "inputs_sha256": item["inputs_sha256"],
                                "worker_argv_sha256": worker_argv_sha256(
                                    checked["worker_argv"], remote + "/" + item["id"]),
                                "phase": "starting"} for item in state["jobs"]]})
        self._save(state)
        return self._reconcile_dispatch(state, checked, checked)

    def poll_workers(self) -> dict[str, Any]:
        state, policy = self._existing_context()
        checked = validate_policy(policy, self.now())
        if state.get("phase") not in {"workers-running", "workers-finished", "workers-failed"}:
            raise PilotError("worker status requires dispatched jobs")
        remote = state.get("remote_job_directory")
        if remote != expected_remote_job_directory(checked):
            raise PilotError("saved remote jobs directory is invalid")
        ids = expected_job_ids(checked["worker_count"])
        if [item.get("id") for item in state.get("jobs", [])] != list(ids):
            raise PilotError("saved worker job set differs from policy")
        command = "set -eu; for j in " + " ".join(ids) + "; do d=" + remote + "/$j; if test -f \"$d/complete.json\"; then printf '%s\\t' \"$j\"; cat \"$d/complete.json\"; else printf '%s\\tRUNNING\\n' \"$j\"; fi; done"
        result = self._ssh(state, "sh", "-lc", shlex.quote(command), timeout=60)
        if result.returncode:
            raise PilotError("worker status poll failed")
        observed: dict[str, str] = {}
        for line in result.stdout.splitlines():
            parts = line.split("\t", 1)
            if len(parts) != 2 or parts[0] not in ids or parts[0] in observed:
                raise PilotError("worker status response is malformed")
            observed[parts[0]] = parts[1]
        if set(observed) != set(ids):
            raise PilotError("worker status response is incomplete")
        statuses = []
        policy_jobs = {item["id"]: item for item in checked["jobs"]}
        for item in state["jobs"]:
            text = observed[item["id"]]
            if text == "RUNNING":
                statuses.append({**item, "phase": "running"})
            else:
                try:
                    marker = json.loads(text)
                except json.JSONDecodeError as error:
                    raise PilotError("worker completion marker is invalid") from error
                if (marker.get("commit") != policy["repository"]["commit"]
                        or type(marker.get("exit_code")) is not int
                        or not SHA_RE.fullmatch(str(marker.get("database_sha256")))):
                    raise PilotError("worker completion marker identity is invalid")
                if checked["generic_worker"] and (
                        marker.get("archive_kind") not in {"result", "diagnostic"}
                        or marker.get("archive_kind") == "diagnostic" and marker["exit_code"] == 0):
                    raise PilotError("worker completion marker has an invalid result/diagnostic classification")
                if checked["generic_worker"]:
                    expected_argv = worker_argv_sha256(
                        checked["worker_argv"], remote + "/" + item["id"])
                    expected_inputs = job_inputs_sha256(_validate_job_input_specs(
                        policy_jobs[item["id"]].get("inputs", [])))
                    if (marker.get("manifest_sha256") != item.get("manifest_sha256")
                            or marker.get("worker_argv_sha256") != expected_argv
                            or marker.get("inputs_sha256") != expected_inputs):
                        raise PilotError("worker completion marker does not authenticate its inputs and command")
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
        checked = validate_policy(policy, self.now())
        ids = expected_job_ids(checked["worker_count"])
        if state.get("phase") not in {"workers-finished", "workers-failed"}:
            raise PilotError("collection requires every worker to finish")
        if [item.get("id") for item in state.get("jobs", [])] != list(ids):
            raise PilotError("saved worker job set differs from policy")
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
        if remote_root != expected_remote_job_directory(checked):
            raise PilotError("saved remote jobs directory is invalid")
        output_dir.parent.mkdir(parents=True, exist_ok=True)
        size_command = ("set -eu; for j in " + " ".join(ids) + "; do f=" + remote_root +
                        "/$j/result.tar.gz; if test -f \"$f\"; then printf '%s\\t%s\\n' \"$j\" "
                        "\"$(stat -c %s \"$f\")\"; else printf '%s\\tMISSING\\n' \"$j\"; fi; done")
        size_result = self._ssh(state, "sh", "-lc", shlex.quote(size_command), timeout=60)
        if size_result.returncode:
            raise PilotError("remote result archive sizing failed")
        remote_sizes: dict[str, int] = {}
        missing_archives: set[str] = set()
        for line in size_result.stdout.splitlines():
            parts = line.split("\t")
            if len(parts) != 2 or parts[0] not in ids or parts[0] in remote_sizes or parts[0] in missing_archives:
                raise PilotError("remote result archive sizes are malformed")
            if parts[1] == "MISSING":
                missing_archives.add(parts[0])
            elif parts[1].isdigit():
                remote_sizes[parts[0]] = int(parts[1])
            else:
                raise PilotError("remote result archive size is malformed")
        if set(remote_sizes) | missing_archives != set(ids):
            raise PilotError("remote result archive size list is incomplete")
        aggregate_archive_limit = aggregate_archive_limit_bytes(checked["worker_count"])
        per_job_archive_limit = worker_archive_limit_bytes(checked["worker_count"])
        if (any(size <= 0 or size > per_job_archive_limit for size in remote_sizes.values())
                or sum(remote_sizes.values()) > aggregate_archive_limit):
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
            local_tar = out / "result.tar.gz"
            free_for_extract = shutil.disk_usage(output_dir.parent).free
            if free_for_extract < MAX_TOTAL_EXTRACTED_BYTES + COLLECTION_DISK_RESERVE_BYTES:
                raise PilotError("local free disk fell below the bounded extraction reserve")
            import tarfile
            extracted: list[Path] = []
            if job_id in missing_archives:
                remote_base = f"{login}@{address}:{remote_root}/{job_id}/"
                diagnostic_sources = [remote_base + name for name in
                                      ("mathlib-db.sqlite3", "worker.log", "complete.json")]
                proc = self._run(["scp", "-i", str(Path(machine["ssh_identity_file"]).expanduser()),
                                  "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes",
                                  "-o", f"UserKnownHostsFile={machine['known_hosts_file']}",
                                  *diagnostic_sources, str(out)], 300)
                if proc.returncode:
                    raise PilotError(f"{job_id} bounded diagnostic transfer failed")
                marker = _read_json(out / "complete.json", f"{job_id} completion marker")
                expected_argv = worker_argv_sha256(checked["worker_argv"], remote_root + "/" + job_id)
                expected_inputs = job_inputs_sha256(_validate_job_input_specs(spec.get("inputs", [])))
                expected_exit = next(item.get("exit_code") for item in state["jobs"] if item["id"] == job_id)
                if (marker.get("archive_kind") != "diagnostic" or marker.get("exit_code") == 0
                        or marker.get("schema") != 1 or type(marker.get("exit_code")) is not int
                        or marker.get("exit_code") != expected_exit
                        or marker.get("commit") != policy["repository"]["commit"]
                        or marker.get("manifest_sha256") != spec["manifest_sha256"]
                        or marker.get("worker_argv_sha256") != expected_argv
                        or marker.get("inputs_sha256") != expected_inputs
                        or marker.get("database_sha256") != sha256_file(out / "mathlib-db.sqlite3")
                        or sha256_file(out / "mathlib-db.sqlite3") != spec["database_sha256"]
                        ):
                    raise PilotError(f"{job_id} no-archive diagnostic did not authenticate its baseline")
                log_size = (out / "worker.log").stat().st_size
                marker_size = (out / "complete.json").stat().st_size
                if log_size > WORKER_LOG_MAX_BYTES or marker_size > COMPLETE_MARKER_MAX_BYTES:
                    raise PilotError(f"{job_id} no-archive diagnostic exceeded its transfer bounds")
                extracted = [out / name for name in ("mathlib-db.sqlite3", "worker.log", "complete.json")]
                digest = sha256_file(out / "mathlib-db.sqlite3")
                file_hashes.update({f"{job_id}/{path.name}": sha256_file(path) for path in extracted})
                job_results.append({"id": job_id, "exit_code": marker["exit_code"],
                                    "database_sha256": digest, "archive_sha256": None,
                                    "artifact_file_hashes": {}, "archive_kind": "diagnostic"})
                total_extracted += sum(path.stat().st_size for path in extracted)
                if total_extracted > MAX_TOTAL_EXTRACTED_BYTES:
                    raise PilotError("diagnostic collection exceeded the cumulative extraction bound")
                continue
            remote_tar = f"{login}@{address}:{remote_root}/{job_id}/result.tar.gz"
            proc = self._run(["scp", "-i", str(Path(machine["ssh_identity_file"]).expanduser()),
                              "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes",
                              "-o", f"UserKnownHostsFile={machine['known_hosts_file']}", remote_tar, str(local_tar)], 300)
            if proc.returncode:
                raise PilotError(f"{job_id} result transfer failed")
            actual_archive_size = local_tar.stat().st_size
            if actual_archive_size <= 0 or actual_archive_size > per_job_archive_limit or actual_archive_size != remote_sizes[job_id]:
                raise PilotError(f"{job_id} downloaded archive size differs from its bounded remote size")
            with tarfile.open(local_tar, "r:gz") as archive:
                members = archive.getmembers()
                names = {member.name for member in members}
                marker_member = next((member for member in members if member.name == "complete.json"), None)
                if marker_member is None or not marker_member.isfile():
                    raise PilotError(f"{job_id} archive lacks a regular completion marker")
                marker_stream = archive.extractfile(marker_member)
                if marker_stream is None:
                    raise PilotError(f"{job_id} completion marker could not be read")
                try:
                    marker_bytes = marker_stream.read(COMPLETE_MARKER_MAX_BYTES + 1)
                    if len(marker_bytes) > COMPLETE_MARKER_MAX_BYTES:
                        raise PilotError(f"{job_id} completion marker exceeds its configured bound")
                    archive_marker = json.loads(marker_bytes)
                except json.JSONDecodeError as error:
                    raise PilotError(f"{job_id} completion marker is invalid") from error
                if not isinstance(archive_marker, dict):
                    raise PilotError(f"{job_id} completion marker is not an object")
                archive_kind = archive_marker.get("archive_kind", "result")
                if archive_kind not in {"result", "diagnostic"}:
                    raise PilotError(f"{job_id} archive result classification is invalid")
                if archive_kind == "diagnostic" and (not checked["generic_worker"]
                                                       or archive_marker.get("exit_code") == 0):
                    raise PilotError(f"{job_id} diagnostic archive is inconsistent with worker status")
                required = {"mathlib-db.sqlite3", "worker.log", "complete.json"}
                if checked["generic_worker"] and archive_kind == "result":
                    required.update({"scratch", "artifacts"})
                def allowed(member: Any) -> bool:
                    return (member.name in required or member.name in {"artifacts", "scratch"} and member.isdir()
                            or member.name.startswith("artifacts/") or member.name.startswith("scratch/"))
                member_total = sum(member.size for member in members if member.isfile())
                if (len(members) > MAX_TAR_MEMBERS or member_total > MAX_TOTAL_EXTRACTED_BYTES
                        or any(member.size < 0 or member.size > MAX_TAR_MEMBER_BYTES for member in members)
                        or total_extracted + member_total > MAX_TOTAL_EXTRACTED_BYTES
                        or not required.issubset(names) or len(names) != len(members) or any(
                        Path(member.name).is_absolute() or ".." in Path(member.name).parts or not allowed(member)
                        for member in members)):
                    raise PilotError(f"{job_id} result archive has missing or unsafe entries")
                if archive_kind == "diagnostic" and names != required:
                    raise PilotError(f"{job_id} diagnostic archive contains unexpected payload")
                if any(member.name in {"artifacts", "scratch"} and not member.isdir() for member in members):
                    raise PilotError(f"{job_id} result output directory entry is not a directory")
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
            expected_argv = worker_argv_sha256(
                checked["worker_argv"], remote_root + "/" + job_id)
            expected_inputs = job_inputs_sha256(_validate_job_input_specs(spec.get("inputs", [])))
            if (marker.get("schema") != 1 or type(marker.get("exit_code")) is not int
                    or marker.get("commit") != repository.get("commit")
                    or marker.get("manifest_sha256") != spec.get("manifest_sha256")
                    or marker.get("database_sha256") != sha256_file(out / "mathlib-db.sqlite3")):
                raise PilotError(f"{job_id} completion marker or result hash is invalid")
            if checked["generic_worker"] and (
                    marker.get("worker_argv_sha256") != expected_argv
                    or marker.get("inputs_sha256") != expected_inputs):
                raise PilotError(f"{job_id} completion marker does not authenticate its command or immutable inputs")
            if marker["exit_code"] != next(item.get("exit_code") for item in state["jobs"] if item["id"] == job_id):
                raise PilotError(f"{job_id} completion marker exit does not match status")
            file_hashes.update({f"{job_id}/{path.relative_to(out)}": sha256_file(path) for path in extracted})
            job_results.append({"id": job_id, "exit_code": marker["exit_code"],
                                "database_sha256": sha256_file(out / "mathlib-db.sqlite3"),
                                "archive_sha256": sha256_file(local_tar),
                                "archive_kind": marker.get("archive_kind", "result"),
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
            try:
                if cleanup_allowed and self.state_path.exists() and self._load_state().get("phase") != "deleted":
                    final["cleanup"] = self.cleanup(confirm=True)
            except Exception as error:
                final["cleanup_error"] = f"{type(error).__name__}: {error}"
        final["elapsed_seconds"] = int(time.monotonic() - started)
        if failure is not None:
            final["error"] = failure
        final["complete"] = failure is None and "cleanup_error" not in final and final.get("cleanup", {}).get("phase") == "deleted"
        if self.state_path.exists():
            try:
                checkpoint = self._load_state()
                checkpoint["supervisor_report"] = final
                self._save(checkpoint)
            except Exception as error:
                final["state_checkpoint_error"] = f"{type(error).__name__}: {error}"
                final["complete"] = False
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
            checked = {"project_id": project_id, "zone": zone, "cli_profile": policy["cli_profile"],
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
        cleanup_checked = {"project_id": project_id, "zone": zone, "cli_profile": policy["cli_profile"],
                           "root_volume": root_policy}
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
    launch = sub.add_parser("create", help="create the single authorized bounded-worker server")
    launch.add_argument("--repo", type=Path, required=True); launch.add_argument("--jobs", type=Path, required=True)
    launch.add_argument("--confirm-create", action="store_true")
    sub.add_parser("status", help="read provider status only")
    run = sub.add_parser("run-workers", help="bootstrap exact checkout, transfer pinned jobs and launch workers concurrently")
    run.add_argument("--repo", type=Path, required=True); run.add_argument("--jobs", type=Path, required=True)
    collect = sub.add_parser("collect-workers", help="download and verify both worker results")
    collect.add_argument("--output", type=Path, required=True)
    finalize = sub.add_parser("finalize-worker", help=argparse.SUPPRESS)
    finalize.add_argument("--job-dir", type=Path, required=True)
    finalize.add_argument("--inputs-json", required=True)
    finalize.add_argument("--worker-count", type=int, required=True)
    finalize.add_argument("--commit", required=True)
    finalize.add_argument("--exit-code", type=int, required=True)
    finalize.add_argument("--argv-sha256", required=True)
    finalize.add_argument("--inputs-sha256", required=True)
    monitor = sub.add_parser("supervise", help="poll workers, collect results and delete resources automatically")
    monitor.add_argument("--repo", type=Path, required=True); monitor.add_argument("--jobs", type=Path, required=True)
    monitor.add_argument("--output", type=Path, required=True); monitor.add_argument("--poll-seconds", type=int, default=60)
    cleanup = sub.add_parser("cleanup", help="delete exact pilot server, attached volume and IP")
    cleanup.add_argument("--confirm-delete", action="store_true")
    args = parser.parse_args(argv)
    ctl = ScalewayPilot(policy_path=args.policy, state_path=args.state)
    try:
        if args.command == "finalize-worker":
            result = finalize_worker_result(args.job_dir, json.loads(args.inputs_json), args.worker_count,
                                            commit=args.commit, exit_code=args.exit_code,
                                            argv_sha256=args.argv_sha256, inputs_sha256=args.inputs_sha256)
        elif args.command == "plan": result = ctl.plan()
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
