#!/usr/bin/env python3
"""Run the compiled Lean instrumentation tools safely.

The source based ``lake env lean --run`` commands elaborate an instrumentation
entry point for every invocation.  Lake executable targets compile those entry
points once.  This wrapper hashes the pinned source and configuration inputs,
invokes ``lake build`` when that identity changes (or the binary is missing),
and only then hands control to the compiled tool.  Callers therefore do not
need to manage a potentially stale binary themselves, while warm calls avoid
replaying Lake's complete build graph.

Usage::

    python3 Experiment/lean_toolchain_cache.py inventory <source> ...
    python3 Experiment/lean_toolchain_cache.py scope <module> <source> ...
    python3 Experiment/lean_toolchain_cache.py oracle <module> <stock> <applied>

The wrapped tool's stdout and stderr are passed through unchanged.  Build
diagnostics are kept off stdout because the inventory and classifier protocols
parse their stdout as machine-readable records.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from collections.abc import Sequence


ROOT = Path(__file__).resolve().parents[1]
LOCK_PATH = ROOT / ".lake" / "simp-engine-toolchain.lock"
CACHE_PATH = ROOT / ".lake" / "simp-engine-toolchain-cache.json"
CacheEntry = dict[str, str]

TOOLS: dict[str, tuple[str, str]] = {
    "inventory": (
        "simpEngineInventory",
        ".lake/build/bin/simpEngineInventory",
    ),
    "scope": (
        "simpEngineBoundaryScope",
        ".lake/build/bin/simpEngineBoundaryScope",
    ),
    "oracle": (
        "simpEngineDeclarationOracle",
        ".lake/build/bin/simpEngineDeclarationOracle",
    ),
}


def _input_paths(tool: str) -> list[Path]:
    """Return source/config inputs whose contents affect the compiled tools.

    Mathlib is imported through its aggregate ``Mathlib`` module, so a change
    in any pinned package source can alter the import environment.  Hashing
    source files is much cheaper than invoking Lake's complete build graph on
    every warm call, while retaining content based invalidation (including
    same-size or same-mtime edits).
    """
    source_names = {
        "inventory": "SimpEngineInventory.lean",
        "scope": "SimpEngineBoundaryScope.lean",
        "oracle": "SimpEngineDeclarationOracle.lean",
    }
    try:
        tool_source = ROOT / "Experiment" / source_names[tool]
    except KeyError as error:
        raise ValueError(f"unknown tool {tool!r}") from error
    paths = [
        ROOT / "lakefile.toml",
        ROOT / "lake-manifest.json",
        ROOT / "lean-toolchain",
        ROOT / "ExplicitLean.lean",
        tool_source,
    ]
    paths.extend((ROOT / "ExplicitLean").rglob("*.lean"))
    package_root = ROOT / ".lake" / "packages"
    paths.extend(package_root.rglob("*.lean"))
    for pattern in ("lakefile.toml", "lakefile.lean", "lean-toolchain"):
        paths.extend(package_root.rglob(pattern))
    return sorted({path for path in paths if path.is_file()})


def _fingerprint(tool: str) -> str:
    digest = hashlib.sha256()
    for path in _input_paths(tool):
        digest.update(path.relative_to(ROOT).as_posix().encode("utf-8"))
        digest.update(b"\0")
        with path.open("rb") as source:
            while chunk := source.read(1024 * 1024):
                digest.update(chunk)
        digest.update(b"\0")
    return digest.hexdigest()


def _binary_fingerprint(binary: Path) -> str:
    digest = hashlib.sha256()
    with binary.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _read_cache() -> dict[str, CacheEntry]:
    try:
        value = json.loads(CACHE_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(value, dict):
        return {}
    return {
        str(target): {
            "inputs": str(entry["inputs"]),
            "binary": str(entry["binary"]),
        }
        for target, entry in value.items()
        if isinstance(target, str)
        and isinstance(entry, dict)
        and isinstance(entry.get("inputs"), str)
        and isinstance(entry.get("binary"), str)
    }


def _write_cache(cache: dict[str, CacheEntry]) -> None:
    temporary = CACHE_PATH.with_suffix(".json.tmp")
    temporary.write_text(
        json.dumps(cache, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    temporary.replace(CACHE_PATH)


def _build(tool: str, target: str, binary: Path) -> None:
    """Ensure ``target`` is fresh without polluting the tool's stdout."""
    LOCK_PATH.parent.mkdir(parents=True, exist_ok=True)
    with LOCK_PATH.open("a+") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        try:
            fingerprint = _fingerprint(tool)
            cache = _read_cache()
            entry = cache.get(target)
            if (
                entry is not None
                and entry.get("inputs") == fingerprint
                and binary.is_file()
                and entry.get("binary") == _binary_fingerprint(binary)
            ):
                return
            result = subprocess.run(
                ["lake", "build", target],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            if result.returncode:
                output = result.stdout or ""
                if output:
                    print(
                        output,
                        file=sys.stderr,
                        end="" if output.endswith("\n") else "\n",
                    )
                raise RuntimeError(
                    f"lake build {target} failed with status {result.returncode}"
                )
            if not binary.is_file():
                raise RuntimeError(
                    f"lake reported success but executable is missing: {binary}"
                )
            current_fingerprint = _fingerprint(tool)
            if current_fingerprint != fingerprint:
                raise RuntimeError(
                    f"source inputs changed while building {target}; refusing to cache"
                )
            cache[target] = {
                "inputs": current_fingerprint,
                "binary": _binary_fingerprint(binary),
            }
            _write_cache(cache)
        finally:
            fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


def run_tool(tool: str, args: Sequence[str]) -> int:
    """Build and run one named tool, returning its process status."""
    try:
        target, relative_binary = TOOLS[tool]
    except KeyError as error:
        choices = ", ".join(sorted(TOOLS))
        raise ValueError(f"unknown tool {tool!r}; choose one of: {choices}") from error
    binary = ROOT / relative_binary
    _build(tool, target, binary)
    completed = subprocess.run(
        ["lake", "env", str(binary), *args],
        cwd=ROOT,
        check=False,
    )
    return completed.returncode


def main(argv: Sequence[str]) -> int:
    if len(argv) < 2:
        print(
            "usage: lean_toolchain_cache.py <inventory|scope|oracle> <args...>",
            file=sys.stderr,
        )
        return 2
    try:
        return run_tool(argv[1], argv[2:])
    except (OSError, RuntimeError, ValueError) as error:
        print(f"explicit-lean tool launcher failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
