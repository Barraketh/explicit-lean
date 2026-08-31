"""Content identity for analysis checkpoints, independent of replay changes.

Analysis imports all of Mathlib. Hash its locked source/runtime closure and the
pinned Lean runtime before and after a manifest run. Project artifacts are
restricted to the five analysis modules; replay artifacts are deliberately not
part of this key. Full replay provenance still belongs to each fresh manifest.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
from typing import Any

ANALYSIS_IDENTITY_SCHEMA = 1
ANALYSIS_MODULES = (
    "ExplicitLean/SimpEngine/Inventory",
    "ExplicitLean/SimpEngine/Boundary/ScopeProbe",
    "ExplicitLean/SimpEngine/Boundary/ScopeFixture",
    "Experiment/SimpEngineInventory",
    "Experiment/SimpEngineBoundaryScope",
)
ANALYSIS_SOURCE_FILES = (
    *(f"{module}.lean" for module in ANALYSIS_MODULES),
    "Experiment/simp_engine_inventory.py",
    "Experiment/check_simp_engine_boundary_scope.py",
    "Experiment/inventory_checkpoint.py",
    "Experiment/process_runner.py",
    "Experiment/lean_toolchain_cache.py",
    "Experiment/simp_engine_boundary_corpus.py",
    "Experiment/analysis_checkpoint_identity.py",
    "Experiment/check_simp_engine_pin.py",
    "lakefile.toml", "lake-manifest.json", "lean-toolchain",
)
RUNTIME_SUFFIXES = (
    ".olean", ".olean.private", ".olean.server", ".ilean", ".ir",
    ".dylib", ".so", ".a", ".o", ".o.export", ".c",
)


def _file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _require_directory(path: Path) -> None:
    if not path.is_dir():
        raise RuntimeError(f"required identity root is missing: {path}")


def _walk(root: Path, *, source: bool = False) -> list[Path]:
    _require_directory(root)
    paths = []
    for directory, dirs, files in os.walk(root):
        # Package .lake/packages may link back to the whole dependency tree.
        dirs[:] = sorted(d for d in dirs if d != ".git" and
                         (not source or d != ".lake"))
        for name in sorted(files):
            matches = (name.endswith((".lean", ".toml")) or
                       name in {"lean-toolchain", "lake-manifest.json"}) if source else (
                           name.endswith(RUNTIME_SUFFIXES))
            if matches:
                paths.append(Path(directory) / name)
    return sorted(paths)


def _digest_paths(root: Path, paths: list[Path], *, stat_only: bool = False) -> str:
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(path.relative_to(root).as_posix().encode())
        digest.update(b"\0")
        if stat_only:
            st = path.stat()
            value = repr((st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns))
        else:
            value = _file_hash(path)
        digest.update(value.encode())
        digest.update(b"\0")
    return digest.hexdigest()


def _prefix(root: Path) -> Path:
    prefix = Path(subprocess.check_output(
        ["lake", "env", "lean", "--print-prefix"], cwd=root,
        text=True, timeout=60).strip()).resolve()
    for name in ("lean", "lake"):
        if not (prefix / "bin" / name).is_file():
            raise RuntimeError(f"pinned executable is missing: {prefix / 'bin' / name}")
    _require_directory(prefix / "lib/lean")
    return prefix


def _project_artifacts(root: Path) -> list[Path]:
    build = root / ".lake/build"
    _require_directory(build / "lib/lean")
    paths = []
    for module in ANALYSIS_MODULES:
        olean = build / "lib/lean" / f"{module}.olean"
        if not olean.is_file():
            raise RuntimeError(f"required analysis module is missing: {olean}")
        for subdir in ("lib/lean", "ir"):
            stem = build / subdir / module
            if stem.parent.is_dir():
                paths.extend(p for p in stem.parent.glob(stem.name + ".*")
                             if p.is_file() and p.name.endswith(RUNTIME_SUFFIXES))
    return sorted(set(paths))


def _dependency_paths(root: Path, prefix: Path) -> dict[str, tuple[Path, list[Path]]]:
    package_root = root / ".lake/packages"
    _require_directory(package_root)
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        raise RuntimeError("analysis identity needs locked packages")
    result = {"leanRuntime": (prefix / "lib", _walk(prefix / "lib"))}
    seen = set()
    for package in packages:
        name = package.get("name") if isinstance(package, dict) else None
        if (not isinstance(name, str) or not name or Path(name).name != name
                or name in {".", ".."} or name in seen):
            raise RuntimeError("invalid or duplicate locked package name")
        seen.add(name)
        directory = package_root / name
        source_paths = _walk(directory, source=True)
        if not source_paths:
            raise RuntimeError(f"package has no source inputs: {directory}")
        result[f"packageSource:{name}"] = (directory, source_paths)
        build = directory / ".lake/build"
        # Some toolchain-provided packages (Cli) have no local build directory.
        # Its absence is represented by the key set and changes when created.
        if build.exists():
            result[f"packageRuntime:{name}"] = (build, _walk(build))
        elif name == "mathlib":
            raise RuntimeError("required Mathlib runtime is missing")
    return result


def cheap_snapshot(root: Path, *, inventory_binary: Path, scope_binary: Path,
                   prefix: Path | None = None) -> dict[str, Any]:
    """Rehash small analysis inputs; stat the broad closure between batches.

    The stat snapshot is a mutation guard within one run, never a cache key or
    replacement for the full content hashes in identity(). Including ctime
    detects same-size edits followed by an mtime reset during a batch.
    """
    root = root.resolve()
    prefix = _prefix(root) if prefix is None else prefix
    return {
        "sources": {name: _file_hash(root / name) for name in ANALYSIS_SOURCE_FILES},
        "executables": {"inventory": _file_hash(inventory_binary),
                        "scope": _file_hash(scope_binary),
                        "lean": _file_hash(prefix / "bin/lean"),
                        "lake": _file_hash(prefix / "bin/lake")},
        "projectArtifacts": _digest_paths(root, _project_artifacts(root)),
        "dependencyStats": {name: _digest_paths(base, paths, stat_only=True)
                            for name, (base, paths) in _dependency_paths(root, prefix).items()},
    }


def identity(root: Path, *, inventory_binary: Path, scope_binary: Path) -> dict[str, Any]:
    root = root.resolve()
    prefix = _prefix(root)
    return {
        "analysisIdentitySchema": ANALYSIS_IDENTITY_SCHEMA,
        "analysisSources": {name: _file_hash(root / name) for name in ANALYSIS_SOURCE_FILES},
        "inventoryExecutableSha256": _file_hash(inventory_binary),
        "scopeExecutableSha256": _file_hash(scope_binary),
        "toolchain": {
            "prefix": str(prefix),
            "leanSha256": _file_hash(prefix / "bin/lean"),
            "lakeSha256": _file_hash(prefix / "bin/lake"),
            "leanVersion": subprocess.check_output(
                [str(prefix / "bin/lean"), "--version"], cwd=root,
                text=True, timeout=60).strip(),
        },
        "analysisArtifactTreeSha256": _digest_paths(root, _project_artifacts(root)),
        "dependencyContentHashes": {
            name: _digest_paths(base, paths)
            for name, (base, paths) in _dependency_paths(root, prefix).items()
        },
    }
