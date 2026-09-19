#!/usr/bin/env python3
"""Build the private Lean toolchain used by certification controls.

The only source mutation is inside ``.lake/SimpDisabled``.  The installed
elan toolchain and package cache are inputs and are never written.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tempfile
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
PATCH = Path(__file__).with_name("Main.lean.patch")
WORK = ROOT / ".lake" / "SimpDisabled"
SOURCE = WORK / "lean4-source"
BUILD = SOURCE / "build" / "release" / "stage1"
BINARY = BUILD / "bin" / "lean"
SYSROOT = BUILD
RUNTIME = SYSROOT / "lib" / "lean" / "libleanshared.dylib"
EXPECTED_COMMIT = "f3b06c705e6c85f5314019d5d3baab0fec5b580c"
EXPECTED_PATCH_SHA256 = "0db9b47b4319221db2c7c6bab176edd0455cf8c6feb6e2bd9d5b3afebd51f8b7"
VERSION = "4.32.2"
MANIFEST = WORK / "manifest.json"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def run(command: list[str], *, cwd: Path, timeout: int = 1800) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=timeout, check=False,
    )


def git_head() -> str:
    result = run(["git", "-C", str(SOURCE), "rev-parse", "HEAD"], cwd=ROOT, timeout=30)
    if result.returncode:
        raise RuntimeError(f"cannot read private Lean source HEAD:\n{result.stdout}")
    return result.stdout.strip()


def patch_source() -> None:
    if sha256(PATCH) != EXPECTED_PATCH_SHA256:
        raise RuntimeError("reviewed simp patch has unexpected contents")
    if not SOURCE.is_dir():
        SOURCE.parent.mkdir(parents=True, exist_ok=True)
        result = run(
            ["git", "clone", "--depth", "1", "--branch", "v4.32.2",
             "https://github.com/leanprover/lean4.git", str(SOURCE)],
            cwd=ROOT, timeout=1800,
        )
        if result.returncode:
            raise RuntimeError(f"cannot fetch pinned Lean source:\n{result.stdout}")
    if git_head() != EXPECTED_COMMIT:
        raise RuntimeError("private Lean source has the wrong pinned commit")
    paths = ["Lean/AddDecl.lean", "Lean/Meta/Tactic/Simp/Main.lean"]
    actual = {
        path: (SOURCE / "src" / path).read_text(encoding="utf-8")
        for path in paths
    }
    expected = expected_patched_sources()
    if actual != expected:
        clean = {
            path: run(["git", "-C", str(SOURCE), "show", f"HEAD:src/{path}"], cwd=ROOT, timeout=30).stdout
            for path in paths
        }
        if actual != clean:
            raise RuntimeError("private Lean source contains changes other than the reviewed patch")
        check = run(["patch", "-d", str(SOURCE / "src"), "-p1", "--dry-run", "-i", str(PATCH)], cwd=ROOT, timeout=30)
        if check.returncode:
            raise RuntimeError(f"cannot apply the reviewed simp patch:\n{check.stdout}")
        applied = run(["patch", "-d", str(SOURCE / "src"), "-p1", "-i", str(PATCH)], cwd=ROOT, timeout=30)
        if applied.returncode:
            raise RuntimeError(f"cannot apply the reviewed simp patch:\n{applied.stdout}")
        actual = {
            path: (SOURCE / "src" / path).read_text(encoding="utf-8")
            for path in paths
        }
    if actual != expected:
        raise RuntimeError("private Lean source is not exactly the reviewed simp-disabled patch")
    changed = run(["git", "-C", str(SOURCE), "diff", "--name-only"], cwd=ROOT, timeout=30)
    staged = run(["git", "-C", str(SOURCE), "diff", "--cached", "--name-only"], cwd=ROOT, timeout=30)
    expected_changes = {
        "src/Lean/AddDecl.lean",
        "src/Lean/Meta/Tactic/Simp/Main.lean",
    }
    actual_changes = set(changed.stdout.strip().splitlines()) | set(staged.stdout.strip().splitlines())
    if changed.returncode or staged.returncode or staged.stdout.strip() or actual_changes != expected_changes:
        raise RuntimeError("private Lean source contains unexpected tracked changes")


def expected_patched_sources() -> dict[str, str]:
    """Apply the committed patch to clean checkout copies for exact attestation."""
    paths = ["Lean/AddDecl.lean", "Lean/Meta/Tactic/Simp/Main.lean"]
    with tempfile.TemporaryDirectory(prefix="t56-patch-") as raw:
        for path in paths:
            clean = run(["git", "-C", str(SOURCE), "show", f"HEAD:src/{path}"], cwd=ROOT, timeout=30)
            if clean.returncode:
                raise RuntimeError(f"cannot read clean pinned source {path}:\n{clean.stdout}")
            target = Path(raw) / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(clean.stdout, encoding="utf-8")
        applied = run(["patch", "-d", raw, "-p1", "-i", str(PATCH)], cwd=ROOT, timeout=30)
        if applied.returncode:
            raise RuntimeError(f"reviewed simp patch does not apply cleanly:\n{applied.stdout}")
        return {path: (Path(raw) / path).read_text(encoding="utf-8") for path in paths}


def runtime_path() -> Path:
    if RUNTIME.is_file():
        return RUNTIME
    alternatives = sorted((SYSROOT / "lib" / "lean").glob("libleanshared.*"))
    if len(alternatives) != 1:
        raise RuntimeError("patched Lean shared runtime is missing or ambiguous")
    return alternatives[0]


def version() -> str:
    result = run([str(BINARY), "--version"], cwd=ROOT, timeout=30)
    if result.returncode:
        raise RuntimeError(f"patched Lean cannot report its version:\n{result.stdout}")
    expected = f"version {VERSION}"
    if expected not in result.stdout or EXPECTED_COMMIT not in result.stdout:
        raise RuntimeError(f"patched Lean has the wrong identity:\n{result.stdout}")
    return result.stdout.strip()


def expected_manifest() -> dict[str, object] | None:
    try:
        value = json.loads(MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def patched_sources_hash() -> str:
    digest = hashlib.sha256()
    for path in ("Lean/AddDecl.lean", "Lean/Meta/Tactic/Simp/Main.lean"):
        file = SOURCE / "src" / path
        digest.update(path.encode("utf-8"))
        digest.update(b"\0")
        with file.open("rb") as stream:
            while chunk := stream.read(1024 * 1024):
                digest.update(chunk)
        digest.update(b"\0")
    return digest.hexdigest()


def artifact_is_fresh() -> bool:
    current = expected_manifest()
    if current is None or not BINARY.is_file() or not (SYSROOT / "lib" / "lean").is_dir():
        return False
    return (
        current.get("schema") == 1
        and current.get("sourceCommit") == EXPECTED_COMMIT
        and current.get("leanVersion") == VERSION
        and current.get("patchSha256") == sha256(PATCH)
        and current.get("patchedSourcesSha256") == patched_sources_hash()
        and current.get("binary") == str(BINARY)
        and current.get("binarySha256") == sha256(BINARY)
        and current.get("runtime") == str(runtime_path())
        and current.get("runtimeSha256") == sha256(runtime_path())
        and current.get("sysroot") == str(SYSROOT)
        and current.get("guardOption") == "explicitLean.simpDisabled=true"
        and current.get("guardArguments") == "-DexplicitLean.simpDisabled=true;-DexplicitLean.certification=true;-E hasSorry"
        and current.get("guardEnvironment") == "EXPLICIT_LEAN_SIMP_DISABLED=1;EXPLICIT_LEAN_CERTIFICATION=1"
        and current.get("hasSorryDiagnostic") == "-E hasSorry"
    )


def build() -> dict[str, object]:
    patch_source()
    if not artifact_is_fresh():
        source_file = SOURCE / "src" / "Lean" / "Meta" / "Tactic" / "Simp" / "Main.lean"
        configured = SOURCE / "build" / "release" / "CMakeCache.txt"
        if not configured.is_file():
            result = run(["cmake", "--preset", "release", str(SOURCE)], cwd=ROOT)
            if result.returncode:
                raise RuntimeError(f"CMake configuration failed:\n{result.stdout}")
        result = run(["cmake", "--build", str(SOURCE / "build" / "release"), "--parallel", "4"], cwd=ROOT)
        if result.returncode:
            raise RuntimeError(f"private Lean build failed:\n{result.stdout}")
        if not BINARY.is_file():
            raise RuntimeError("private Lean build succeeded without a compiler")
        identity = version()
        manifest = {
            "schema": 1,
            "sourceCommit": EXPECTED_COMMIT,
            "leanVersion": VERSION,
            "compilerIdentity": identity,
            "patchSha256": sha256(PATCH),
            "patchedSourcesSha256": patched_sources_hash(),
            "binary": str(BINARY),
            "binarySha256": sha256(BINARY),
            "runtime": str(runtime_path()),
            "runtimeSha256": sha256(runtime_path()),
            "sysroot": str(SYSROOT),
            "guardOption": "explicitLean.simpDisabled=true",
            "guardArguments": "-DexplicitLean.simpDisabled=true;-DexplicitLean.certification=true;-E hasSorry",
            "guardEnvironment": "EXPLICIT_LEAN_SIMP_DISABLED=1;EXPLICIT_LEAN_CERTIFICATION=1",
            "hasSorryDiagnostic": "-E hasSorry",
            "builtAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
        WORK.mkdir(parents=True, exist_ok=True)
        temporary = MANIFEST.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        temporary.replace(MANIFEST)
    else:
        version()
    result = expected_manifest()
    if result is None or not artifact_is_fresh():
        raise RuntimeError("private patched Lean artifact is missing or stale")
    return result


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.parse_args(argv)
    try:
        value = build()
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"simp-disabled build failed closed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(value, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
