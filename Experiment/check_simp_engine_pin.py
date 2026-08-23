#!/usr/bin/env python3
"""Fail if the authoritative Lean simplifier source surface moves."""

from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_VERSION = "4.32.2"
LEAN_COMMIT = "f3b06c705e6c85f5314019d5d3baab0fec5b580c"
SOURCE_HASHES = {
    "Lean/Elab/Tactic/Simp.lean": "e92ca8455b6c711c6b14ee7b65a46151756179ca1ff83a0f7d34f4de36853962",
    "Lean/Meta/Tactic/Simp/Main.lean": "868a8f709f798aa9ab46c50b4ccfc11750269b5c4a02461db26e0fca9b938b7b",
    "Lean/Meta/Tactic/Simp/Rewrite.lean": "232c1bf17adc086ce3812361d98886740c81894b117525dd270fa68c5bee5a4a",
    "Lean/Meta/Tactic/Simp/Types.lean": "2c7b77822452e3194d4d820854068e2fb72f33a2041dd9ae3a09df153423c869",
    "Lean/Meta/Tactic/Simp/SimpTheorems.lean": "78b3a7f971d3bd2aeca9c60a7850ec3449b9e48f9730000569fa43fa0274957d",
    "Lean/Meta/Tactic/Simp/SimpCongrTheorems.lean": "46852cd6ba7a38bf58188ccce2dcec4dd6b21c072f05d45d3bd6425a5a863b1b",
    "Lean/Meta/CongrTheorems.lean": "2a24eae0954ff67bab815eab23dd595be020c0320086f070bae846947413d2db",
    "Lean/Meta/Transform.lean": "de997e740f295fd829a76362d714343bc8bca0d82ace7418b8d75b3a1d0e02ea",
    "Lean/Meta/HaveTelescope.lean": "551e4ae4b8c98ca5d841ae3449406a0835bfa3a398d59c4dca3e6aef95b60620",
}


def command_output(*command: str) -> str:
    completed = subprocess.run(
        list(command),
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=30,
    )
    if completed.returncode != 0:
        raise RuntimeError(completed.stdout)
    return completed.stdout.strip()


def main() -> None:
    version = command_output("lean", "--version")
    if f"version {LEAN_VERSION}" not in version or f"commit {LEAN_COMMIT}" not in version:
        raise RuntimeError(f"unexpected Lean toolchain: {version}")
    prefix = Path(command_output("lean", "--print-prefix"))
    source_root = prefix / "src" / "lean"
    for relative, expected in SOURCE_HASHES.items():
        path = source_root / relative
        if not path.is_file():
            raise RuntimeError(f"pinned Lean source is missing: {path}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise RuntimeError(
                f"pinned Lean source changed: {relative}: {actual} != {expected}"
            )
    fork = (ROOT / "ExplicitLean" / "SimpEngine.lean").read_text(encoding="utf-8")
    if LEAN_COMMIT not in fork:
        raise RuntimeError("simp engine fork does not declare the pinned Lean commit")
    print(f"pinned simp source surface: Lean {LEAN_VERSION} {LEAN_COMMIT[:12]}: ok")


if __name__ == "__main__":
    main()
