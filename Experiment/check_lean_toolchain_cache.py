#!/usr/bin/env python3
"""Focused safety checks for the compiled Lean tool launcher."""

from __future__ import annotations

from contextlib import contextmanager
from pathlib import Path
from types import SimpleNamespace
import tempfile
from collections.abc import Iterator

import lean_toolchain_cache as launcher


@contextmanager
def isolated_cache() -> Iterator[Path]:
    with tempfile.TemporaryDirectory(prefix="lean-toolchain-cache-") as raw:
        root = Path(raw)
        old_cache = launcher.CACHE_PATH
        old_lock = launcher.LOCK_PATH
        launcher.CACHE_PATH = root / "cache.json"
        launcher.LOCK_PATH = root / "lock"
        try:
            yield root
        finally:
            launcher.CACHE_PATH = old_cache
            launcher.LOCK_PATH = old_lock


def test_root_aggregator_is_an_input() -> None:
    assert launcher.ROOT / "ExplicitLean.lean" in launcher._input_paths("inventory")


def test_replaced_binary_does_not_hit_cache() -> None:
    with isolated_cache() as root:
        binary = root / "tool"
        binary.write_bytes(b"original")
        launcher._write_cache(
            {
                "target": {
                    "inputs": "stable-inputs",
                    "binary": launcher._binary_fingerprint(binary),
                }
            }
        )
        binary.write_bytes(b"replacement")
        calls: list[list[str]] = []
        original_run = launcher.subprocess.run
        original_fingerprint = launcher._fingerprint

        def fake_run(command: list[str], **_kwargs: object) -> SimpleNamespace:
            calls.append(command)
            binary.write_bytes(b"rebuilt")
            return SimpleNamespace(returncode=0, stdout="")

        launcher.subprocess.run = fake_run  # type: ignore[assignment]
        launcher._fingerprint = lambda _tool: "stable-inputs"
        try:
            launcher._build("inventory", "target", binary)
        finally:
            launcher.subprocess.run = original_run
            launcher._fingerprint = original_fingerprint
        assert calls == [["lake", "build", "target"]]
        cache = launcher._read_cache()
        assert cache["target"]["binary"] == launcher._binary_fingerprint(binary)


def test_source_change_during_build_is_not_published() -> None:
    with isolated_cache() as root:
        binary = root / "tool"
        fingerprints = iter(("before-build", "after-build"))
        original_run = launcher.subprocess.run
        original_fingerprint = launcher._fingerprint

        def fake_run(_command: list[str], **_kwargs: object) -> SimpleNamespace:
            binary.write_bytes(b"built-from-before-build")
            return SimpleNamespace(returncode=0, stdout="")

        launcher.subprocess.run = fake_run  # type: ignore[assignment]
        launcher._fingerprint = lambda _tool: next(fingerprints)
        try:
            try:
                launcher._build("inventory", "target", binary)
            except RuntimeError as error:
                assert "changed while building" in str(error)
            else:
                raise AssertionError("source change during build was accepted")
        finally:
            launcher.subprocess.run = original_run
            launcher._fingerprint = original_fingerprint
        assert not (root / "cache.json").exists()


def main() -> None:
    test_root_aggregator_is_an_input()
    test_replaced_binary_does_not_hit_cache()
    test_source_change_during_build_is_not_published()
    print("lean toolchain cache: focused invalidation checks passed")


if __name__ == "__main__":
    main()
