#!/usr/bin/env python3
"""Focused protocol checks for durable inventory/scope batch checkpoints."""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
from types import SimpleNamespace

import check_simp_engine_boundary_scope as scope
import simp_engine_boundary_corpus as corpus
from inventory_checkpoint import CheckpointStore


def test_hit_avoids_producer() -> None:
    with tempfile.TemporaryDirectory(prefix="inventory-checkpoint-") as raw:
        store = CheckpointStore(Path(raw) / "checkpoints", identity={
            "repositoryCommit": "repo",
            "mathlibCommit": "mathlib",
            "lean": {"version": "4.32.2", "commit": "lean"},
            "implementationHashes": {"Experiment/tool.py": "impl-a"},
            "pinnedPackages": [{"name": "mathlib", "rev": "mathlib", "type": "git"}],
        })
        calls = 0

        def producer() -> dict[str, str]:
            nonlocal calls
            calls += 1
            return {"stdout": "batch output"}

        first = store.get_or_compute(
            "inventory", ["Mathlib/A.lean"], ["source-a"], producer,
            validator=lambda value: isinstance(value, dict) and isinstance(value.get("stdout"), str),
        )
        second = store.get_or_compute(
            "inventory", ["Mathlib/A.lean"], ["source-a"], producer,
            validator=lambda value: isinstance(value, dict) and isinstance(value.get("stdout"), str),
        )
        assert first.hit is False
        assert second.hit is True
        assert calls == 1


def test_key_changes_miss() -> None:
    with tempfile.TemporaryDirectory(prefix="inventory-checkpoint-key-") as raw:
        root = Path(raw) / "checkpoints"
        identity = {"toolchain": "lean", "implementationHashes": {"tool.py": "a"}}
        store = CheckpointStore(root, identity=identity)
        calls = 0

        def producer() -> dict[str, str]:
            nonlocal calls
            calls += 1
            return {"stdout": str(calls)}

        store.get_or_compute("scope", ["Mathlib/A.lean"], ["source-a"], producer)
        assert store.get_or_compute("scope", ["Mathlib/A.lean"], ["source-a"], producer).hit
        assert not store.get_or_compute("scope", ["Mathlib/A.lean"], ["source-b"], producer).hit
        changed = CheckpointStore(root, identity={"toolchain": "lean", "implementationHashes": {"tool.py": "b"}})
        assert not changed.get_or_compute("scope", ["Mathlib/A.lean"], ["source-b"], producer).hit
        # The ordered module set is part of the key, so changing its order is
        # conservative even when the source hash multiset is unchanged.
        assert not changed.get_or_compute(
            "scope", ["Mathlib/B.lean", "Mathlib/A.lean"], ["source-b", "source-a"], producer
        ).hit
        assert calls == 4


def test_corruption_is_not_reused() -> None:
    with tempfile.TemporaryDirectory(prefix="inventory-checkpoint-corrupt-") as raw:
        store = CheckpointStore(Path(raw) / "checkpoints", identity={"toolchain": "lean"})
        calls = 0

        def producer() -> dict[str, str]:
            nonlocal calls
            calls += 1
            return {"stdout": f"result-{calls}"}

        first = store.get_or_compute("inventory", ["Mathlib/A.lean"], ["source"], producer)
        path = store.path_for(first.key, "inventory")
        envelope = json.loads(path.read_text(encoding="utf-8"))
        envelope["payload"] = {"stdout": "forged"}
        path.write_text(json.dumps(envelope), encoding="utf-8")
        second = store.get_or_compute("inventory", ["Mathlib/A.lean"], ["source"], producer)
        assert second.hit is False
        assert calls == 2


def test_failed_producer_does_not_publish() -> None:
    with tempfile.TemporaryDirectory(prefix="inventory-checkpoint-failure-") as raw:
        root = Path(raw) / "checkpoints"
        store = CheckpointStore(root, identity={"toolchain": "lean"})

        def producer() -> object:
            raise RuntimeError("producer failed")

        try:
            store.get_or_compute("scope", ["Mathlib/A.lean"], ["source"], producer)
        except RuntimeError as error:
            assert str(error) == "producer failed"
        else:
            raise AssertionError("failed producer was accepted")
        assert not root.exists()


def test_freshness_failure_does_not_publish() -> None:
    with tempfile.TemporaryDirectory(prefix="inventory-checkpoint-fresh-") as raw:
        root = Path(raw) / "checkpoints"
        store = CheckpointStore(root, identity={"toolchain": "lean"})

        def freshness_failure() -> None:
            raise RuntimeError("source changed during batch")

        try:
            store.get_or_compute(
                "inventory", ["Mathlib/A.lean"], ["source"],
                lambda: {"stdout": "complete"},
                freshness=freshness_failure,
            )
        except RuntimeError as error:
            assert str(error) == "source changed during batch"
        else:
            raise AssertionError("freshness failure was accepted")
        assert not root.exists()


def test_inventory_and_scope_hits_skip_batch_producers() -> None:
    """Exercise both existing batch seams, including their raw-output payloads."""
    with tempfile.TemporaryDirectory(prefix="inventory-checkpoint-seams-") as raw:
        root = Path(raw)
        identity = {"toolchain": "lean", "implementationHashes": {"tool.py": "a"}}
        store = CheckpointStore(root / "checkpoints", identity=identity)

        module_path = corpus.MATHLIB / "Mathlib/CategoryTheory/EqToHom.lean"
        inventory_calls = 0
        original_inventory_runner = corpus.run_process

        def fake_inventory_runner(*_args: object, **_kwargs: object) -> object:
            nonlocal inventory_calls
            inventory_calls += 1
            return SimpleNamespace(
                returncode=0,
                stdout=json.dumps({
                    "file": str(module_path), "kind": "simp", "startByte": 0,
                    "endByte": 4, "line": 1, "column": 0,
                    "syntaxKind": "Lean.Parser.Tactic.simp", "source": "simp",
                }) + "\n",
                stderr="",
            )

        corpus.run_process = fake_inventory_runner  # type: ignore[assignment]
        try:
            corpus._inventory_batch_result([module_path], 10, store)
            result = corpus._inventory_batch_result([module_path], 10, store)
            assert result[2] is True
            assert inventory_calls == 1
        finally:
            corpus.run_process = original_inventory_runner

        source = root / "A.lean"
        source.write_text("example : True := by simp\n", encoding="utf-8")
        spec = scope.ModuleSpec("Test.A", source, 1)
        scope_calls: list[list[str]] = []
        original_scope_runner = scope.run

        def fake_scope_runner(command: list[str], timeout: int = 600) -> str:
            scope_calls.append(command)
            if command[:2] == ["lake", "build"]:
                return ""
            return (
                scope.OCCURRENCE_MARKER
                + json.dumps({
                    "module": "Test.A", "startByte": 20, "endByte": 24,
                    "kind": "simp", "source": "simp",
                })
                + "\n"
                + scope.DECLARATION_MARKER
                + json.dumps({
                    "module": "Test.A", "startByte": 0, "endByte": 25,
                    "name": "Test.A.example", "isProof": True,
                })
                + "\n"
            )

        scope.run = fake_scope_runner  # type: ignore[assignment]
        try:
            scope.load_records_with_fallbacks([spec], batch_size=1, timeout=10, checkpoint=store)
            scope.load_records_with_fallbacks([spec], batch_size=1, timeout=10, checkpoint=store)
            # The prerequisite build remains intentionally uncached; only the
            # completed scope batch is reused.
            assert len(scope_calls) == 3
        finally:
            scope.run = original_scope_runner


def test_scope_expected_zero_and_missing_counts() -> None:
    with tempfile.TemporaryDirectory(prefix="inventory-checkpoint-scope-counts-") as raw:
        root = Path(raw)
        store = CheckpointStore(root / "checkpoints", identity={"toolchain": "lean"})
        zero_source = root / "Zero.lean"
        zero_source.write_text("def zero := True\n", encoding="utf-8")
        missing_source = root / "Missing.lean"
        missing_source.write_text("example : True := by simp\n", encoding="utf-8")
        calls: list[list[str]] = []
        original_scope_runner = scope.run

        def empty_scope_runner(command: list[str], timeout: int = 600) -> str:
            calls.append(command)
            return ""

        scope.run = empty_scope_runner  # type: ignore[assignment]
        try:
            zero = scope.ModuleSpec("Test.Zero", zero_source, 0)
            result = scope.load_records_with_fallbacks(
                [zero], batch_size=1, timeout=10, checkpoint=store
            )
            assert result[0] == {} and result[1] == {}
            missing = scope.ModuleSpec("Test.Missing", missing_source, 1)
            try:
                scope.load_records_with_fallbacks(
                    [missing], batch_size=1, timeout=10, checkpoint=store
                )
            except RuntimeError as error:
                assert "expected 1, found 0" in str(error)
            else:
                raise AssertionError("strict scope validation accepted missing records")
        finally:
            scope.run = original_scope_runner


def main() -> None:
    test_hit_avoids_producer()
    test_key_changes_miss()
    test_corruption_is_not_reused()
    test_failed_producer_does_not_publish()
    test_freshness_failure_does_not_publish()
    test_inventory_and_scope_hits_skip_batch_producers()
    test_scope_expected_zero_and_missing_counts()
    print("inventory checkpoints: hits, key invalidation, corruption, and failed producers passed")


if __name__ == "__main__":
    main()
