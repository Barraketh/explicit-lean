#!/usr/bin/env python3
"""Check manifest/scope timeout propagation without running Lake or Lean."""

from __future__ import annotations

from contextlib import ExitStack
import json
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch

import check_simp_engine_boundary_scope as scope
import boundary_materialize_shard as materializer
import simp_engine_boundary_corpus as corpus


def test_scope_build_and_batches(root: Path) -> None:
    specs = []
    for name in ("One", "Two"):
        path = root / f"{name}.lean"
        path.write_text("-- fixture\n")
        specs.append(scope.ModuleSpec(f"Test.{name}", path, 1))
    for loader, requested, expected in (
        (scope.load_records_with_fallbacks, {}, 600),
        (scope.load_records_with_fallbacks, {"timeout": 173}, 173),
        (scope.load_records, {"timeout": 941}, 941),
    ):
        calls = []

        def fake_process(command, **kwargs):
            calls.append((command, kwargs["timeout"]))
            if command[:2] == ["lake", "build"]:
                output = ""
            else:
                assert command[2] == "scope"
                module = command[3]
                output = scope.OCCURRENCE_MARKER + json.dumps({"module": module}) + "\n"
            return subprocess.CompletedProcess(command, 0, output, None)

        with patch.object(scope, "run_process", side_effect=fake_process):
            result = loader(specs, batch_size=1, **requested)
        assert set(result[0]) == {"Test.One", "Test.Two"}
        assert len(calls) == 3  # prerequisite build and both batches
        assert calls[0][0][:2] == ["lake", "build"]
        assert [timeout for _command, timeout in calls] == [expected] * 3


def test_manifest_passes_requested_timeout(root: Path) -> None:
    mathlib = root / "packages/mathlib"
    path = mathlib / "Mathlib/Test.lean"
    path.parent.mkdir(parents=True)
    path.write_text("simp")
    observed = []

    class ScopeReached(Exception):
        pass

    def scope_adapter(specs, *, batch_size=128, timeout=600):
        observed.append((specs, batch_size, timeout))
        raise ScopeReached

    with ExitStack() as stack:
        stack.enter_context(patch.object(corpus, "MATHLIB", mathlib))
        stack.enter_context(patch.object(corpus, "assert_repository", return_value="revision"))
        stack.enter_context(patch.object(corpus, "verify_environment", return_value=("mathlib", {})))
        stack.enter_context(patch.object(corpus, "implementation_hashes", return_value={}))
        stack.enter_context(patch.object(corpus, "inventory_paths", return_value=({}, [])))
        stack.enter_context(patch.object(
            corpus, "validate_module_inventory", return_value=([{"id": "occurrence"}], 0, 0)
        ))
        stack.enter_context(patch.object(scope, "load_records_with_fallbacks", side_effect=scope_adapter))
        try:
            corpus.build_manifest([path], module_prefix="Mathlib/", scope_batch_size=7, timeout=1234)
        except ScopeReached:
            pass
        else:
            raise AssertionError("manifest never invoked the scope adapter")
    assert len(observed) == 1
    specs, batch_size, timeout = observed[0]
    assert [spec.module for spec in specs] == ["Mathlib.Test"]
    assert (batch_size, timeout) == (7, 1234)


def test_shard_classification_passes_requested_timeout(root: Path) -> None:
    from types import SimpleNamespace

    path = root / "Selected.lean"
    path.write_text("-- no simp calls\n")
    selected = [SimpleNamespace(
        source_path=path, module="Mathlib/Selected.lean",
        compiled_module="Mathlib.Selected", source=path.read_bytes(), occurrences=[],
    )]
    with patch.object(corpus, "inventory_paths", return_value=({}, [])) as inventory_call, \
            patch.object(corpus, "validate_module_inventory", return_value=([], 0, 0)), \
            patch.object(corpus, "join_scope_records", return_value=([], 0)), \
            patch.object(scope, "load_records_with_fallbacks", return_value=({}, {}, [])) as scope_call:
        materializer.verify_selected_classifications(selected, timeout=37)
    assert inventory_call.call_args.kwargs["timeout"] == 37
    assert scope_call.call_args.kwargs["timeout"] == 37


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="scope-timeout-") as raw:
        root = Path(raw).resolve()
        test_scope_build_and_batches(root)
        test_manifest_passes_requested_timeout(root)
        test_shard_classification_passes_requested_timeout(root)
    print("scope timeout: default and overrides reach build, batches, manifest and shard adapters")


if __name__ == "__main__":
    main()
