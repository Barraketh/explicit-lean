"""Filesystem-backed controls for analysis checkpoint identity."""
from __future__ import annotations

from contextlib import contextmanager
from pathlib import Path
import tempfile
import os
import subprocess
from unittest.mock import patch

import analysis_checkpoint_identity as identity


def _write(path: Path, contents: str = "fixture\n") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")


def _fixture(root: Path) -> tuple[Path, Path, Path]:
    for relative in identity.ANALYSIS_SOURCE_FILES:
        _write(root / relative, f"source:{relative}\n")
    _write(root / "lake-manifest.json", '{"packages":[{"name":"mathlib","type":"git","rev":"test"}]}\n')
    build = root / ".lake/build/lib/lean"
    for module in identity.ANALYSIS_MODULES:
        for suffix in identity.RUNTIME_SUFFIXES:
            _write(build / f"{module}{suffix}", f"artifact:{module}{suffix}\n")
            if suffix in {".ir", ".c", ".o", ".a", ".dylib", ".so", ".o.export"}:
                _write(root / ".lake/build/ir" / f"{module}{suffix}", f"ir-artifact:{module}{suffix}\n")
    package = root / ".lake/packages/mathlib"
    _write(package / "Mathlib/Test.lean", "def test := 1\n")
    _write(package / "lakefile.toml", "name = 'mathlib'\n")
    _write(package / ".lake/build/lib/lean/Mathlib/Test.olean", "package artifact\n")
    _write(package / ".lake/build/lib/lean/Mathlib/Test.dylib", "package native\n")
    prefix = root / "toolchain"
    _write(prefix / "bin/lean", "lean executable\n")
    _write(prefix / "bin/lake", "lake executable\n")
    for suffix in identity.RUNTIME_SUFFIXES:
        _write(prefix / "lib/lean" / f"Runtime{suffix}", f"runtime{suffix}\n")
    inventory = root / "bin/inventory"
    scope = root / "bin/scope"
    _write(inventory, "inventory executable\n")
    _write(scope, "scope executable\n")
    return prefix, inventory, scope


@contextmanager
def _pinned_toolchain(prefix: Path):
    def fake_check_output(command, *, cwd=None, text=True, timeout=None):
        if list(command) == ["lake", "env", "lean", "--print-prefix"]:
            return f"{prefix}\n"
        if list(command) == [str(prefix.resolve() / "bin/lean"), "--version"]:
            return "Lean version 4.32.2\n"
        raise AssertionError(f"unexpected subprocess query: {command!r}")
    with patch.object(identity.subprocess, "check_output", side_effect=fake_check_output):
        yield


def _identity(root: Path, prefix: Path, inventory: Path, scope: Path) -> dict:
    with _pinned_toolchain(prefix):
        return identity.identity(root, inventory_binary=inventory, scope_binary=scope)


def _changes_key(root: Path, prefix: Path, inventory: Path, scope: Path, path: Path) -> None:
    before = _identity(root, prefix, inventory, scope)
    path.write_text(path.read_text(encoding="utf-8") + "mutation\n", encoding="utf-8")
    after = _identity(root, prefix, inventory, scope)
    assert before != after, f"identity did not change for {path}"


def test_identity_controls() -> None:
    with tempfile.TemporaryDirectory(prefix="analysis-identity-") as temporary:
        root = Path(temporary)
        prefix, inventory, scope = _fixture(root)
        baseline = _identity(root, prefix, inventory, scope)
        replay_source = root / "ExplicitLean/SimpEngine/Boundary/SequenceCodec.lean"
        replay_artifact = root / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/SequenceCodec.olean"
        _write(replay_source, "changed replay source\n")
        _write(replay_artifact, "changed replay artifact\n")
        assert _identity(root, prefix, inventory, scope) == baseline
        mutations = (
            root / "Experiment/SimpEngineBoundaryScope.lean",
            root / ".lake/build/lib/lean/Experiment/SimpEngineBoundaryScope.olean",
            scope,
            inventory,
            prefix / "bin/lake",
            prefix / "lib/lean/Runtime.olean.server",
            root / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/ScopeProbe.olean.private",
            root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Test.dylib",
            root / ".lake/packages/mathlib/Mathlib/Test.lean",
            root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Test.olean",
            prefix / "lib/lean/Runtime.olean.private",
            prefix / "lib/lean/Runtime.dylib",
            prefix / "bin/lean",
        )
        for path in mutations:
            original = path.read_text(encoding="utf-8")
            _changes_key(root, prefix, inventory, scope, path)
            path.write_text(original, encoding="utf-8")
        runtime = prefix / "lib/lean/Runtime.dylib"
        runtime.unlink()
        assert _identity(root, prefix, inventory, scope) != baseline
        _write(runtime, "runtime.dylib\n")
        for native in (prefix / "bin/lean", prefix / "bin/lake", inventory, scope):
            original = native.read_bytes()
            native.unlink()
            try:
                _identity(root, prefix, inventory, scope)
            except (RuntimeError, FileNotFoundError):
                pass
            else:
                raise AssertionError(f"missing required executable accepted: {native}")
            native.write_bytes(original)
        with _pinned_toolchain(prefix):
            before = identity.cheap_snapshot(root, inventory_binary=inventory, scope_binary=scope)
            package_file = root / ".lake/packages/mathlib/Mathlib/Test.lean"
            stat = package_file.stat()
            original = package_file.read_bytes()
            package_file.write_bytes(original.replace(b"1", b"2"))
            os.utime(package_file, ns=(stat.st_atime_ns, stat.st_mtime_ns))
            assert identity.cheap_snapshot(root, inventory_binary=inventory, scope_binary=scope) != before
            package_file.write_bytes(original)
        required = root / ".lake/build/lib/lean/Experiment/SimpEngineInventory.olean"
        required.unlink()
        try:
            try:
                _identity(root, prefix, inventory, scope)
            except RuntimeError:
                pass
            else:
                raise AssertionError("missing required analysis artifact did not reject identity")
        finally:
            _write(required, "restored artifact\n")


def test_checkpoint_hit_runs_freshness() -> None:
    import inventory_checkpoint
    with tempfile.TemporaryDirectory(prefix="checkpoint-hit-") as temporary:
        store = inventory_checkpoint.CheckpointStore(Path(temporary), identity={"test": 1})
        modules = ["Mathlib/Test.lean"]
        hashes = {modules[0]: "source"}
        inputs = store.inputs("inventory", modules, hashes)
        store._publish(inputs, store.key_for(inputs), {"ok": True})
        calls: list[str] = []
        def freshness() -> None:
            calls.append("freshness")
            raise RuntimeError("changed during batch")
        try:
            store.get_or_compute("inventory", modules, hashes, lambda: {"never": True}, freshness=freshness)
        except RuntimeError as error:
            assert str(error) == "changed during batch"
        else:
            raise AssertionError("checkpoint HIT bypassed freshness")
        assert calls == ["freshness"]


def test_checkpoint_build_failure_does_not_publish() -> None:
    import inventory_checkpoint
    with tempfile.TemporaryDirectory(prefix="checkpoint-failure-") as temporary:
        checkpoint_root = Path(temporary)
        store = inventory_checkpoint.CheckpointStore(checkpoint_root, identity={"test": 1})
        modules = ["Mathlib/Test.lean"]
        hashes = {modules[0]: "source"}
        try:
            store.get_or_compute(
                "inventory", modules, hashes,
                lambda: (_ for _ in ()).throw(RuntimeError("build failed")),
            )
        except RuntimeError as error:
            assert str(error) == "build failed"
        else:
            raise AssertionError("failed producer unexpectedly returned")
        assert not list(checkpoint_root.rglob("*.json"))


def test_manifest_prewarm_failure_does_not_publish() -> None:
    import simp_engine_boundary_corpus as corpus
    with tempfile.TemporaryDirectory(prefix="manifest-prewarm-") as temporary:
        root = Path(temporary).resolve()
        source = root / ".lake/packages/mathlib/Mathlib/Test.lean"
        _write(source, "example : True := by simp\n")
        checkpoints = root / "checkpoints"
        failure = subprocess.CalledProcessError(1, ["lake", "build"], output="intentional build failure")
        with patch.object(corpus, "ROOT", root), \
             patch.object(corpus, "MATHLIB", root / ".lake/packages/mathlib"), \
             patch.object(corpus, "assert_repository", return_value="commit"), \
             patch.object(corpus, "verify_environment", return_value=("mathlib", {"version": "test"})), \
             patch.object(
                 corpus.manual_overrides, "load_database",
                 return_value=({"mathlibCommit": "mathlib", "lean": {"version": "test"}}, []),
             ), \
             patch.object(corpus, "implementation_hashes", return_value={}), \
             patch.object(corpus, "run_process", side_effect=failure) as build:
            try:
                corpus.build_manifest([source], module_prefix="Mathlib", checkpoint_root=checkpoints)
            except subprocess.CalledProcessError as error:
                assert error is failure
            else:
                raise AssertionError("manifest accepted failed prewarm")
        assert build.call_count == 1
        assert not checkpoints.exists()


def main() -> None:
    test_identity_controls()
    test_checkpoint_hit_runs_freshness()
    test_checkpoint_build_failure_does_not_publish()
    test_manifest_prewarm_failure_does_not_publish()
    print("analysis checkpoint identity: filesystem mutation and HIT freshness controls passed")


if __name__ == "__main__":
    main()
