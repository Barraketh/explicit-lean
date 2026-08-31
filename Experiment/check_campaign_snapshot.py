#!/usr/bin/env python3
"""Check snapshot cache isolation using tiny temporary fixtures, without builds."""

from __future__ import annotations

from contextlib import contextmanager
import json
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch

import campaign_snapshot as snapshot


@contextmanager
def fixture():
    with tempfile.TemporaryDirectory(prefix="snapshot-safety-") as raw:
        root = Path(raw).resolve() / "project"
        package = root / ".lake/packages/mathlib"
        package.mkdir(parents=True)
        # Real Git status distinguishes untracked sources from ignored caches.
        # No commits, project worktrees, or Lean builds are created by this test.
        subprocess.run(["git", "init", "--quiet", str(package)], check=True)
        (package / ".git/info/exclude").write_text(".lake/\n")
        (package / ".lake/build").mkdir(parents=True)
        (package / ".lake/build/ignored.olean").write_bytes(b"ignored fixture cache")
        (root / ".lake/build").mkdir()
        (root / ".lake/build/cache-entry").write_bytes(b"original cache bytes")
        destination = root / "snapshots/test"
        destination.mkdir(parents=True)

        def fake_git(args, cwd=None):
            if args[:3] == ["git", "rev-parse", "--verify"]:
                return "project-revision"
            if args[:2] == ["git", "show"]:
                return json.dumps({"packages": [
                    {"type": "git", "name": "mathlib", "rev": "package-revision"}
                ]})
            if cwd == package:
                if args == ["git", "rev-parse", "HEAD"]:
                    return "package-revision"
                if args[:2] == ["git", "status"]:
                    return subprocess.check_output(args, cwd=cwd, text=True).strip()
            if cwd == destination:
                if args == ["git", "rev-parse", "--show-toplevel"]:
                    return str(destination)
                if args == ["git", "rev-parse", "HEAD"]:
                    return "project-revision"
                if args == ["git", "status", "--porcelain"]:
                    return ""
            raise AssertionError(f"unexpected Git call: {args}, cwd={cwd}")

        with patch.multiple(snapshot, ROOT=root, SNAPSHOTS=root / "snapshots"), \
                patch.object(snapshot, "run", side_effect=fake_git):
            yield root, destination, package


def test_cache_paths_reject_aliases_and_files() -> None:
    paths = (
        ("source .lake path", "source", ".lake"),
        ("source build cache", "source", ".lake/build"),
        ("snapshot .lake path", "destination", ".lake"),
        ("snapshot build cache", "destination", ".lake/build"),
    )
    for label, owner, relative in paths:
        for kind in ("symlink", "dangling_symlink", "file"):
            with fixture() as (root, destination, _package):
                path = (root if owner == "source" else destination) / relative
                if path.exists():
                    path.rename(root / "saved-directory")
                path.parent.mkdir(parents=True, exist_ok=True)
                if kind == "file":
                    path.write_bytes(b"not a cache directory")
                else:
                    target = root / "symlink-target"
                    if kind == "symlink":
                        target.mkdir()
                    path.symlink_to(target, target_is_directory=True)
                try:
                    snapshot.create("HEAD", "test")
                except RuntimeError as error:
                    assert label in str(error), (label, kind, error)
                else:
                    raise AssertionError(f"accepted {label}: {kind}")
                assert not (destination / ".lake/campaign-snapshot.json").exists()


def test_untracked_package_source_rejected() -> None:
    with fixture() as (_root, destination, package):
        (package / "Untracked.lean").write_text("-- not part of the pinned revision\n")
        try:
            snapshot.create("HEAD", "test")
        except RuntimeError as error:
            assert "shared mathlib has source edits" in str(error)
        else:
            raise AssertionError("snapshot accepted an untracked package source")
        assert not (destination / ".lake").exists()


def test_clone_is_private_and_sharing_is_explicit() -> None:
    with fixture() as (root, destination, package):
        result = snapshot.create("HEAD", "test")
        assert result["cacheClonedThisCall"] is True
        assert result["cacheValidated"] is False
        assert result["sharedPackageArtifactsImmutable"] is False
        assert result["noPackageWritesLeaseRequired"] is True
        assert result["noPackageWritesLeaseEnforced"] is False
        copied = destination / ".lake/build/cache-entry"
        original = root / ".lake/build/cache-entry"
        assert original.stat().st_ino != copied.stat().st_ino
        original.write_bytes(b"changed in source checkout")
        assert copied.read_bytes() == b"original cache bytes"
        assert (destination / ".lake/packages/mathlib").resolve() == package
        metadata = destination / ".lake/campaign-snapshot.json"
        assert json.loads(metadata.read_text()) == result
        assert snapshot.create("HEAD", "test")["cacheClonedThisCall"] is False


def main() -> None:
    test_cache_paths_reject_aliases_and_files()
    test_untracked_package_source_rejected()
    test_clone_is_private_and_sharing_is_explicit()
    print("campaign snapshot: cache paths, untracked sources, private clone, and lease metadata passed")


if __name__ == "__main__":
    main()
