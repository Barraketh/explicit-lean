#!/usr/bin/env python3
"""Prepare a pinned local run checkout without disturbing active development.

The checkout has its own APFS copy-on-write project build cache. Package sources
and package build artifacts are shared, not immutable. Callers must coordinate
a no-package-writes lease across all users of that tree for the entire run;
this helper checks initial cleanliness but does not acquire or enforce a lease.
Lake must still validate the copied project cache; the copy itself is not build
or translation evidence.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SNAPSHOTS = ROOT / ".lake/search-free-mathlib/snapshots"


def run(args: list[str], cwd: Path = ROOT) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def require_plain_directory(path: Path, label: str) -> None:
    """Allow an absent directory, but never a symlink or another file type."""
    if path.is_symlink() or (path.exists() and not path.is_dir()):
        raise RuntimeError(f"{label} must be a directory, not a symlink or other file: {path}")


def create(commit: str, name: str | None = None) -> dict:
    revision = run(["git", "rev-parse", "--verify", f"{commit}^{{commit}}"])
    name = name or f"run-{revision[:12]}"
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,63}", name):
        raise ValueError("snapshot name must be a simple directory name")
    source_lake = ROOT / ".lake"
    source_build = source_lake / "build"
    require_plain_directory(source_lake, "source .lake path")
    require_plain_directory(source_build, "source build cache")
    packages = source_lake / "packages"
    expected_lock = json.loads(run(["git", "show", f"{revision}:lake-manifest.json"]))
    package_commits = {}
    for package in expected_lock["packages"]:
        if package["type"] != "git":
            raise RuntimeError("only pinned Git packages can be shared by this snapshot helper")
        checkout = packages / package["name"]
        if run(["git", "rev-parse", "HEAD"], checkout) != package["rev"]:
            raise RuntimeError(f"shared {package['name']} does not match the pinned revision")
        if run(["git", "status", "--porcelain", "--untracked-files=all"], checkout):
            raise RuntimeError(f"shared {package['name']} has source edits; refusing to share it")
        package_commits[package["name"]] = package["rev"]
    SNAPSHOTS.mkdir(parents=True, exist_ok=True)
    destination = SNAPSHOTS / name
    if destination.is_symlink():
        raise RuntimeError("snapshot destination must not be a symlink")
    if not destination.exists():
        subprocess.run(["git", "worktree", "add", "--detach", str(destination), revision],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    if Path(run(["git", "rev-parse", "--show-toplevel"], destination)).resolve() != destination.resolve():
        raise RuntimeError("existing destination is not its own worktree")
    if run(["git", "rev-parse", "HEAD"], destination) != revision:
        raise RuntimeError("existing snapshot has a different commit")
    if run(["git", "status", "--porcelain"], destination):
        raise RuntimeError("snapshot source is dirty; use another name or finish its edits")
    lake = destination / ".lake"
    build = lake / "build"
    require_plain_directory(lake, "snapshot .lake path")
    require_plain_directory(build, "snapshot build cache")
    lake.mkdir(exist_ok=True)
    shared = lake / "packages"
    if shared.exists() or shared.is_symlink():
        if not shared.is_symlink() or shared.resolve() != packages.resolve():
            raise RuntimeError("existing snapshot package path is not the expected shared checkout")
    else:
        shared.symlink_to(packages, target_is_directory=True)
    cloned = False
    if not build.exists() and source_build.is_dir():
        subprocess.run(["cp", "-cR", str(source_build), str(build)], check=True)
        cloned = True
    result = {
        "commit": revision, "path": str(destination), "mathlibCommit": package_commits["mathlib"],
        "packageCommits": package_commits,
        "packages": str(packages), "cacheClonedThisCall": cloned,
        "sharedPackageArtifactsImmutable": False,
        "noPackageWritesLeaseRequired": True,
        "noPackageWritesLeaseEnforced": False,
        "cacheValidated": False, "preparedAt": datetime.now(timezone.utc).isoformat(),
    }
    metadata = lake / "campaign-snapshot.json"
    temporary = metadata.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(result, indent=2) + "\n")
    temporary.replace(metadata)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", default="HEAD")
    parser.add_argument("--name")
    args = parser.parse_args()
    print(json.dumps(create(args.commit, args.name), indent=2))


if __name__ == "__main__":
    main()
