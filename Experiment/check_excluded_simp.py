#!/usr/bin/env python3
"""Check the separately materialized tactic modules.

The ordinary manifest intentionally excludes these modules because several
occurrences are inside reusable tactic implementations.  This checker keeps
the exception closed: it validates exact source bytes and ranges, lowers only
the deterministic occurrences, compiles the resulting modules with the
pinned import path, and records the dynamic occurrences as fail-closed
unsupported or syntax/data records.
"""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import simp_engine_inventory as inventory


ROOT = Path(__file__).resolve().parents[1]
# Worktrees do not carry the campaign's ignored `.lake`; the package is still
# shared read-only by all worktrees.  A normal checkout has ROOT/.lake.
CAMPAIGN_ROOT = ROOT.parents[2] if ROOT.parents[2].name == "explicit-lean" else ROOT
MATHLIB = CAMPAIGN_ROOT / ".lake" / "packages" / "mathlib"
MODULES = {
    "Mathlib/Tactic/DeriveEncodable.lean": {
        2799: "rw [Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair] at *",
        3417: (
            "dsimp only\n"
            "      split\n"
            "      next h =>\n"
            "        rw [Nat.unpair_pair] at h ⊢\n"
            "      next h =>\n"
            "        rw [Nat.unpair_pair] at h ⊢\n"
            "        dsimp only at h ⊢\n"
            "        exact False.elim (h rfl)"
        ),
        3485: (
            "dsimp only\n"
            "      split\n"
            "      next h =>\n"
            "        rw [Nat.unpair_pair] at h ⊢\n"
            "        exact False.elim ((Nat.succ_ne_zero _) h)\n"
            "      next h =>\n"
            "        rw [Nat.unpair_pair] at h ⊢\n"
            "        dsimp only at h ⊢\n"
            "        rw [Nat.add_sub_cancel, iha, ihb]"
        ),
        3988: "rfl",
    },
    "Mathlib/Tactic/Lift.lean": {
        1999: "rfl",
        8643: "rw [← $newEqIdent] at $declIdent:ident",
        8740: "rw [← $newEqIdent]",
    },
}

SUPPORTED_SOURCE = {
    ("Mathlib/Tactic/DeriveEncodable.lean", 2799): "simp only [Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair] at *",
    ("Mathlib/Tactic/DeriveEncodable.lean", 3417): "simp",
    ("Mathlib/Tactic/DeriveEncodable.lean", 3485): "simp [iha, ihb]",
    ("Mathlib/Tactic/DeriveEncodable.lean", 3988): "simp",
    ("Mathlib/Tactic/Lift.lean", 1999): "simp",
    ("Mathlib/Tactic/Lift.lean", 8643): "simp -failIfUnchanged only [← $newEqIdent] at $declIdent:ident",
    ("Mathlib/Tactic/Lift.lean", 8740): "simp -failIfUnchanged only [← $newEqIdent]",
}
SOURCE_HASHES = {
    "Mathlib/Tactic/DeriveEncodable.lean": "cd54a8c4e5f61292446d64d9a58dcad41df0cda67733601fb6074efbbd1498a9",
    "Mathlib/Tactic/Lift.lean": "a0e8117b3064286e00da19c0e338c3c3a425c701720992134cd4a87e68c84e2f",
    "Mathlib/Tactic/Nontriviality/Core.lean": "e6038583b48c41e4cc873e22701d699f2ddce9deb3a521697a52d3dfac217f4f",
    "Mathlib/Tactic/Zify.lean": "f0ce5e1e74c0a884b5bce026651e0efc15723caaae87cbac0e6c1f3a54a84da3",
}

# The one retained syntax/data call and the three dynamic calls remain
# explicitly accounted for.  They are never passed to the materializer.
RETAINED_SYNTAX_DATA = {
    "Mathlib/Tactic/Zify.lean": (2404, 2471, "b3360f1193c3c8b2", "simp -decide only [zify_simps, push_cast, $args,*] $[at $location]?")
}
UNSUPPORTED_DYNAMIC = {
    "Mathlib/Tactic/DeriveEncodable.lean": (10757, 10797, "8a18ca2cc5877278", "simp only [Encodable.encodek, $lemmas,*]"),
    "Mathlib/Tactic/Nontriviality/Core.lean": (1780, 1798, "35beee1afee45baf", "simp [$simpArgs,*]"),
    "Mathlib/Tactic/Zify.lean": (2739, 2789, "87ef8f8d4afcf255", "simp -decide only [zify_simps, push_cast, $args,*]"),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _source_path(module: str) -> Path:
    path = (MATHLIB / Path(*module.split("/"))).resolve()
    path.relative_to(MATHLIB.resolve())
    if not path.is_file():
        raise RuntimeError(f"missing pinned source: {path}")
    return path


def _render(source: bytes, start: int, end: int, replacement: str) -> bytes:
    original = source[start:end].decode("utf-8")
    first, separator, rest = replacement.partition("\n")
    column = len(source[:start].decode("utf-8").rsplit("\n", 1)[-1].expandtabs(8))
    indent = " " * (column + 2)
    comments = [indent + "-- Original simp:"]
    comments.extend(indent + "-- " + line for line in original.split("\n"))
    suffix = rest if separator else indent[:-2]
    return (first + "\n" + "\n".join(comments) + "\n" + suffix).encode("utf-8")


def _apply(source: bytes, entries: list[tuple[int, int, str]]) -> bytes:
    chunks: list[bytes] = []
    cursor = 0
    for start, end, replacement in entries:
        chunks.extend((source[cursor:start], _render(source, start, end, replacement)))
        cursor = end
    chunks.append(source[cursor:])
    return b"".join(chunks)


def _imports(source: bytes) -> list[str]:
    # Module headers contain only the import forms below.  Stop at the first
    # non-header command so an import-looking docstring cannot be accepted.
    result: list[str] = []
    header = source.decode("utf-8").splitlines()
    for line in header:
        stripped = line.strip()
        if not stripped or stripped.startswith("/-") or stripped.startswith("--"):
            continue
        match = re.fullmatch(r"(?:(?:public|private|scoped|noncomputable|meta)\s+)*import\s+([A-Za-z0-9_.]+)", stripped)
        if match:
            result.append(match.group(1))
            continue
        if stripped == "module":
            continue
        # Header options and namespace declarations are not imports.  Once a
        # declaration starts, no later import is trusted by this audit.
        if stripped.startswith("set_option "):
            continue
        break
    return result


def _check_imports(source: bytes, module: str, lean_path: list[Path]) -> None:
    for imported in _imports(source):
        relative = Path(*imported.split("."))
        if any((root / (str(relative) + suffix)).is_file() for root in lean_path for suffix in (".olean", ".ilean")):
            continue
        raise RuntimeError(f"{module}: import is not resolvable in pinned search path: {imported}")


def _lean_path() -> list[Path]:
    completed = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=CAMPAIGN_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(f"could not read pinned LEAN_PATH:\n{completed.stdout}")
    values = [Path(item) for item in completed.stdout.splitlines() if item]
    if not values:
        raise RuntimeError("pinned LEAN_PATH is empty")
    return values


def _compile(path: Path, lean_path: list[Path]) -> str:
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(str(value) for value in lean_path)
    completed = subprocess.run(
        ["lean", str(path)],
        cwd=CAMPAIGN_ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(f"materialized module failed to compile: {path}\n{completed.stdout}")
    if re.search(r"\b(error|declaration uses 'sorry'):\s*", completed.stdout):
        raise RuntimeError(f"compiler emitted an error/sorry diagnostic for {path}:\n{completed.stdout}")
    return completed.stdout


def _check_dynamic_records() -> None:
    for module, (start, end, occurrence, expected) in {**RETAINED_SYNTAX_DATA, **UNSUPPORTED_DYNAMIC}.items():
        source = _source_path(module).read_bytes()
        if sha256(source) != SOURCE_HASHES[module]:
            raise RuntimeError(f"source hash changed for {module}")
        actual = source[start:end].decode("utf-8")
        if actual != expected:
            raise RuntimeError(f"stale dynamic record {module}:{start}: {actual!r} != {expected!r}")
        if inventory.occurrence_id(module, start, end) != occurrence:
            raise RuntimeError(f"stale occurrence identity for {module}:{start}")
        if module.endswith("Zify.lean") and start == 2404:
            before = source[:start]
            if b"macro_rules" not in before[-1200:] or b"`(tactic|" not in before[-500:]:
                raise RuntimeError("Zify retained call is no longer guarded as macro syntax/data")


def main() -> int:
    if not MATHLIB.is_dir():
        raise RuntimeError(f"pinned Mathlib package is unavailable: {MATHLIB}")
    if subprocess.check_output(["git", "-C", str(MATHLIB), "rev-parse", "HEAD"], text=True).strip() != "905b95818eb32af7874a58b427f50c1711a5e96c":
        raise RuntimeError("manual overrides are bound to a different Mathlib commit")
    if subprocess.check_output(["git", "-C", str(MATHLIB), "status", "--porcelain"], text=True):
        raise RuntimeError("pinned Mathlib checkout is dirty")

    lean_path = _lean_path()
    by_module: dict[str, list[tuple[int, int, str]]] = {}
    for module, positions in MODULES.items():
        source = _source_path(module).read_bytes()
        if sha256(source) != SOURCE_HASHES[module]:
            raise RuntimeError(f"source hash changed for {module}")
        _check_imports(source, module, lean_path)
        module_entries: list[tuple[int, int, str]] = []
        for start, replacement in positions.items():
            expected = SUPPORTED_SOURCE[(module, start)]
            end = start + len(expected.encode("utf-8"))
            actual = source[start:end].decode("utf-8")
            if actual != expected:
                raise RuntimeError(f"stale source range at {module}:{start}: {actual!r} != {expected!r}")
            if inventory.occurrence_id(module, start, end) not in {
                "ba6410d96ffc0357", "f775b816b6c6b9de", "471aa4d60b0acdd6", "2aee64956119f34b",
                "b2288ad41bec49c3", "d9b60e8150d86521", "6c2a52e93b5afdd3",
            }:
                raise RuntimeError(f"unexpected supported occurrence identity at {module}:{start}")
            module_entries.append((start, end, replacement))
        by_module[module] = module_entries

    _check_dynamic_records()
    with tempfile.TemporaryDirectory(prefix="excluded-simp-") as temporary:
        root = Path(temporary)
        for module, module_entries in by_module.items():
            source = _source_path(module).read_bytes()
            patched = _apply(source, module_entries)
            destination = root / Path(*module.split("/"))
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(patched)
            if patched.count(b"-- Original simp:") != len(module_entries):
                raise RuntimeError(f"{module}: replacement did not preserve every original call comment")
            _compile(destination, lean_path)
    print("excluded simp check: 7 deterministic replacements compiled; 3 dynamic calls fail-closed; 1 Zify syntax/data call retained")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"excluded simp check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
