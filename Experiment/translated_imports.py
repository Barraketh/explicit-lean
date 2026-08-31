#!/usr/bin/env python3
"""Construct a strict, Lake-independent Lean import environment.

The project uses prebuilt Mathlib oleans.  A translated tree must put its own
oleans first while making every stock root containing ``Mathlib/`` unavailable;
otherwise Lean can silently accept an unbuilt translated dependency from the
locked package.  This module discovers the non-Mathlib package roots through
``lake env printenv`` once, then invokes the pinned Lean binary directly with
an explicit ``LEAN_PATH``.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Iterable, Sequence

from process_runner import run_process


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TIMEOUT = 60
LEAN_VERSION = "4.32.2"
LEAN_COMMIT = "f3b06c705e6c85f5314019d5d3baab0fec5b580c"


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _resolve_existing(path: str | Path, label: str) -> Path:
    value = Path(path).expanduser().resolve()
    if not value.exists():
        raise RuntimeError(f"{label} does not exist: {value}")
    return value


def _canonical_paths(paths: Iterable[str | Path]) -> list[Path]:
    result: list[Path] = []
    seen: set[Path] = set()
    for raw in paths:
        path = Path(raw).expanduser().resolve()
        if not path.is_dir():
            raise RuntimeError(f"Lean search path is not a directory: {path}")
        if path not in seen:
            result.append(path)
            seen.add(path)
    return result


def _run_lake_env(timeout: int = DEFAULT_TIMEOUT) -> dict[str, str]:
    """Read only Lean lookup variables without invoking a build target."""
    try:
        completed = run_process(
            ["lake", "env", "printenv", "LEAN_PATH", "LEAN_SYSROOT"],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except OSError as error:
        raise RuntimeError(f"cannot execute lake env printenv: {error}") from error
    # `printenv` returns 1 when one requested variable is unset; this Lake
    # version leaves LEAN_SYSROOT unset, so retain the first value and derive
    # the sysroot below. Any other failure remains fatal.
    if completed.returncode not in {0, 1}:
        raise RuntimeError(
            f"lake env printenv failed ({completed.returncode}):\n{completed.stderr[-4000:]}"
        )
    # `printenv` emits values without names, and this Lake currently omits the
    # unset LEAN_SYSROOT.  LEAN_PATH is requested first; derive the sysroot
    # through the non-building `--print-prefix` query in that case.
    lines = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
    if not lines:
        raise RuntimeError("lake env printenv returned no LEAN_PATH")
    values = {"LEAN_PATH": lines[0]}
    if len(lines) >= 2:
        values["LEAN_SYSROOT"] = lines[1]
    else:
        try:
            prefix = run_process(
                ["lake", "env", "lean", "--print-prefix"],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
                check=False,
            )
        except OSError as error:
            raise RuntimeError(f"cannot query Lean prefix: {error}") from error
        if prefix.returncode != 0:
            raise RuntimeError(
                f"lake env lean --print-prefix failed ({prefix.returncode}):\n"
                f"{prefix.stderr[-4000:]}"
            )
        values["LEAN_SYSROOT"] = prefix.stdout.strip().splitlines()[-1]
    if not values.get("LEAN_PATH") or not values.get("LEAN_SYSROOT"):
        raise RuntimeError("could not derive LEAN_PATH and LEAN_SYSROOT")
    return values


def _contains_mathlib_modules(root: Path) -> bool:
    """Return true for any root that could satisfy a Mathlib module import."""
    return (root / "Mathlib").is_dir() or (root / "Mathlib.olean").is_file()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _source_tree_hash(source_root: Path) -> str:
    """Hash the source files that can affect module resolution/elaboration."""
    digest = hashlib.sha256()
    files = sorted(path for path in source_root.rglob("*.lean") if path.is_file())
    for path in files:
        relative = path.relative_to(source_root).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        data = path.read_bytes()
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(data)
    return digest.hexdigest()


def _search_path_hash(paths: Sequence[Path]) -> str:
    payload = json.dumps(
        [path.as_posix() for path in paths],
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")
    return _sha256_bytes(payload)


def _module_relative(module: str, suffix: str) -> Path:
    if not module or module.startswith(".") or any(part in {"", ".", ".."} for part in module.split(".")):
        raise RuntimeError(f"invalid Lean module name: {module!r}")
    if module != "Mathlib" and not module.startswith("Mathlib."):
        raise RuntimeError(f"resolution audit only accepts Mathlib modules: {module!r}")
    return Path(*module.split(".")).with_suffix(suffix)


@dataclass(frozen=True)
class ImportEnvironment:
    source_root: Path
    translated_olean_root: Path
    lean_binary: Path
    lean_sysroot: Path
    search_path: tuple[Path, ...]
    excluded_roots: tuple[Path, ...]
    unavailable_roots: tuple[Path, ...]
    source_hash: str
    search_path_hash: str

    def result(self) -> dict[str, object]:
        return {
            "sourceRoot": str(self.source_root),
            "translatedOleanRoot": str(self.translated_olean_root),
            "leanBinary": str(self.lean_binary),
            "leanSysroot": str(self.lean_sysroot),
            "searchPath": [str(path) for path in self.search_path],
            "excludedRoots": [str(path) for path in self.excluded_roots],
            "unavailableRoots": [str(path) for path in self.unavailable_roots],
            "sourceHash": self.source_hash,
            "searchPathHash": self.search_path_hash,
            "leanBinarySha256": _sha256_file(self.lean_binary),
            "leanVersion": LEAN_VERSION,
            "leanCommit": LEAN_COMMIT,
        }

    def environment(self) -> dict[str, str]:
        """Return the complete environment used by direct pinned Lean calls."""
        # Preserve ordinary process settings needed by elaborators and their
        # subprocesses, while replacing only Lean's lookup inputs.  The
        # absolute binary path below means PATH cannot select another Lean;
        # direct invocation also prevents Lake from appending stock roots.
        environment = os.environ.copy()
        environment.update(
            {
                "LEAN_PATH": os.pathsep.join(str(path) for path in self.search_path),
                "LEAN_SYSROOT": str(self.lean_sysroot),
            }
        )
        return environment

    def resolve_mathlib(self, modules: Sequence[str], *, require_all: bool = True) -> dict[str, dict[str, object]]:
        """Audit the exact olean chosen for each requested Mathlib module.

        Resolution is a filesystem audit performed before compilation.  The
        first matching root is reported; a missing translated olean is an error
        even if a caller still has a stock source or olean elsewhere on disk.
        """
        result: dict[str, dict[str, object]] = {}
        for module in modules:
            relative = _module_relative(module, ".olean")
            matches = [
                root / relative
                for root in self.search_path
                if (root / relative).is_file()
            ]
            translated = self.translated_olean_root / relative
            translated_root = self.translated_olean_root.resolve()
            if translated.is_symlink() or translated.exists():
                # Resolve the complete path, not just a final symlink: an
                # ancestor directory symlink can otherwise escape the run
                # root while still making ``translated.is_symlink()`` false.
                resolved_translated = translated.resolve()
                try:
                    resolved_translated.relative_to(translated_root)
                except ValueError as error:
                    raise RuntimeError(
                        f"translated olean escapes translated root for {module}: "
                        f"{resolved_translated}"
                    ) from error
            if require_all and not translated.is_file():
                raise RuntimeError(
                    f"translated olean is missing for {module}: {translated}"
                )
            if matches and matches[0] != translated:
                raise RuntimeError(
                    f"Mathlib resolution for {module} would use non-translated olean: "
                    f"{matches[0]}"
                )
            resolved_path = matches[0].resolve() if matches else None
            result[module] = {
                "module": module,
                "relative": relative.as_posix(),
                "translatedPath": str(translated),
                "resolvedPath": str(resolved_path) if resolved_path else None,
                "resolvedFromTranslatedRoot": bool(matches and matches[0] == translated),
                "availableMatches": [str(path.resolve()) for path in matches],
                "translatedSha256": _sha256_file(translated) if translated.is_file() else None,
                "resolvedSha256": _sha256_file(resolved_path) if resolved_path else None,
            }
        return result


def build_import_environment(
    source_root: str | Path,
    translated_olean_root: str | Path,
    *,
    lake_env: dict[str, str] | None = None,
    timeout: int = DEFAULT_TIMEOUT,
) -> ImportEnvironment:
    """Derive a strict search path with translated Mathlib precedence."""
    source = _resolve_existing(source_root, "source root")
    translated_input = Path(translated_olean_root).expanduser()
    if translated_input.is_symlink():
        raise RuntimeError(
            f"translated olean root must not be a symlink: {translated_input}"
        )
    translated = _resolve_existing(translated_olean_root, "translated olean root")
    if _contains_mathlib_modules(translated):
        # The olean root normally contains Mathlib/, which is expected.
        pass
    values = _run_lake_env(timeout) if lake_env is None else lake_env
    raw_paths = [Path(item) for item in values["LEAN_PATH"].split(os.pathsep) if item]
    unavailable = tuple(
        Path(item).expanduser().resolve()
        for item in raw_paths
        if not Path(item).expanduser().resolve().is_dir()
    )
    package_paths = _canonical_paths(
        path for path in raw_paths if Path(path).expanduser().resolve().is_dir()
    )
    excluded = tuple(path for path in package_paths if _contains_mathlib_modules(path))
    retained = [translated]
    retained.extend(path for path in package_paths if path not in excluded)
    sysroot = _resolve_existing(values["LEAN_SYSROOT"], "Lean sysroot")
    core_lib = sysroot / "lib" / "lean"
    if not core_lib.is_dir():
        raise RuntimeError(f"Lean core library directory is missing: {core_lib}")
    retained.append(core_lib)
    search_path = tuple(_canonical_paths(retained))
    if search_path[0] != translated:
        raise RuntimeError("translated olean root is not first in LEAN_PATH")
    if any(path != translated and _contains_mathlib_modules(path) for path in search_path):
        raise RuntimeError("a stock or shadow Mathlib root remains in LEAN_PATH")
    binary = sysroot / "bin" / "lean"
    if not binary.is_file():
        raise RuntimeError(f"pinned Lean binary is missing: {binary}")
    try:
        version = run_process(
            [str(binary), "--version"],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    except OSError as error:
        raise RuntimeError(f"cannot execute pinned Lean: {error}") from error
    identity = re.search(
        r"\bversion ([^,\s]+).*?\bcommit ([^,\s]+)", version.stdout
    )
    if (
        version.returncode != 0
        or identity is None
        or identity.group(1) != LEAN_VERSION
        or identity.group(2) != LEAN_COMMIT
    ):
        raise RuntimeError(
            f"unexpected pinned Lean binary identity: {version.stdout.strip()}"
        )
    return ImportEnvironment(
        source_root=source,
        translated_olean_root=translated,
        lean_binary=binary,
        lean_sysroot=sysroot,
        search_path=search_path,
        excluded_roots=excluded,
        unavailable_roots=unavailable,
        source_hash=_source_tree_hash(source),
        search_path_hash=_search_path_hash(search_path),
    )


def run_pinned_lean(
    imports: ImportEnvironment,
    arguments: Sequence[str],
    *,
    timeout: int = DEFAULT_TIMEOUT,
) -> subprocess.CompletedProcess[str]:
    """Run the pinned compiler without Lake or ambient search-path injection."""
    command = [str(imports.lean_binary), *arguments]
    return run_process(
        command,
        cwd=imports.source_root,
        env=imports.environment(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


__all__ = ["ImportEnvironment", "build_import_environment", "run_pinned_lean"]
