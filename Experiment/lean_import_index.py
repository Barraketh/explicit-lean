#!/usr/bin/env python3
"""Build a source-bound dependency map with Lean's native header parser.

The parser is run once per bounded argument batch and never elaborates an
imported module. The output is accepted by ``translation_index.import_manifest``:

    python3 Experiment/lean_import_index.py \
      --manifest .lake/search-free-mathlib/snapshots/corpus-bootstrap/.lake/campaign-inventory.json \
      --source-root .lake/packages/mathlib \
      --output .lake/week-2026-08-31/index-header-dependency-map.json

Every output key is ``<module>@<sourceHash>``. Source hashes are checked both
before and after parsing; output is replaced atomically only after every batch
is complete and all records join the manifest exactly.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any, Iterable

from process_runner import run_process


ROOT = Path(__file__).resolve().parents[1]
LEAN_TOOL = ROOT / "Experiment" / "LeanImportIndex.lean"


def _source_records(manifest_path: Path, source_root: Path) -> list[dict[str, str]]:
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot read manifest {manifest_path}: {error}") from error
    modules = manifest.get("modules") if isinstance(manifest, dict) else None
    if not isinstance(modules, list):
        raise ValueError("manifest modules must be an array")
    records: list[dict[str, str]] = []
    seen: set[str] = set()
    root = source_root.resolve()
    for raw in modules:
        if not isinstance(raw, dict) or not all(isinstance(raw.get(k), str) and raw[k] for k in ("module", "sourceHash")):
            raise ValueError("manifest module records need module and sourceHash strings")
        module = raw["module"]
        if module in seen:
            raise ValueError(f"duplicate module record: {module}")
        seen.add(module)
        path = (root / module).resolve()
        try:
            path.relative_to(root)
        except ValueError as error:
            raise ValueError(f"module escapes source root: {module}") from error
        records.append({"module": module, "sourceHash": raw["sourceHash"], "path": str(path)})
    return records


def _verify_hashes(records: Iterable[dict[str, str]]) -> None:
    for record in records:
        path = Path(record["path"])
        try:
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
        except OSError as error:
            raise ValueError(f"cannot read source {path}: {error}") from error
        if actual != record["sourceHash"]:
            raise ValueError(f"source changed or hash mismatch for {record['module']}")


def _batches(records: list[dict[str, str]], max_argument_bytes: int) -> Iterable[list[dict[str, str]]]:
    if max_argument_bytes <= 0:
        raise ValueError("max argument bytes must be positive")
    batch: list[dict[str, str]] = []
    size = 0
    for record in records:
        path_size = len(record["path"].encode()) + 1
        if batch and size + path_size > max_argument_bytes:
            yield batch
            batch = []
            size = 0
        if path_size > max_argument_bytes:
            raise ValueError(f"source path exceeds max argument bytes: {record['path']}")
        batch.append(record)
        size += path_size
    if batch:
        yield batch


def build_map(
    manifest_path: str | Path,
    source_root: str | Path,
    *,
    max_argument_bytes: int = 200_000,
    timeout: float = 300,
) -> dict[str, dict[str, Any]]:
    manifest = Path(manifest_path).resolve()
    root = Path(source_root).resolve()
    records = _source_records(manifest, root)
    _verify_hashes(records)
    by_path = {record["path"]: record for record in records}
    result: dict[str, dict[str, Any]] = {}
    for batch in _batches(records, max_argument_bytes):
        command = ["lake", "env", "lean", "--run", str(LEAN_TOOL), *(record["path"] for record in batch)]
        completed = run_process(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        if completed.returncode:
            detail = (completed.stderr or completed.stdout or "").strip()
            raise ValueError(f"native header parser failed ({completed.returncode}): {detail[:2000]}")
        seen_paths: set[str] = set()
        for line in completed.stdout.splitlines():
            path, separator, imports = line.partition("\t")
            if not separator or path not in by_path or path in seen_paths:
                raise ValueError(f"invalid native header output: {line[:200]}")
            seen_paths.add(path)
            record = by_path[path]
            names = [] if not imports else imports.split(",")
            if any(not name for name in names):
                raise ValueError(f"invalid empty import in native output: {path}")
            key = f"{record['module']}@{record['sourceHash']}"
            result[key] = {
                "module": record["module"],
                "sourceHash": record["sourceHash"],
                "dependencies": names,
            }
        expected = {record["path"] for record in batch}
        if seen_paths != expected:
            raise ValueError(f"native header output omitted {len(expected - seen_paths)} source files")
    _verify_hashes(records)
    if len(result) != len(records):
        raise ValueError(f"native dependency map has {len(result)} entries, expected {len(records)}")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--source-root", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--max-argument-bytes", type=int, default=200_000)
    parser.add_argument("--timeout", type=float, default=300)
    args = parser.parse_args(argv)
    temporary_name = None
    try:
        output = Path(args.output).resolve()
        source_root = Path(args.source_root).resolve()
        if output == Path(args.manifest).resolve() or output.is_relative_to(source_root):
            raise ValueError("output must not overwrite the manifest or source tree")
        if output.is_relative_to((ROOT / ".lake/packages").resolve()):
            raise ValueError("output must be outside shared package trees")
        if output.is_dir():
            raise ValueError("output must be a file path")
        value = build_map(
            args.manifest,
            args.source_root,
            max_argument_bytes=args.max_argument_bytes,
            timeout=args.timeout,
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=output.parent, prefix=f".{output.name}.", delete=False) as temporary:
            json.dump(value, temporary, sort_keys=True, separators=(",", ":"))
            temporary.write("\n")
            temporary_name = Path(temporary.name)
        temporary_name.replace(output)
        print(json.dumps({"entries": len(value), "output": str(output)}, sort_keys=True))
        return 0
    except (OSError, ValueError) as error:
        print(f"lean-import-index: {error}", file=sys.stderr)
        return 2
    finally:
        if temporary_name is not None:
            temporary_name.unlink(missing_ok=True)


if __name__ == "__main__":
    raise SystemExit(main())
