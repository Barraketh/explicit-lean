"""Immutable publication and output audits for cold-certified modules."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import tempfile
from typing import Mapping, Sequence

import certified_module as cm
import cold_certified_module as cold


KIND = "cold_certified_cone_publication"
SCHEMA = 1


def _files(root: Path) -> set[Path]:
    if root.is_symlink() or not root.is_dir():
        raise RuntimeError(f"publication root is not a regular directory: {root}")
    for path in root.rglob("*"):
        if path.is_symlink() and path.is_dir():
            raise RuntimeError(f"publication root contains a symlinked directory: {path}")
    return {path for path in root.rglob("*") if path.is_file() or path.is_symlink()}


def _module_path(root: Path, module: str, suffix: str) -> Path:
    path = root / cm._module_path(module).with_suffix(suffix)
    current = root
    for part in path.relative_to(root).parts[:-1]:
        current /= part
        if current.is_symlink():
            raise RuntimeError(f"publication path escapes through a symlink: {current}")
    return path


def _family(family: Mapping[str, str], module: str, is_module: bool) -> dict[str, str]:
    suffixes = cm.SUFFIXES if is_module else cm.SUFFIXES[:1]
    relative = cm._module_path(module)
    result: dict[str, str] = {}
    for raw, digest in family.items():
        path = Path(raw)
        suffix = next((s for s in suffixes if path.name == relative.with_suffix(s).name), None)
        if suffix is None or suffix in result:
            raise RuntimeError(f"unexpected certified family member for {module}")
        cm._checked_file(cm.InputFile(path, digest))
        result[str(path)] = digest
    if set(result) != {str(Path(raw)) for raw in family} or len(result) != len(suffixes):
        raise RuntimeError(f"incomplete certified family for {module}")
    return dict(sorted(result.items()))


def _publish_json(path: Path, value: Mapping[str, object]) -> str:
    payload = json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2).encode() + b"\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=".publication-", dir=path.parent)
    temporary_path = Path(temporary)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary_path, path)
    except FileExistsError as error:
        raise RuntimeError(f"refusing to overwrite publication receipt: {path}") from error
    finally:
        temporary_path.unlink(missing_ok=True)
    return cm.sha256(path)


def publish(cert: cold.Certification, *, output_root: str | Path,
            staging_parent: str | Path, receipt_root: str | Path) -> dict:
    record = cold.verify_certification(cert)
    root = Path(output_root).expanduser().absolute()
    staging = Path(staging_parent).expanduser().absolute()
    receipts = Path(receipt_root).expanduser().absolute()
    if root.is_symlink() or staging.is_symlink() or receipts.is_symlink():
        raise RuntimeError("publication roots must not be symlinks")
    root.mkdir(parents=True, exist_ok=True); staging.mkdir(parents=True, exist_ok=True)
    receipts.mkdir(parents=True, exist_ok=True)
    if root != Path(record["importEnvironment"]["searchPath"][0]):
        raise RuntimeError("publication root differs from certified import environment")
    module = record["module"]; is_module = record["isModule"]
    family = _family(record["outputArtifactFamily"], module, is_module)
    targets = {_module_path(root, module, s) for s in (cm.SUFFIXES if is_module else cm.SUFFIXES[:1])}
    receipt_path = _module_path(receipts, module, ".json")
    if any(path.exists() or path.is_symlink() for path in (*targets, receipt_path)):
        raise RuntimeError(f"publication would overwrite an existing artifact: {module}")
    stage = Path(tempfile.mkdtemp(prefix="publish-", dir=staging))
    try:
        copied: dict[Path, str] = {}
        for raw, digest in family.items():
            source = Path(raw); target = stage / source.name
            shutil.copyfile(source, target)
            cm._checked_file(cm.InputFile(target, digest)); copied[target] = digest
        result: dict[str, str] = {}
        for target, digest in zip(sorted(targets), [family[str(Path(raw))] for raw in sorted(family)]):
            target.parent.mkdir(parents=True, exist_ok=True)
            os.link(next(path for path, value in copied.items() if value == digest), target)
            cm._checked_file(cm.InputFile(target, digest)); result[str(target)] = digest
        publication = {"kind": KIND, "schema": SCHEMA, "module": module,
                       "isModule": is_module, "certification": {"path": str(cert.receipt_path), "sha256": cert.receipt_sha256},
                       "artifactFamily": result, "singleWriter": True}
        receipt_hash = _publish_json(receipt_path, publication)
        return {"path": str(receipt_path), "sha256": receipt_hash, **publication}
    finally:
        # The copied bytes are already linked into output; retaining the stage
        # as evidence is useful, but it is outside the published output root.
        pass


def verify_publications(records: Sequence[Mapping[str, object]], output_root: str | Path,
                        *, receipt_root: str | Path | None = None) -> dict[str, dict]:
    root = Path(output_root).expanduser().absolute()
    expected_output: dict[str, str] = {}
    expected_receipts: set[Path] = set()
    result: dict[str, dict] = {}
    for raw in records:
        if not isinstance(raw, Mapping) or not isinstance(raw.get("path"), str) or not isinstance(raw.get("sha256"), str):
            raise RuntimeError("publication record is incomplete")
        receipt = Path(raw["path"])
        cm._checked_file(cm.InputFile(receipt, raw["sha256"]))
        stored = json.loads(receipt.read_bytes())
        if stored != {key: value for key, value in raw.items() if key not in {"path", "sha256"}}:
            raise RuntimeError("publication receipt changed")
        module = stored.get("module")
        if not isinstance(module, str) or module in result:
            raise RuntimeError("duplicate published module")
        if type(stored.get("isModule")) is not bool:
            raise RuntimeError("publication module mode is invalid")
        family = stored.get("artifactFamily")
        if not isinstance(family, Mapping):
            raise RuntimeError("publication artifact family is incomplete")
        checked_family = _family(family, module, stored["isModule"])
        if checked_family != dict(family):
            raise RuntimeError("publication artifact family changed")
        expected_receipts.add(receipt)
        for path, digest in checked_family.items():
            if path in expected_output:
                raise RuntimeError("duplicate published artifact")
            cm._checked_file(cm.InputFile(Path(path), digest))
            expected_output[path] = digest
        result[module] = dict(stored)
    actual_output = _files(root)
    if actual_output != {Path(path) for path in expected_output}:
        raise RuntimeError("unreceipted, missing, or extra output artifact")
    if receipt_root is not None:
        receipt_directory = Path(receipt_root).expanduser().absolute()
        actual_receipts = _files(receipt_directory)
        if actual_receipts != expected_receipts:
            raise RuntimeError("unreceipted, missing, or extra publication receipt")
    return result


__all__ = ["publish", "verify_publications"]
