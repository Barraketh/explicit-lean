#!/usr/bin/env python3
"""Certify one newly emitted module family, without publishing it for imports.

The caller supplies a strict ImportEnvironment and the complete dependency
families required by its graph. This helper verifies every supplied family;
it does not discover that graph, reuse old outputs, or establish corpus/comment
provenance acceptance. Outputs remain quarantined even after certification.
"""
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Mapping

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_scope as scope
import check_simp_engine_command_audit as audit
import process_runner
import translated_imports
from translated_imports import ImportEnvironment

ROOT = Path(__file__).resolve().parents[1]
KIND = "simp_engine_certified_module"
SCHEMA = 1
SUFFIXES = (".olean", ".olean.server", ".olean.private", ".ir")


@dataclass(frozen=True)
class InputFile:
    path: Path
    sha256: str


@dataclass(frozen=True)
class Certification:
    receipt_path: Path
    receipt_sha256: str
    receipt: dict


class CertificationError(RuntimeError):
    def __init__(self, message: str, work_directory: Path | None = None):
        super().__init__(message)
        self.work_directory = work_directory


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _path(path: Path, *, directory: bool = False) -> Path:
    path = Path(os.path.abspath(path))
    if path.resolve(strict=True) != path or path.is_symlink():
        raise RuntimeError(f"symlink path is not an immutable input/output: {path}")
    if not (path.is_dir() if directory else path.is_file()):
        raise RuntimeError(f"expected {'directory' if directory else 'regular file'}: {path}")
    return path


def _checked_file(item: InputFile) -> InputFile:
    if not isinstance(item.sha256, str) or not re.fullmatch(r"[0-9a-f]{64}", item.sha256):
        raise RuntimeError("invalid expected SHA256")
    path = _path(item.path)
    if sha256(path) != item.sha256:
        raise RuntimeError(f"input hash mismatch: {path}")
    return InputFile(path, item.sha256)


def _module_path(module: str) -> Path:
    if not isinstance(module, str) or not module or any(
        not part or part in {".", ".."} or any(c.isspace() or c in "/\\\0" for c in part)
        for part in module.split(".")
    ):
        raise RuntimeError("invalid module identity")
    return Path(*module.split(".")).with_suffix(".olean")


def _outside(path: Path, roots: tuple[Path, ...]) -> None:
    for root in roots:
        if path.is_relative_to(root) or root.is_relative_to(path):
            raise RuntimeError(f"quarantine intersects import search root: {root}")


def _environment(imports: ImportEnvironment) -> tuple[tuple[Path, ...], dict]:
    paths = tuple(_path(p, directory=True) for p in imports.search_path)
    translated = _path(imports.translated_olean_root, directory=True)
    if not paths or paths[0] != translated or len(set(paths)) != len(paths):
        raise RuntimeError("invalid strict import search path")
    if any(p != translated and translated_imports._contains_mathlib_modules(p) for p in paths):
        raise RuntimeError("stock or shadow Mathlib root in strict import environment")
    sysroot = _path(imports.lean_sysroot, directory=True)
    lean = _path(imports.lean_binary)
    if lean != sysroot / "bin/lean" or sysroot / "lib/lean" not in paths:
        raise RuntimeError("strict environment has inconsistent Lean toolchain paths")
    # Only selected source files are certified. Do not advertise the caller's
    # possibly stale whole-source-tree hash as something rechecked here.
    identity = {"searchPath": [str(p) for p in paths], "leanSysroot": str(sysroot),
                "leanBinary": {"path": str(lean), "sha256": sha256(lean)}}
    return paths, identity


def _dependencies(dependencies: Mapping[str, Mapping[str | Path, str]],
                  paths: tuple[Path, ...], module: str) -> dict[str, dict[str, str]]:
    result = {}
    for dependency, values in dependencies.items():
        if dependency == module:
            raise RuntimeError("module cannot depend on its own output")
        relative = _module_path(dependency)
        matches = [p / relative for p in paths if (p / relative).exists()]
        if not matches:
            raise RuntimeError(f"missing dependency artifact: {dependency}")
        primary = _path(matches[0])
        if (dependency == "Mathlib" or dependency.startswith("Mathlib.")) and primary != paths[0] / relative:
            raise RuntimeError(f"dependency did not resolve from translated root: {dependency}")
        checked = dict((str(item.path), item.sha256) for item in
                       (_checked_file(InputFile(Path(p), h)) for p, h in values.items()))
        expected_one = {str(primary)}
        expected_all = {str(primary.with_suffix(s)) for s in SUFFIXES}
        if set(checked) not in (expected_one, expected_all):
            raise RuntimeError(f"incomplete dependency artifact family: {dependency}")
        actual = {str(primary.with_suffix(s)) for s in SUFFIXES
                  if primary.with_suffix(s).exists() or primary.with_suffix(s).is_symlink()}
        if actual != set(checked):
            raise RuntimeError(f"dependency companion inventory changed: {dependency}")
        result[dependency] = checked
    return result


def _target_absent(paths: tuple[Path, ...], module: str) -> None:
    primary = paths[0] / _module_path(module)
    if any(primary.with_suffix(s).exists() or primary.with_suffix(s).is_symlink() for s in SUFFIXES):
        raise RuntimeError("target artifacts already present in translated import root")


def _artifact_family(quarantine: Path, output: Path, is_module: bool) -> dict[str, str]:
    _path(quarantine, directory=True)
    files = {output.with_suffix(s) for s in (SUFFIXES if is_module else SUFFIXES[:1])}
    allowed = set(files)
    for path in files:
        allowed.update(p for p in path.parents if p != quarantine and p.is_relative_to(quarantine))
    if set(quarantine.rglob("*")) != allowed:
        raise RuntimeError("incomplete or unexpected output artifact family (postponed IR is unsupported)")
    result = {}
    for path in files:
        _path(path)
        if not path.stat().st_size:
            raise RuntimeError(f"empty output artifact: {path}")
        result[str(path)] = sha256(path)
    return dict(sorted(result.items()))


def validate_observation(output: str, *, exit_code: int, module: str, nonce: str,
                         stock: audit.ExpectedAudit, applied: audit.ExpectedAudit) -> dict:
    """Validate an observation; this alone never creates a certification receipt."""
    if (stock.module, applied.module, stock.label, applied.label) != (module, module, "stock", "applied") or \
            type(stock.is_module) is not bool or type(applied.is_module) is not bool or \
            stock.is_module != applied.is_module:
        raise RuntimeError("inconsistent observation identities")
    protocol.check_replay_abort_markers(output, expected_nonce=nonce, expected_module=module)
    if exit_code != 0:
        raise RuntimeError(f"declaration oracle exited with code {exit_code}")
    report = materializer._parse_declaration_oracle(output, module)
    if report["status"] != "success":
        raise RuntimeError("declaration oracle did not succeed")
    records = audit.parse_audits(output, expected_nonce=nonce, expected=[stock, applied])
    audit.require_clear(records[1])
    return {"declarationOracle": report, "commandAudits": records}


def _publish_json(path: Path, data: dict) -> None:
    """Publish a complete new record, refusing to overwrite any prior path."""
    fd, name = tempfile.mkstemp(prefix=".record-", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(data, stream, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)
        directory_fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)


def _sync_evidence(work: Path, paths: list[Path]) -> None:
    """Make artifact/evidence bytes and their directory entries durable first."""
    directories = {work, work.parent}
    for path in paths:
        with _path(path).open("rb") as stream:
            os.fsync(stream.fileno())
        directories.update(p for p in path.parents if p.is_relative_to(work))
    for directory in sorted(directories, key=lambda p: len(p.parts), reverse=True):
        descriptor = os.open(_path(directory, directory=True), os.O_RDONLY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)


def certify_module(*, module: str, stock: InputFile, applied: InputFile,
                   is_module: bool, oracle: InputFile, imports: ImportEnvironment,
                   dependencies: Mapping[str, Mapping[str | Path, str]],
                   work_parent: Path, timeout: float = 900) -> Certification:
    """Run one fresh source-pair oracle and retain its certified output in quarantine.

    Dependency closure completeness belongs to the caller. A receipt binds only
    the supplied families, selected source bytes, tool, environment and this run.
    External package/core/runtime files need a separate caller-owned manifest
    when they are not included among the supplied dependency families.
    Callers must keep inputs immutable and recheck receipt hashes before promotion.
    On failure, evidence and any partial outputs remain under work_directory;
    no success receipt is written and nothing enters an import search root.
    """
    work = None
    try:
        _module_path(module)
        if type(is_module) is not bool or isinstance(timeout, bool) or not math.isfinite(timeout) or timeout <= 0:
            raise RuntimeError("invalid module mode or timeout")
        stock, applied, oracle = map(_checked_file, (stock, applied, oracle))
        if not os.access(oracle.path, os.X_OK):
            raise RuntimeError("oracle is not an executable file")
        paths, environment_identity = _environment(imports)
        dep_hashes = _dependencies(dependencies, paths, module)
        _target_absent(paths, module)
        parent = _path(work_parent, directory=True)
        if any(parent.is_relative_to(p) for p in paths):
            raise RuntimeError("work parent lies inside an import search root")
        work = Path(tempfile.mkdtemp(prefix="certified-module-", dir=parent))
        _outside(work, paths)
        quarantine = work / "quarantine"
        quarantine.mkdir()
        output = quarantine / _module_path(module)
        output.parent.mkdir(parents=True, exist_ok=True)
        sources = {"stock": stock.path.read_bytes(), "applied": applied.path.read_bytes()}
        for label, item in (("stock", stock), ("applied", applied)):
            if hashlib.sha256(sources[label]).hexdigest() != item.sha256:
                raise RuntimeError(f"source changed while archiving: {item.path}")
            (work / f"{label}.lean").write_bytes(sources[label])
        implementation = {str(_path(Path(m.__file__))): sha256(Path(m.__file__)) for m in
                          (materializer, protocol, scope, audit, process_runner, translated_imports)}
        implementation[str(Path(__file__).resolve())] = sha256(Path(__file__).resolve())
        nonce = protocol.fresh_run_nonce()
        env = imports.environment()
        env.update({protocol.RUN_NONCE_ENV: nonce, audit.ENABLE_ENV: "1",
                    "LEAN_PATH": os.pathsep.join(str(p) for p in paths),
                    "LEAN_SYSROOT": environment_identity["leanSysroot"]})
        command = [str(oracle.path), module, str(stock.path), str(applied.path), "--olean", str(output)]
        _publish_json(work / "invocation.json", {"command": command, "nonce": nonce,
                      "environment": environment_identity, "module": module})
        log = work / "oracle.log"
        try:
            process = process_runner.run_process(command, cwd=ROOT, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, check=False)
        except subprocess.TimeoutExpired as error:
            partial = error.output or b""
            log.write_text(partial.decode("utf-8", errors="replace") if isinstance(partial, bytes) else partial)
            raise RuntimeError("certified module oracle timed out") from error
        log.write_text(process.stdout, encoding="utf-8")
        log_hash = hashlib.sha256(process.stdout.encode("utf-8")).hexdigest()
        observed = validate_observation(process.stdout, exit_code=process.returncode, module=module, nonce=nonce,
            stock=audit.ExpectedAudit(module, stock.path, sources["stock"], "stock", is_module),
            applied=audit.ExpectedAudit(module, applied.path, sources["applied"], "applied", is_module))
        family = _artifact_family(quarantine, output, is_module)
        for item in (stock, applied, oracle):
            _checked_file(item)
        for path, digest in implementation.items():
            _checked_file(InputFile(Path(path), digest))
        if _environment(imports) != (paths, environment_identity):
            raise RuntimeError("import environment changed during certification")
        if _dependencies(dependencies, paths, module) != dep_hashes:
            raise RuntimeError("dependency families changed during certification")
        _target_absent(paths, module)
        _outside(_path(work, directory=True), paths)
        for label, item in (("stock", stock), ("applied", applied)):
            _checked_file(InputFile(work / f"{label}.lean", item.sha256))
        if _artifact_family(quarantine, output, is_module) != family:
            raise RuntimeError("output family changed during certification")
        _checked_file(InputFile(log, log_hash))
        _sync_evidence(work, [*(Path(p) for p in family), log, work / "stock.lean",
                              work / "applied.lean", work / "invocation.json"])
        receipt = {"kind": KIND, "schema": SCHEMA, "status": "certified_in_quarantine",
                   "module": module, "isModule": is_module, "nonce": nonce, "command": command,
                   "createdAt": datetime.now(timezone.utc).isoformat(), "exitCode": process.returncode,
                   "stock": {"path": str(stock.path), "sha256": stock.sha256, "archivePath": str(work / "stock.lean")},
                   "applied": {"path": str(applied.path), "sha256": applied.sha256, "archivePath": str(work / "applied.lean")},
                   "oracleExecutable": {"path": str(oracle.path), "sha256": oracle.sha256},
                   "implementationHashes": implementation, "importEnvironment": environment_identity,
                   "dependencyArtifactFamilies": dep_hashes, "dependencyScope": "caller_supplied_families",
                   "outputArtifactFamily": family, "log": {"path": str(log), "sha256": log_hash},
                   "quarantine": str(quarantine), "promoted": False, "acceptedCampaignCoverage": False,
                   "sourceCommentProvenanceAccepted": False,
                   **observed}
        receipt_path = work / "receipt.json"
        _publish_json(receipt_path, receipt)
        return Certification(receipt_path, sha256(receipt_path), receipt)
    except Exception as error:
        detail = str(error)
        if work is not None and work.is_dir():
            failure = {"kind": KIND + "_failure", "schema": SCHEMA, "module": module,
                       "error": str(error), "acceptedCampaignCoverage": False, "promoted": False}
            try:
                _publish_json(work / "failure.json", failure)
            except Exception as evidence_error:
                detail += f"; could not archive failure: {evidence_error}"
        raise CertificationError(detail, work) from error
