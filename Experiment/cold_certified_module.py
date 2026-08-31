#!/usr/bin/env python3
"""Bind source-pair semantics to independently compiled, ordinary Lean outputs.

Five fresh processes produce six quarantined artifact families: two ordinary
compilations, two single-source command audits, and an applied-first paired
oracle. Each source's three complete families must be byte-identical. This
detects serialized effects of process-global state; it does not assert purity
of arbitrary compiler/plugin I/O or certify dependency closure by itself.

The caller owns immutable inputs, complete dependency/runtime manifests, source
and comment provenance, and eventual publication. No output is promoted here.
"""
from __future__ import annotations

from dataclasses import replace
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Mapping

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import certified_module as base
import check_simp_engine_command_audit as audit
import process_runner
from translated_imports import ImportEnvironment

ROOT = Path(__file__).resolve().parents[1]
KIND = "simp_engine_cold_certified_module"
SCHEMA = 1
# V1 only compared re-exported metadata and is deliberately not accepted.
BRIDGE_MARKER = "SIMP_ENGINE_COLD_BRIDGE_ORACLE_V2 "
STAGES = ("ordinary-stock", "ordinary-applied", "audited-stock", "audited-applied", "bridge")
FAMILIES = ("ordinary-stock", "ordinary-applied", "audited-stock", "audited-applied", "bridge-stock", "bridge-applied")
# Same pinned options as both native tools. A drift that changes output fails
# the whole-family comparison; callers also bind tool/runtime identities.
PLAIN_OPTIONS = ("-DautoImplicit=false", "-DmaxSynthPendingDepth=3",
                 "-Dweak.linter.unusedVariables=false", "-Dweak.linter.unusedSimpArgs=false",
                 "-Dweak.linter.unreachableTactic=false", "-DmaxHeartbeats=0", "-DElab.async=true")
InputFile = base.InputFile
Certification = base.Certification
CertificationError = base.CertificationError


def _source_root(source: Path, module: str) -> Path:
    relative = base._module_path(module).with_suffix(".lean")
    if tuple(source.parts[-len(relative.parts):]) != relative.parts:
        raise RuntimeError("source path must end with its module-relative .lean path")
    root = source.parents[len(relative.parts) - 1]
    if root / relative != source:
        raise RuntimeError("ordinary frontend module identity mismatch")
    return base._path(root, directory=True)


def _commands(module: str, stock: Path, applied: Path, oracle: Path, auditor: Path,
              lean: Path, outputs: dict) -> dict[str, list[str]]:
    commands = {}
    for side, source in (("stock", stock), ("applied", applied)):
        commands["ordinary-" + side] = [str(lean), *PLAIN_OPTIONS,
            "-R", str(_source_root(source, module)), "-o", str(outputs["ordinary-" + side]), str(source)]
        commands["audited-" + side] = [str(auditor), module, str(source),
            "--olean", str(outputs["audited-" + side])]
    commands["bridge"] = [str(oracle), module, str(stock), str(applied),
        "--bridge-oleans", str(outputs["bridge-stock"]), str(outputs["bridge-applied"])]
    return commands


def validate_bridge(output: str, *, exit_code: int, module: str, nonce: str,
                    stock: audit.ExpectedAudit, applied: audit.ExpectedAudit) -> dict:
    """Validate new-mode framing/semantics/audits; not a cold-output certificate."""
    if (stock.module, applied.module, stock.label, applied.label) != (module, module, "stock", "applied") or \
            type(stock.is_module) is not bool or type(applied.is_module) is not bool or stock.is_module != applied.is_module:
        raise RuntimeError("inconsistent cold bridge identities")
    protocol.check_replay_abort_markers(output, expected_nonce=nonce, expected_module=module)
    if exit_code != 0:
        raise RuntimeError(f"cold bridge exited with code {exit_code}")
    if any(line.startswith((materializer.DECLARATION_ORACLE_MARKER, "SIMP_ENGINE_COLD_BRIDGE_ORACLE "))
           for line in output.splitlines()):
        raise RuntimeError("obsolete oracle marker is not a serialized cold bridge result")
    values = protocol.parse_framed_json_lines(output, marker=BRIDGE_MARKER,
        expected_nonce=nonce, label="cold bridge")
    if len(values) != 1:
        raise RuntimeError("cold bridge must emit exactly one nonce-framed result")
    # The native new mode retains the old strict semantic payload schema.
    report = materializer._parse_declaration_oracle(
        materializer.DECLARATION_ORACLE_MARKER + json.dumps(values[0]), module)
    if report["status"] != "success":
        raise RuntimeError("cold bridge semantic comparison did not succeed")
    records = audit.parse_audits(output, expected_nonce=nonce, expected=[applied, stock])
    audit.require_clear(records[0])
    return {"declarationOracle": report, "commandAudits": records, "auditOrder": ["applied", "stock"]}


def _family_digest(family: Mapping[str, str], output: Path, is_module: bool) -> dict[str, str]:
    suffixes = base.SUFFIXES if is_module else base.SUFFIXES[:1]
    expected = {str(output.with_suffix(s)) for s in suffixes}
    if set(family) != expected:
        raise RuntimeError("unexpected cold family identity")
    return {s: family[str(output.with_suffix(s))] for s in suffixes}


def _same_source_families(families: dict, outputs: dict, is_module: bool) -> dict:
    comparisons = {}
    for side in ("stock", "applied"):
        ordinary = _family_digest(families["ordinary-" + side], outputs["ordinary-" + side], is_module)
        for kind in ("audited", "bridge"):
            actual = _family_digest(families[kind + "-" + side], outputs[kind + "-" + side], is_module)
            if actual != ordinary:
                changed = [s for s in ordinary if actual[s] != ordinary[s]]
                raise RuntimeError(f"cold artifact mismatch: {side} {kind}: {changed}")
        comparisons[side] = ordinary
    return comparisons


def _observe(log: str, event: dict, identities: dict) -> dict:
    stage = event["stage"]
    protocol.check_replay_abort_markers(log, expected_nonce=event["nonce"], expected_module=identities["stock"].module)
    if event["exitCode"] != 0:
        raise RuntimeError(f"{stage} exited with code {event['exitCode']}")
    if stage == "bridge":
        return validate_bridge(log, exit_code=event["exitCode"], module=identities["stock"].module,
            nonce=event["nonce"], **identities)
    if stage.startswith("audited-"):
        side = stage.removeprefix("audited-")
        records = audit.parse_audits(log, expected_nonce=event["nonce"],
            expected=[replace(identities[side], label="standalone")])
        if side == "applied":
            audit.require_clear(records[0])
        return {"commandAudits": records}
    return {}


def certify_module(*, module: str, stock: InputFile, applied: InputFile, is_module: bool,
                   oracle: InputFile, auditor: InputFile, imports: ImportEnvironment,
                   dependencies: Mapping[str, Mapping[str | Path, str]],
                   work_parent: Path, timeout: float = 900) -> Certification:
    """Fresh cold compilation certificate, with no reuse or publication.

    ``timeout`` bounds each process. Source paths must end in the exact module
    path so ordinary Lean and explicit-module native tools read identical paths.
    Inputs must remain immutable. The supplied dependency graph and runtime
    manifest completeness belong to the caller, as with the legacy helper.
    """
    work = None
    try:
        relative = base._module_path(module)
        if type(is_module) is not bool or isinstance(timeout, bool) or not math.isfinite(timeout) or timeout <= 0:
            raise RuntimeError("invalid module mode or timeout")
        stock, applied, oracle, auditor = map(base._checked_file, (stock, applied, oracle, auditor))
        for item in (oracle, auditor):
            if not os.access(item.path, os.X_OK):
                raise RuntimeError("compiler tool is not executable")
        for item in (stock, applied):
            _source_root(item.path, module)
        paths, environment_identity = base._environment(imports)
        dep_hashes = base._dependencies(dependencies, paths, module)
        base._target_absent(paths, module)
        parent = base._path(work_parent, directory=True)
        if any(parent.is_relative_to(p) for p in paths):
            raise RuntimeError("work parent lies inside an import search root")
        work = Path(tempfile.mkdtemp(prefix="cold-certified-module-", dir=parent))
        base._outside(work, paths)
        outputs, quarantines = {}, {}
        for label in FAMILIES:
            q = work / label
            q.mkdir()
            quarantines[label] = q
            outputs[label] = q / relative
            outputs[label].parent.mkdir(parents=True, exist_ok=True)
        sources = {"stock": stock.path.read_bytes(), "applied": applied.path.read_bytes()}
        for side, item in (("stock", stock), ("applied", applied)):
            if hashlib.sha256(sources[side]).hexdigest() != item.sha256:
                raise RuntimeError("source changed while archiving")
            (work / f"{side}.lean").write_bytes(sources[side])
        identities = {side: audit.ExpectedAudit(module, item.path, sources[side], side, is_module)
                      for side, item in (("stock", stock), ("applied", applied))}
        implementation = {str(base._path(Path(m.__file__))): base.sha256(Path(m.__file__)) for m in
            (base, materializer, protocol, base.scope, audit, process_runner, base.translated_imports)}
        implementation[str(Path(__file__).resolve())] = base.sha256(Path(__file__).resolve())
        commands = _commands(module, stock.path, applied.path, oracle.path, auditor.path,
                             imports.lean_binary, outputs)
        events = []
        for stage in STAGES:
            nonce = protocol.fresh_run_nonce()
            env = imports.environment()
            env.update({protocol.RUN_NONCE_ENV: nonce, "LEAN_PATH": os.pathsep.join(str(p) for p in paths),
                        "LEAN_SYSROOT": environment_identity["leanSysroot"]})
            env.pop(audit.ENABLE_ENV, None)
            if stage == "bridge":
                env[audit.ENABLE_ENV] = "1"
            invocation = work / (stage + ".invocation.json")
            event = {"stage": stage, "command": commands[stage], "nonce": nonce, "module": module,
                     "environment": environment_identity, "auditEnableVariable": stage == "bridge"}
            base._publish_json(invocation, event)
            log = work / (stage + ".log")
            try:
                process = process_runner.run_process(commands[stage], cwd=ROOT, env=env, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, check=False)
            except subprocess.TimeoutExpired as error:
                partial = error.output or b""
                log.write_text(partial.decode("utf-8", errors="replace") if isinstance(partial, bytes) else partial)
                raise RuntimeError(f"{stage} timed out") from error
            log.write_text(process.stdout, encoding="utf-8")
            event.update(exitCode=process.returncode, log={"path": str(log), "sha256": base.sha256(log)},
                         invocation={"path": str(invocation), "sha256": base.sha256(invocation)})
            event["observation"] = _observe(process.stdout, event, identities)
            events.append(event)
            base._publish_json(work / (stage + ".result.json"), event)
        families = {label: base._artifact_family(quarantines[label], outputs[label], is_module) for label in FAMILIES}
        comparisons = _same_source_families(families, outputs, is_module)
        receipt = {"kind": KIND, "schema": SCHEMA, "status": "certified_in_quarantine",
            "nativeContract": "serialized_bridge_v2",
            "module": module, "isModule": is_module, "createdAt": datetime.now(timezone.utc).isoformat(),
            "stock": {"path": str(stock.path), "sha256": stock.sha256, "archivePath": str(work / "stock.lean")},
            "applied": {"path": str(applied.path), "sha256": applied.sha256, "archivePath": str(work / "applied.lean")},
            "oracleExecutable": {"path": str(oracle.path), "sha256": oracle.sha256},
            "auditorExecutable": {"path": str(auditor.path), "sha256": auditor.sha256},
            "implementationHashes": implementation, "importEnvironment": environment_identity,
            "dependencyArtifactFamilies": dep_hashes, "dependencyScope": "caller_supplied_families",
            "stages": events, "artifactFamilies": families, "sameSourceComparisons": comparisons,
            "outputArtifactFamily": families["ordinary-applied"], "quarantine": str(quarantines["ordinary-applied"]),
            "promoted": False, "acceptedCampaignCoverage": False, "sourceCommentProvenanceAccepted": False,
            "scope": "serialized compiler semantics under caller-supplied immutable dependencies/runtime"}
        _verify_record(receipt, work)
        if base._environment(imports) != (paths, environment_identity):
            raise RuntimeError("import environment changed during cold certification")
        if base._dependencies(dependencies, paths, module) != dep_hashes:
            raise RuntimeError("dependency families changed during cold certification")
        base._target_absent(paths, module)
        evidence = [p for p in work.rglob("*") if p.is_file()]
        base._sync_evidence(work, evidence)
        receipt_path = work / "receipt.json"
        base._publish_json(receipt_path, receipt)
        return Certification(receipt_path, base.sha256(receipt_path), receipt)
    except Exception as error:
        detail = str(error)
        if work is not None and work.is_dir():
            try:
                base._publish_json(work / "failure.json", {"kind": KIND + "_failure", "schema": SCHEMA,
                    "module": module, "error": detail, "acceptedCampaignCoverage": False, "promoted": False})
            except Exception as evidence_error:
                detail += f"; could not archive failure: {evidence_error}"
        raise CertificationError(detail, work) from error


def _verify_record(r: dict, work: Path, *, require_target_absent: bool = True) -> None:
    """Recheck bytes, framing and families without rerunning a compiler."""
    if r.get("kind") != KIND or type(r.get("schema")) is not int or r["schema"] != SCHEMA or \
            r.get("status") != "certified_in_quarantine" or r.get("promoted") is not False or type(r.get("isModule")) is not bool:
        raise RuntimeError("invalid cold certification identity")
    if r.get("nativeContract") != "serialized_bridge_v2":
        raise RuntimeError("cold certification lacks serialized metadata comparison")
    if any(r.get(field) is not False for field in ("acceptedCampaignCoverage", "sourceCommentProvenanceAccepted")) or \
            r.get("dependencyScope") != "caller_supplied_families":
        raise RuntimeError("cold certification exceeds its validation scope")
    module = r["module"]; is_module = r["isModule"]
    relative = base._module_path(module)
    work = base._path(work, directory=True)
    paths = tuple(base._path(Path(p), directory=True) for p in r["importEnvironment"]["searchPath"])
    if not paths:
        raise RuntimeError("empty certified import search path")
    identity = r["importEnvironment"]
    # Reconstruct only fields that the legacy strict checker actually verifies;
    # do not imply acceptance of a caller's source-tree or external-runtime hash.
    imports = ImportEnvironment(source_root=_source_root(Path(r["stock"]["path"]), module),
        translated_olean_root=paths[0], lean_binary=Path(identity["leanBinary"]["path"]),
        lean_sysroot=Path(identity["leanSysroot"]), search_path=paths, excluded_roots=(),
        unavailable_roots=(), source_hash="", search_path_hash="")
    if base._environment(imports) != (paths, identity):
        raise RuntimeError("certified strict import environment changed")
    if require_target_absent:
        base._target_absent(paths, module)
    base._outside(work, paths)
    identities = {}
    for side in ("stock", "applied"):
        item = r[side]
        if item["archivePath"] != str(work / f"{side}.lean"):
            raise RuntimeError("source archive identity mismatch")
        for key in ("path", "archivePath"):
            base._checked_file(InputFile(Path(item[key]), item["sha256"]))
        _source_root(Path(item["path"]), module)
        identities[side] = audit.ExpectedAudit(module, Path(item["path"]), Path(item["archivePath"]).read_bytes(), side, is_module)
    for item in (r["oracleExecutable"], r["auditorExecutable"], r["importEnvironment"]["leanBinary"]):
        base._checked_file(InputFile(Path(item["path"]), item["sha256"]))
    for group in (r["implementationHashes"], *r["dependencyArtifactFamilies"].values()):
        for path, digest in group.items():
            base._checked_file(InputFile(Path(path), digest))
    if base._dependencies(r["dependencyArtifactFamilies"], paths, module) != r["dependencyArtifactFamilies"]:
        raise RuntimeError("dependency family resolution changed")
    if [e["stage"] for e in r["stages"]] != list(STAGES):
        raise RuntimeError("cold certification stage inventory changed")
    outputs = {label: work / label / relative for label in FAMILIES}
    commands = _commands(module, Path(r["stock"]["path"]), Path(r["applied"]["path"]),
        Path(r["oracleExecutable"]["path"]), Path(r["auditorExecutable"]["path"]),
        Path(identity["leanBinary"]["path"]), outputs)
    nonces = set()
    for event in r["stages"]:
        stage = event["stage"]
        if event["module"] != module or event["command"] != commands[stage] or \
                event["environment"] != identity or event["auditEnableVariable"] is not (stage == "bridge"):
            raise RuntimeError("stage command/environment identity mismatch")
        if type(event["exitCode"]) is not int:
            raise RuntimeError("stage exit code is not an integer")
        if event["nonce"] in nonces:
            raise RuntimeError("compiler nonce reused")
        nonces.add(event["nonce"])
        for field, suffix in (("log", ".log"), ("invocation", ".invocation.json")):
            item = event[field]
            if item["path"] != str(work / (stage + suffix)):
                raise RuntimeError("stage evidence identity mismatch")
            base._checked_file(InputFile(Path(item["path"]), item["sha256"]))
        invocation = json.loads(Path(event["invocation"]["path"]).read_text())
        if invocation != {k: event[k] for k in ("stage", "command", "nonce", "module", "environment", "auditEnableVariable")}:
            raise RuntimeError("stage invocation changed")
        observation = _observe(Path(event["log"]["path"]).read_text(), event, identities)
        if observation != event["observation"]:
            raise RuntimeError("stage observation changed")
        result = work / (stage + ".result.json")
        base._path(result)
        if json.loads(result.read_text()) != event:
            raise RuntimeError("stage result changed")
    if set(r["artifactFamilies"]) != set(FAMILIES):
        raise RuntimeError("cold family inventory changed")
    for label, family in r["artifactFamilies"].items():
        if base._artifact_family(work / label, outputs[label], is_module) != family:
            raise RuntimeError("cold family changed")
    if _same_source_families(r["artifactFamilies"], outputs, is_module) != r["sameSourceComparisons"]:
        raise RuntimeError("cold comparison changed")
    if r["outputArtifactFamily"] != r["artifactFamilies"]["ordinary-applied"] or r["quarantine"] != str(work / "ordinary-applied"):
        raise RuntimeError("publication candidate is not the ordinary applied output")


def verify_certification(certification: Certification, *, require_target_absent: bool = True) -> dict:
    """Revalidate a cold receipt and all its evidence before a caller publishes.

    Only a caller auditing its own completed publication may disable the absent
    target check; all other byte, dependency and import-root checks still run.
    """
    base._checked_file(InputFile(certification.receipt_path, certification.receipt_sha256))
    record = json.loads(certification.receipt_path.read_text())
    if record != certification.receipt:
        raise RuntimeError("cold certification receipt changed")
    if type(require_target_absent) is not bool:
        raise RuntimeError("invalid publication target policy")
    _verify_record(record, certification.receipt_path.parent, require_target_absent=require_target_absent)
    return record
