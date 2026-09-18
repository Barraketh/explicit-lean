#!/usr/bin/env python3
"""Build the reviewed seven-module readable-Lean cone.

This driver deliberately has a small contract.  ``source-root`` is a complete
source tree (the generated target files and the pinned source files needed for
the header walk); ``run-dir`` is a fresh, private output directory.  Stock
Mathlib oleans are copied into the private translated root and are never left
on ``LEAN_PATH``.  Target and bridge oleans are then rebuilt in the reviewed
order with the pinned Lean binary.

The JSON report is an audit log, not a certificate.  It records paths,
versions, import kinds, resolutions and compiler output.  It intentionally
does not contain hashes, nonces or a mandatory declaration oracle.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Iterable, Sequence

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Experiment"))

from translated_imports import ImportEnvironment, build_import_environment, run_pinned_lean


TARGETS = (
    "Mathlib.Logic.Basic",
    "Mathlib.Logic.ExistsUnique",
    "Mathlib.Logic.Function.Defs",
    "Mathlib.Logic.Nontrivial.Defs",
    "Mathlib.Logic.Function.Basic",
    "Mathlib.Logic.IsEmpty.Basic",
    "Mathlib.Data.Option.Basic",
)
BRIDGE = "Mathlib.Logic.Relator"
BUILD_ORDER = (
    TARGETS[0],
    TARGETS[1],
    TARGETS[2],
    TARGETS[3],
    BRIDGE,
    TARGETS[4],
    TARGETS[5],
    TARGETS[6],
)
EXPECTED_MODULES = 69
EXPECTED_EDGES = 134
RUNNER_VERSION = "readable-cone-v1"


class ConeFailure(RuntimeError):
    """A fail-closed cone preflight, staging or build failure."""


@dataclass(frozen=True)
class ImportEdge:
    source: str
    kind: str
    module: str

    def as_json(self) -> dict[str, str]:
        return {"source": self.source, "kind": self.kind, "module": self.module}


@dataclass(frozen=True)
class Closure:
    modules: tuple[str, ...]
    edges: tuple[ImportEdge, ...]

    def as_json(self) -> dict[str, object]:
        return {
            "modules": list(self.modules),
            "edges": [edge.as_json() for edge in self.edges],
            "moduleCount": len(self.modules),
            "edgeCount": len(self.edges),
        }


def _mask_source(text: str) -> str:
    """Blank comments, strings and quoted attribute lists, preserving lines."""
    out = list(text)
    i = 0
    comment_depth = 0
    while i < len(text):
        if comment_depth:
            if text.startswith("/-", i):
                out[i:i + 2] = [" ", " "]
                comment_depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = [" ", " "]
                comment_depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            for j in range(i, end):
                out[j] = " "
            i = end
            continue
        if text.startswith("/-", i):
            out[i:i + 2] = [" ", " "]
            comment_depth = 1
            i += 2
            continue
        if text[i] == '"':
            out[i] = " "
            i += 1
            while i < len(text):
                if text[i] != "\n":
                    out[i] = " "
                if text[i] == "\\":
                    i += 1
                    if i < len(text) and text[i] != "\n":
                        out[i] = " "
                    i += 1
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            continue
        if text.startswith("@[", i):
            # Attribute spans may contain strings and nested brackets.  They
            # are not imports, but masking them avoids treating an example in
            # an attribute as a header command.
            j = i + 2
            depth = 1
            quoted = False
            while j < len(text) and depth:
                if quoted:
                    if text[j] == "\\":
                        j += 2
                        continue
                    if text[j] == '"':
                        quoted = False
                elif text[j] == '"':
                    quoted = True
                elif text[j] == "[":
                    depth += 1
                elif text[j] == "]":
                    depth -= 1
                if text[j] != "\n":
                    out[j] = " "
                j += 1
            out[i] = " "
            if i + 1 < len(text):
                out[i + 1] = " "
            i = j
            continue
        i += 1
    return "".join(out)


# Lean's header grammar permits the forms import, meta import, public import,
# public meta import, and their private-prefixed counterparts.  Keep the
# original spelling in the manifest; it is useful when diagnosing a closure.
IMPORT_RE = re.compile(
    r"(?m)^\s*((?:(?:public|private)\s+)?(?:meta\s+)?import)\s+([A-Za-z_][A-Za-z0-9_.]*)\b"
)


def module_relative(module: str, suffix: str = ".lean") -> Path:
    if not module.startswith("Mathlib."):
        raise ConeFailure(f"not a Mathlib module: {module}")
    parts = module.split(".")
    if any(part in {"", ".", ".."} for part in parts):
        raise ConeFailure(f"invalid module name: {module}")
    return Path(*parts).with_suffix(suffix)


def source_path(source_root: Path, module: str) -> Path:
    return source_root / module_relative(module)


def imports_in_source(source_root: Path, module: str) -> list[tuple[str, str]]:
    path = source_path(source_root, module)
    if not path.is_file():
        raise ConeFailure(f"missing source for {module}: {path}")
    masked = _mask_source(path.read_text(encoding="utf-8"))
    return [(kind, name) for kind, name in IMPORT_RE.findall(masked) if name.startswith("Mathlib.")]


def discover_closure(source_root: Path, roots: Sequence[str] = TARGETS) -> Closure:
    """Walk every Mathlib header import, retaining exact import forms."""
    todo = list(roots)
    seen: set[str] = set()
    by_source: dict[str, list[tuple[str, str]]] = {}
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        entries = imports_in_source(source_root, module)
        by_source[module] = entries
        todo.extend(name for _, name in entries if name not in seen)
    modules = tuple(sorted(seen))
    edges = tuple(
        sorted(
            (ImportEdge(source, kind, module) for source, entries in by_source.items() for kind, module in entries),
            key=lambda edge: (edge.source, edge.kind, edge.module),
        )
    )
    return Closure(modules, edges)


def verify_reviewed_closure(closure: Closure) -> None:
    if len(closure.modules) != EXPECTED_MODULES:
        raise ConeFailure(
            f"reviewed source closure requires {EXPECTED_MODULES} modules, found {len(closure.modules)}"
        )
    if len(closure.edges) != EXPECTED_EDGES:
        raise ConeFailure(
            f"reviewed source closure requires {EXPECTED_EDGES} edges, found {len(closure.edges)}"
        )
    for module in TARGETS:
        if module not in closure.modules:
            raise ConeFailure(f"target missing from closure: {module}")
    if BRIDGE not in closure.modules:
        raise ConeFailure(f"bridge missing from closure: {BRIDGE}")
    cross = sorted(
        (edge.source, edge.module)
        for edge in closure.edges
        if edge.source not in TARGETS and edge.module in TARGETS
    )
    expected = [(BRIDGE, "Mathlib.Logic.Function.Defs")]
    if cross != expected:
        raise ConeFailure(f"unexpected non-target-to-target edges: {cross}")


def verify_build_order(closure: Closure) -> None:
    positions = {module: index for index, module in enumerate(BUILD_ORDER)}
    if set(BUILD_ORDER) != set(TARGETS) | {BRIDGE}:
        raise ConeFailure("runner build order does not contain exactly the seven targets and bridge")
    for edge in closure.edges:
        if edge.source in positions and edge.module in positions:
            if positions[edge.module] >= positions[edge.source]:
                raise ConeFailure(
                    f"reviewed build order violates import edge {edge.source} -> {edge.module}"
                )


def _artifact_files(root: Path, module: str) -> list[Path]:
    rel = module_relative(module)
    base = root / rel.with_suffix("")
    # A module's emitted family is Module.olean, Module.olean.server,
    # Module.olean.private and Module.ir.  Do not copy source or unrelated
    # files from the stock package.
    candidates = [base.with_suffix(".olean"), base.with_suffix(".ir")]
    candidates.extend(base.parent.glob(base.name + ".olean.*"))
    return sorted(path for path in candidates if path.is_file() and not path.is_symlink())


def _output_family(output: Path) -> list[Path]:
    """Return every expected emitted artifact for one module output."""
    candidates = [output, output.with_suffix(".ir")]
    candidates.extend(output.parent.glob(output.name + ".*"))
    return sorted(set(candidates))


def _prepare_output_family(output: Path) -> dict[str, object]:
    """Remove only this module's old outputs, preserving all prerequisites."""
    before = _output_family(output)
    existing_before = [path for path in before if path.exists()]
    removed: list[str] = []
    for path in before:
        if path.is_dir() and not path.is_symlink():
            raise ConeFailure(f"unexpected directory in module output family: {path}")
        if path.is_symlink():
            raise ConeFailure(f"unexpected symlink in module output family: {path}")
        if path.exists():
            path.unlink()
            removed.append(str(path))
    return {
        "beforeFamily": [str(path) for path in existing_before],
        "removedFamily": removed,
    }


def _freshness(prepared: dict[str, object], output: Path) -> dict[str, object]:
    after = [path for path in _output_family(output) if path.is_file() and not path.is_symlink()]
    return {
        **prepared,
        "afterFamily": [str(path) for path in after],
        "freshOlean": output.is_file() and not output.is_symlink(),
    }


def stage_artifacts(stock_root: Path, translated_root: Path, modules: Iterable[str]) -> dict[str, object]:
    if not stock_root.is_dir() or stock_root.is_symlink():
        raise ConeFailure(f"invalid stock artifact root: {stock_root}")
    if translated_root.exists() and translated_root.is_symlink():
        raise ConeFailure(f"translated root must not be a symlink: {translated_root}")
    translated_root.mkdir(parents=True, exist_ok=True)
    staged: list[str] = []
    for module in modules:
        files = _artifact_files(stock_root, module)
        olean = stock_root / module_relative(module, ".olean")
        if not olean.is_file() or olean.is_symlink():
            raise ConeFailure(f"missing pinned stock artifact for {module}: {olean}")
        if olean not in files:
            files = [olean, *files]
        for source in files:
            relative = source.relative_to(stock_root)
            destination = translated_root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            if destination.exists() or destination.is_symlink():
                if destination.is_symlink():
                    raise ConeFailure(f"refusing symlink in translated root: {destination}")
                destination.unlink()
            shutil.copy2(source, destination)
            staged.append(str(destination))
    return {"stockRoot": str(stock_root), "translatedRoot": str(translated_root), "files": staged}


def _strip_resolution(value: dict[str, object]) -> dict[str, object]:
    return {
        key: item
        for key, item in value.items()
        if key not in {"translatedSha256", "resolvedSha256", "availableMatches"}
    }


def _git_version(path: Path) -> str:
    try:
        completed = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return "unavailable"
    return completed.stdout.strip() if completed.returncode == 0 else "unavailable"


def _lean_versions(imports: ImportEnvironment) -> dict[str, str]:
    result = imports.result()
    return {"version": str(result["leanVersion"]), "commit": str(result["leanCommit"]), "binary": str(result["leanBinary"])}


def _write_log(run_dir: Path, name: str, output: str) -> str:
    path = run_dir / "logs" / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(output, encoding="utf-8")
    return str(path)


def _find_stock_root(imports: ImportEnvironment, closure: Closure) -> Path:
    for root in imports.excluded_roots:
        if all((root / module_relative(module, ".olean")).is_file() for module in closure.modules):
            return root
    raise ConeFailure("no stock Mathlib artifact root contains the complete 69-module closure")


def _compile_module(imports: ImportEnvironment, run_dir: Path, module: str) -> dict[str, object]:
    source = source_path(imports.source_root, module)
    output = imports.translated_olean_root / module_relative(module, ".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    prepared = _prepare_output_family(output)
    result = run_pinned_lean(imports, ["-R", str(imports.source_root), "-o", str(output), str(source)])
    log = _write_log(run_dir, module.removeprefix("Mathlib.").replace(".", "_") + ".log", result.stdout)
    freshness = _freshness(prepared, output)
    entry: dict[str, object] = {
        "module": module,
        "source": str(source),
        "output": str(output),
        "family": freshness["afterFamily"],
        "freshness": freshness,
        "log": log,
        "returnCode": result.returncode,
    }
    if result.returncode != 0:
        entry.update({"status": "failed", "failure": f"pinned compile failed; see {log}"})
        return entry
    if not freshness["freshOlean"]:
        entry.update({"status": "failed", "failure": f"compiler did not produce a fresh translated olean: {output}"})
        return entry
    resolution = imports.resolve_mathlib([module], require_all=True)[module]
    if not resolution["resolvedFromTranslatedRoot"]:
        entry.update({"status": "failed", "failure": f"{module} did not resolve from translated root"})
        return entry
    entry.update({"status": "passed", "resolution": _strip_resolution(resolution)})
    return entry


def lint_targets(source_root: Path, baseline_source_root: Path | None = None) -> dict[str, object]:
    try:
        import simp_family_lint
    except ImportError as error:
        raise ConeFailure(f"cannot load simp-family lint: {error}") from error
    findings: list[dict[str, object]] = []
    baseline_findings = 0
    baseline_counts: dict[str, dict[str, int]] = {}
    if baseline_source_root is not None:
        if not baseline_source_root.is_dir() or baseline_source_root.is_symlink():
            raise ConeFailure(f"invalid baseline source root: {baseline_source_root}")
        for module in TARGETS:
            baseline_path = source_path(baseline_source_root, module)
            if not baseline_path.is_file() or baseline_path.is_symlink():
                raise ConeFailure(f"missing baseline target source for lint: {baseline_path}")
            counts = baseline_counts.setdefault(module, {})
            for finding in simp_family_lint.findings(baseline_path.read_text(encoding="utf-8")):
                counts[finding.token] = counts.get(finding.token, 0) + 1
                baseline_findings += 1
    for module in TARGETS:
        path = source_path(source_root, module)
        if not path.is_file():
            raise ConeFailure(f"missing generated target source for lint: {path}")
        counts = baseline_counts.get(module, {})
        for finding in simp_family_lint.findings(path.read_text(encoding="utf-8")):
            if counts.get(finding.token, 0):
                counts[finding.token] -= 1
                continue
            findings.append({"module": module, "line": finding.line, "description": finding.describe()})
    if findings:
        raise ConeFailure(f"generated target source retains executable simp-family calls ({len(findings)})")
    return {
        "status": "passed",
        "targetCount": len(TARGETS),
        "findings": 0,
        "baselineFindings": baseline_findings,
        "introducedFindings": 0,
    }


def run(args: argparse.Namespace) -> dict[str, object]:
    source_root = Path(args.source_root).expanduser().resolve()
    run_dir = Path(args.run_dir).expanduser().resolve()
    if not source_root.is_dir():
        raise ConeFailure(f"source root does not exist: {source_root}")
    run_dir.mkdir(parents=True, exist_ok=True)
    translated_root = run_dir / "translated-oleans"
    if translated_root.exists() and any(translated_root.iterdir()):
        raise ConeFailure(f"run directory is not fresh; translated root is non-empty: {translated_root}")
    manifest_path = Path(args.manifest).expanduser().resolve() if args.manifest else run_dir / "manifest.json"
    report: dict[str, object] = {
        "schema": 1,
        "status": "running",
        "runner": {"version": RUNNER_VERSION, "git": _git_version(ROOT)},
        "sourceRoot": str(source_root),
        "runDir": str(run_dir),
        "targets": list(TARGETS),
        "bridge": BRIDGE,
        "buildOrder": list(BUILD_ORDER),
        "modules": [],
        "lint": None,
        "versions": {
            "recorder": args.recorder_version or os.environ.get("RECORDER_VERSION", "unspecified"),
            "renderer": args.renderer_version or os.environ.get("RENDERER_VERSION", "unspecified"),
        },
    }
    try:
        closure = discover_closure(source_root)
        report["closure"] = closure.as_json()
        verify_reviewed_closure(closure)
        verify_build_order(closure)
        translated_root.mkdir(parents=True, exist_ok=True)
        # Constructing this environment also proves that all stock Mathlib
        # roots are excluded.  It is deliberately done before staging.
        imports = build_import_environment(source_root, translated_root)
        stock_root = Path(args.stock_olean_root).expanduser().resolve() if args.stock_olean_root else _find_stock_root(imports, closure)
        report["staging"] = stage_artifacts(stock_root, translated_root, closure.modules)
        imports = build_import_environment(source_root, translated_root)
        all_resolution = imports.resolve_mathlib(closure.modules, require_all=True)
        report["resolution"] = {module: _strip_resolution(value) for module, value in all_resolution.items()}
        report["toolchain"] = _lean_versions(imports)
        modules: list[dict[str, object]] = []
        for module in BUILD_ORDER:
            entry = _compile_module(imports, run_dir, module)
            entry["role"] = "bridge" if module == BRIDGE else "target"
            modules.append(entry)
            if entry["status"] != "passed":
                report["modules"] = modules
                raise ConeFailure(f"build failed for {module}: {entry.get('failure', 'unknown failure')}")
        report["modules"] = modules
        baseline_source_root = (
            Path(args.baseline_source_root).expanduser().resolve()
            if args.baseline_source_root else None
        )
        report["lint"] = lint_targets(source_root, baseline_source_root)
        report["status"] = "passed"
    except Exception as error:
        report["status"] = "failed"
        report["failure"] = {"type": type(error).__name__, "detail": str(error)}
        raise
    finally:
        manifest_path.parent.mkdir(parents=True, exist_ok=True)
        manifest_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", required=True, help="complete generated source root containing Mathlib/")
    parser.add_argument("--run-dir", required=True, help="fresh private run directory")
    parser.add_argument("--manifest", help="manifest path (default RUN/manifest.json)")
    parser.add_argument("--stock-olean-root", help="optional pinned stock root containing Mathlib/*.olean")
    parser.add_argument(
        "--baseline-source-root",
        help="optional pinned source root; unchanged out-of-scope simp-family calls are baseline",
    )
    parser.add_argument("--recorder-version")
    parser.add_argument("--renderer-version")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        report = run(args)
    except Exception as error:
        print(f"readable cone failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps({"status": report["status"], "manifest": str(Path(args.manifest or Path(args.run_dir) / "manifest.json").expanduser().resolve())}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
