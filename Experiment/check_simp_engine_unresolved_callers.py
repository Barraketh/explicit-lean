#!/usr/bin/env python3
"""Exercise the four unresolved quoted simp calls through stock callers.

Each probe is a disposable copy of the defining Mathlib source. The selected
source heads use the existing scope marker. Lift and Nontriviality are invoked
by importing callers; DeriveEncodable uses an appended in-module fixture so
its generated private names remain accessible. This is execution evidence,
not a transformation, semantic-equivalence check, or coverage claim.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone

import check_simp_engine_boundary_scope as scope
import simp_engine_inventory as inventory
from process_runner import run_process


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake" / "week-2026-08-31" / "unresolved-callers"
CORPUS = ROOT / ".lake" / "week-2026-08-31" / "corpus-unresolved.json"
NONTRIVIALITY_ID = "35beee1afee45baf"
EXECUTION_MARKER = "UNRESOLVED_CALLER_EXECUTION "
NONTRIVIALITY_CONSUMER = "        let ([], _) ← runTactic g₁' stx | failure\n"
NONTRIVIALITY_QUOTE = (
    "        let stx := open TSyntax.Compat in Unhygienic.run `(tactic| simp [$simpArgs,*])\n"
)

CASES: tuple[tuple[str, str, str, str], ...] = (
    (
        "Mathlib.Tactic.DeriveEncodable",
        "Mathlib/Tactic/DeriveEncodable.lean",
        "8a18ca2cc5877278",
        """

-- Close the defining module's still-open `public section` for this fixture.
end

namespace Mathlib.Deriving.Encodable

public inductive unresolvedDeriveCaller where
  | zero
  | one

syntax (name := unresolved_derive_caller) "unresolved_derive_caller" : command

elab_rules : command
  | `(command| unresolved_derive_caller) => do
    let _ ← mkEncodableInstance #[`Mathlib.Deriving.Encodable.unresolvedDeriveCaller]
    pure ()

unresolved_derive_caller

end Mathlib.Deriving.Encodable
""",
    ),
    (
        "Mathlib.Tactic.Lift",
        "Mathlib/Tactic/Lift.lean",
        "d9b60e8150d86521",
        """

inductive unresolvedLiftOld where
  | zero
  | one

inductive unresolvedLiftNew where
  | zero
  | one

def unresolvedLiftCoe : unresolvedLiftNew → unresolvedLiftOld
  | .zero => .zero
  | .one => .one

instance unresolvedLiftCanLift :
    CanLift unresolvedLiftOld unresolvedLiftNew unresolvedLiftCoe (fun _ => True) where
  prf x _ := match x with
    | .zero => ⟨.zero, rfl⟩
    | .one => ⟨.one, rfl⟩

def unresolvedLiftP (x : unresolvedLiftOld) : Prop := x = .zero

theorem unresolvedLiftCaller (e : unresolvedLiftOld) (hcond : True)
    (h : unresolvedLiftP e) : e = e := by
  lift e to unresolvedLiftNew using hcond with e' he'
""",
    ),
    (
        "Mathlib.Tactic.Lift",
        "Mathlib/Tactic/Lift.lean",
        "6c2a52e93b5afdd3",
        "",
    ),
    (
        "Mathlib.Tactic.Nontriviality.Core",
        "Mathlib/Tactic/Nontriviality/Core.lean",
        "35beee1afee45baf",
        """

inductive unresolvedNontrivialityType where
  | sole

elab "unresolved_nontriviality_envelope " body:tactic : tactic => do
  let some caller ← Lean.Elab.Term.getDeclName?
    | throwError "nontriviality envelope has no caller"
  IO.println ("UNRESOLVED_CALLER_ENVELOPE " ++
    (Lean.toJson #["begin", caller.toString]).compress)
  Lean.Elab.Tactic.evalTactic body
  IO.println ("UNRESOLVED_CALLER_ENVELOPE " ++
    (Lean.toJson #["end", caller.toString]).compress)

theorem unresolvedNontrivialityCaller (h : True) : True := by
  unresolved_nontriviality_envelope (nontriviality unresolvedNontrivialityType using h)
  trivial

run_cmd do
  let declaration ← Lean.getConstInfo ``unresolvedNontrivialityCaller
  let isProof ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.isProp declaration.type
  unless isProof do throwError "enclosing caller is not proof-valued"
  IO.println ("UNRESOLVED_CALLER_DECLARATION " ++
    (Lean.toJson declaration.name.toString).compress)
""",
    ),
)


def load_entries() -> dict[str, dict[str, object]]:
    records = json.loads(CORPUS.read_text(encoding="utf-8"))
    by_id = {str(record["id"]): record for record in records}
    if len(by_id) != len(records):
        raise RuntimeError("unresolved corpus contains duplicate IDs")
    entries: dict[str, dict[str, object]] = {}
    for module, _relative, occurrence_id, _fixture in CASES:
        entry = by_id.get(occurrence_id)
        if entry is None:
            raise RuntimeError(f"unresolved corpus is missing {occurrence_id}")
        if entry.get("module") != _relative:
            raise RuntimeError(
                f"occurrence {occurrence_id} has unexpected module {entry.get('module')!r}"
            )
        if inventory.occurrence_id(_relative, int(entry["startByte"]), int(entry["endByte"])) != occurrence_id:
            raise RuntimeError(f"occurrence ID no longer matches its source range: {occurrence_id}")
        entries[occurrence_id] = entry
    return entries


def artifact(path: Path) -> dict[str, str]:
    return {"path": str(path.resolve()), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def enclosing_caller_evidence(output: str, observed: dict[str, object]) -> dict[str, object]:
    """Keep runTactic's missing direct caller distinct from its enclosing proof.

    Immediate diagnostics bracket the unchanged runTactic call in its fresh
    context. Their ordered nesting inside the fixture's caller envelope links
    the sole marked execution to that caller without replacing its raw null.
    """
    envelopes = [json.loads(line.removeprefix("UNRESOLVED_CALLER_ENVELOPE "))
                 for line in output.splitlines() if line.startswith("UNRESOLVED_CALLER_ENVELOPE ")]
    declarations = [json.loads(line.removeprefix("UNRESOLVED_CALLER_DECLARATION "))
                    for line in output.splitlines() if line.startswith("UNRESOLVED_CALLER_DECLARATION ")]
    events: list[dict[str, object]] = []
    for line_number, line in enumerate(output.splitlines(), 1):
        for kind, prefix in (("enclosing", "UNRESOLVED_CALLER_ENVELOPE "),
                             ("execution", EXECUTION_MARKER),
                             ("declaration", "UNRESOLVED_CALLER_DECLARATION ")):
            if line.startswith(prefix):
                events.append({"logLine": line_number, "kind": kind,
                               "value": json.loads(line.removeprefix(prefix))})
    scope_lines = [n for n, line in enumerate(output.splitlines(), 1)
                   if line.startswith(scope.EXECUTION_MARKER)]
    if (len(declarations) != 1 or not isinstance(declarations[0], str)
            or not declarations[0].endswith(".unresolvedNontrivialityCaller")
            or envelopes != [["begin", declarations[0]], ["end", declarations[0]]]
            or observed["status"] != "incomplete_execution_evidence"
            or observed["executionCount"] != 1
            or observed["callers"] != [{"caller": None, "executionCount": 1,
                                        "isProofDeclaration": None}]):
        raise RuntimeError("nontriviality enclosing-caller evidence did not match the bounded fixture")
    expected_events = [
        ("enclosing", ["begin", declarations[0]]),
        ("execution", ["begin", NONTRIVIALITY_ID]),
        ("execution", ["end", NONTRIVIALITY_ID]),
        ("enclosing", ["end", declarations[0]]),
        ("declaration", declarations[0]),
    ]
    if ([(event["kind"], event["value"]) for event in events] != expected_events
            or len(scope_lines) != 1 or scope_lines[0] <= events[-1]["logLine"]):
        raise RuntimeError("nontriviality execution diagnostics were not nested inside the caller envelope")
    return {
        "status": "complete_enclosing_proof_declaration",
        "caller": declarations[0],
        "isProofDeclaration": True,
        "association": "immediate_runTactic_execution_bracket_nested_in_enclosing_caller",
        "orderedEvents": events,
        "rawScopeReportLogLine": scope_lines[0],
        "directScopeCaller": None,
        "limitation": "Lean.Elab.runTactic resets Term.Context; this is independent enclosing provenance, not direct caller evidence",
    }


def nontriviality_diagnostics(
    source: bytes, entries: list[dict[str, object]],
) -> tuple[list[tuple[int, int, bytes, str]], dict[str, object]]:
    """Add IO-only observations around one exactly matched stock consumer."""
    block = (NONTRIVIALITY_QUOTE + NONTRIVIALITY_CONSUMER).encode("utf-8")
    if source.count(block) != 1 or len(entries) != 1 or entries[0]["id"] != NONTRIVIALITY_ID:
        raise RuntimeError("pinned Nontriviality quotation/consumer statement changed")
    block_start = source.index(block)
    if int(entries[0]["startByte"]) != block_start + block.index(b"simp [$simpArgs,*]"):
        raise RuntimeError("Nontriviality consumer does not follow the selected source occurrence")
    start = block_start + len(NONTRIVIALITY_QUOTE.encode("utf-8"))
    end = start + len(NONTRIVIALITY_CONSUMER.encode("utf-8"))
    insertions = []
    for label, position in (("begin", start), ("end", end)):
        event = EXECUTION_MARKER + json.dumps([label, NONTRIVIALITY_ID], separators=(",", ":"))
        diagnostic = f"        IO.println {json.dumps(event)}\n".encode("utf-8")
        insertions.append((position, position, diagnostic, f"runTactic diagnostic {label}"))
    return insertions, {
        "kind": "immediate_runTactic_execution_diagnostics",
        "occurrenceId": NONTRIVIALITY_ID,
        "guardedOriginalBlock": block.decode("utf-8"),
        "consumerStartByte": start,
        "consumerEndByte": end,
        "originalConsumerStatement": NONTRIVIALITY_CONSUMER,
        "consumerStatementPreservedVerbatim": True,
        "freshDefaultTermContextPreserved": True,
        "insertions": [{"sourceByte": position, "text": text.decode("utf-8")}
                       for position, _, text, _ in insertions],
    }


def run_logged(
    command: list[str], log_path: Path, *, env: dict[str, str] | None = None,
    timeout: int = 600,
) -> tuple[int, str, dict[str, object]]:
    started = time.monotonic()
    try:
        completed = run_process(
            command,
            cwd=ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        code = 124
        output += "\nexplicit-lean: compilation timed out\n"
    else:
        code, output = completed.returncode, completed.stdout
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(output, encoding="utf-8")
    record = {
        "command": command,
        "cwd": str(ROOT),
        "leanPath": env.get("LEAN_PATH") if env is not None else None,
        "returnCode": code,
        "seconds": round(time.monotonic() - started, 3),
        "log": artifact(log_path),
    }
    log_path.with_suffix(".command.json").write_text(json.dumps(record, indent=2) + "\n")
    return code, output, record


class LeanRuntime:
    def __init__(self, output: Path):
        self.output = output
        self.compiled = output / "compiled"
        code, path, _ = run_logged(
            ["lake", "env", "printenv", "LEAN_PATH"], output / "lake-lean-path.log"
        )
        if code or not path.strip():
            raise RuntimeError("failed to obtain Lake's dependency search path")
        self.stock_path = path.strip()
        mathlib_root = next(
            (Path(item) for item in self.stock_path.split(os.pathsep)
             if (Path(item) / "Mathlib").is_dir()), None
        )
        if mathlib_root != ROOT / ".lake/packages/mathlib/.lake/build/lib/lean":
            raise RuntimeError(f"unexpected stock Mathlib search root: {mathlib_root}")
        protected = {
            CORPUS, Path(__file__), Path(scope.__file__), Path(inventory.__file__),
            Path(run_process.__code__.co_filename), ROOT / "lean-toolchain",
            ROOT / "ExplicitLean/SimpEngine/Boundary/ScopeProbe.lean",
        }
        protected.update((ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary").glob("ScopeProbe.*"))
        for _, relative, _, _ in CASES:
            protected.add(ROOT / ".lake/packages/mathlib" / relative)
            stock = mathlib_root / Path(relative).with_suffix(".olean")
            protected.update(stock.parent.glob(stock.stem + ".*"))
        self.protected = [artifact(path) for path in sorted(protected) if path.is_file()]
        # Lean chooses the first *package* root, not the first existing module
        # file. Populate a stock symlink overlay, opening real directories only
        # on the paths whose module outputs this probe will replace.
        self.compiled.mkdir(parents=True)
        parents = {Path(relative).parent for _, relative, _, _ in CASES}

        def overlay_directory(relative: Path) -> None:
            target = self.compiled / relative
            target.mkdir()
            for child in (mathlib_root / relative).iterdir():
                child_relative = relative / child.name
                if child.is_dir() and any(
                    parent == child_relative or child_relative in parent.parents
                    for parent in parents
                ):
                    overlay_directory(child_relative)
                else:
                    (target / child.name).symlink_to(child)

        overlay_directory(Path("Mathlib"))
        for child in mathlib_root.glob("Mathlib.*"):
            if child.is_file():
                (self.compiled / child.name).symlink_to(child)
        code, executable, _ = run_logged(
            ["lake", "env", "which", "lean"], output / "lake-lean-executable.log"
        )
        self.lean = Path(executable.strip()).resolve()
        if code or not self.lean.is_file():
            raise RuntimeError("failed to locate the pinned Lean executable")
        self.env = os.environ.copy()
        # Do not run `lake env lean` here: Lake prepends package paths, which
        # would allow the stock defining module to shadow the instrumented one.
        self.env["LEAN_PATH"] = os.pathsep.join((str(self.compiled), self.stock_path))

    def command(self, source: Path, root: Path, olean: Path | None = None) -> list[str]:
        original = inventory.lean_command(source)
        if original[:3] != ["lake", "env", "lean"] or original[-1] != str(source):
            raise RuntimeError("inventory Lean command contract changed")
        arguments = original[3:-1]
        if "-R" in arguments:
            index = arguments.index("-R")
            del arguments[index:index + 2]
        command = [str(self.lean), *arguments, "-R", str(root)]
        if olean is not None:
            command.extend(["-o", str(olean)])
        return [*command, str(source)]

    def run(self, source: Path, root: Path, log: str, olean: Path | None = None):
        return run_logged(
            self.command(source, root, olean), self.output / log, env=self.env
        )

    def check_unchanged_inputs(self) -> None:
        for expected in self.protected:
            if artifact(Path(expected["path"])) != expected:
                raise RuntimeError(f"protected input changed during caller probes: {expected['path']}")


def compile_source(
    runtime: LeanRuntime,
    module: str,
    relative: str,
    entries: list[dict[str, object]],
    suffix: bytes = b"",
) -> tuple[Path, str, dict[str, object], dict[str, object], str]:
    source_path = ROOT / ".lake" / "packages" / "mathlib" / relative
    source = source_path.read_bytes()
    for entry in entries:
        if source[int(entry["startByte"]) : int(entry["endByte"])] != entry["source"].encode():
            raise RuntimeError(f"stale source range for {entry['id']}")
    diagnostic_edits, diagnostic_record = (nontriviality_diagnostics(source, entries)
        if module == "Mathlib.Tactic.Nontriviality.Core" else ([], None))
    instrumented = scope._apply_scope_edits(
        source,
        [*scope._simp_probe_edits(source, entries), *diagnostic_edits],
    )
    # The source's private import is sufficient for its own declarations, but
    # generated commands emitted by the appended in-module caller need the
    # class to be visible at the public declaration boundary.
    if module == "Mathlib.Tactic.DeriveEncodable":
        instrumented = instrumented.replace(
            b"module\n",
            b"module\n\npublic import Mathlib.Logic.Encodable.Basic\n",
            1,
        )
    instrumented = scope._inject_scope_probe_header(instrumented)
    sentinel = "unresolvedCallerProbe" + module.replace(".", "_")
    instrumented += f"\npublic meta def {sentinel} : String := {json.dumps(module)}\n".encode()
    instrumented += suffix
    source_relative = Path(relative)
    destination = runtime.output / "instrumented" / source_relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(instrumented)

    olean = runtime.compiled / source_relative.with_suffix(".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    for previous in olean.parent.glob(olean.stem + ".*"):
        if not previous.is_symlink():
            raise RuntimeError(f"refusing to overwrite existing probe output: {previous}")
        previous.unlink()
    code, output, command = runtime.run(
        destination, runtime.output / "instrumented", f"{module}-source.log", olean
    )
    if code != 0:
        raise RuntimeError(f"instrumented source compile failed for {relative}:\n{output}")
    artifacts = {
        "source": artifact(source_path),
        "instrumentedSource": artifact(destination),
        "compiledSource": artifact(olean),
        "compiledSidecars": [artifact(path) for path in sorted(olean.parent.glob(olean.stem + ".*"))
                             if path != olean],
    }
    if diagnostic_record is not None:
        diagnostic_path = runtime.output / f"{module}-diagnostic-edits.json"
        diagnostic_path.write_text(json.dumps(diagnostic_record, indent=2) + "\n")
        artifacts["extraDiagnosticEdits"] = artifact(diagnostic_path)
    return olean, output, command, artifacts, sentinel


def run_group(
    runtime: LeanRuntime,
    module: str,
    relative: str,
    cases: list[tuple[str, str]],
    entries: dict[str, dict[str, object]],
) -> list[dict[str, object]]:
    fixture = next(fixture for _occurrence_id, fixture in cases if fixture)
    selected_entries = [entries[occurrence_id] for occurrence_id, _ in cases]
    inline = module == "Mathlib.Tactic.DeriveEncodable"
    suffix = fixture.encode("utf-8") + b"\nsimp_engine_boundary_scope_report\n" if inline else b""
    olean, source_output, source_command, artifacts, sentinel = compile_source(
        runtime, module, relative, selected_entries, suffix
    )
    caller_stem = Path(relative).stem
    caller_module = f"UnresolvedCallers.{caller_stem}"
    imports = f"import {module}\nimport ExplicitLean.SimpEngine.Boundary.ScopeProbe"
    if module == "Mathlib.Tactic.Nontriviality.Core":
        imports += "\npublic meta import Lean.Elab.Tactic.Basic"
    import_check = f'''
run_cmd do
  unless {sentinel} == {json.dumps(module)} do
    throwError "wrong instrumented module sentinel"
  let actual ← Lean.findOLean `{module}
  unless actual.toString == {json.dumps(str(olean))} do
    throwError "wrong instrumented module path"
  Lean.logInfo "UNRESOLVED_CALLER_IMPORT_VERIFIED"
'''
    caller = (f"module\n\n{imports}\nset_option Elab.async false\n{import_check}\n"
              + ("" if inline else fixture + "\nsimp_engine_boundary_scope_report\n"))
    caller_root = runtime.output / "callers"
    caller_path = caller_root / "UnresolvedCallers" / f"{caller_stem}.lean"
    caller_path.parent.mkdir(parents=True, exist_ok=True)
    caller_path.write_text(caller, encoding="utf-8")
    code, output, caller_command = runtime.run(
        caller_path, caller_root, f"{module}-caller.log"
    )
    if code != 0:
        raise RuntimeError(f"stock caller failed for {relative}:\n{output}")
    if "UNRESOLVED_CALLER_IMPORT_VERIFIED" not in output:
        raise RuntimeError(f"caller did not verify imported probe for {relative}")
    stock_env = runtime.env.copy()
    stock_env["LEAN_PATH"] = runtime.stock_path
    negative_code, negative_output, negative_command = run_logged(
        runtime.command(caller_path, caller_root),
        runtime.output / f"{module}-stock-import-negative.log", env=stock_env,
    )
    if (negative_code == 0 or f"Unknown identifier `{sentinel}`" not in negative_output
            or scope._parse_execution_reports(negative_output)
            or any(line.startswith(EXECUTION_MARKER) for line in negative_output.splitlines())):
        raise RuntimeError(f"stock import negative control did not reject the probe sentinel for {module}")
    reports = scope._parse_execution_reports(source_output if inline else output)
    ids = {occurrence_id for occurrence_id, _ in cases}
    execution_module = module if inline else caller_module
    evidence = scope._execution_evidence(ids, reports, execution_module)
    result: list[dict[str, object]] = []
    for occurrence_id, _fixture in cases:
        observed = evidence[occurrence_id]
        enclosing = (enclosing_caller_evidence(output, observed)
                     if module == "Mathlib.Tactic.Nontriviality.Core" else None)
        if enclosing is None and observed["status"] != "complete_proof_declaration":
            raise RuntimeError(f"caller probe was incomplete for {occurrence_id}: {observed}")
        result.append(
            {
                "occurrenceId": occurrence_id,
                "sourceModule": relative,
                "sourceDeclarations": entries[occurrence_id]["declarations"],
                "sourceRange": {key: entries[occurrence_id][key]
                                for key in ("startByte", "endByte", "source")},
                "executionModule": execution_module,
                "fixtureMode": "appended_in_module" if inline else "imported_caller",
                "fixtureOnlyExtraImports": (["Mathlib.Logic.Encodable.Basic"] if inline else
                    ["Lean.Elab.Tactic.Basic"] if enclosing is not None else []),
                "artifacts": {**artifacts, "caller": artifact(caller_path)},
                "sourceCompile": source_command,
                "callerCompile": caller_command,
                "stockImportNegativeControl": negative_command,
                "importVerified": True,
                "enclosingCallerEvidence": enclosing,
                "evidence": observed,
            }
        )
    return result


def verify_evidence(path: Path) -> dict[str, object]:
    """Verify saved artifact hashes without invoking Lean or rebuilding anything."""
    report = json.loads(path.read_text(encoding="utf-8"))
    if report.get("kind") != "simp_engine_unresolved_caller_evidence":
        raise RuntimeError("unexpected caller evidence kind")
    checked: set[str] = set()

    def walk(value: object) -> None:
        if isinstance(value, dict):
            if set(value) == {"path", "sha256"}:
                if artifact(Path(value["path"])) != value:
                    raise RuntimeError(f"evidence artifact hash/path mismatch: {value['path']}")
                checked.add(value["path"])
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)

    walk(report)
    results = report["results"]
    if (len(results) != len(CASES)
            or {row["occurrenceId"] for row in results} != {case[2] for case in CASES}):
        raise RuntimeError("evidence source occurrence set changed")
    for row in results:
        if row["sourceCompile"]["returnCode"] or row["callerCompile"]["returnCode"]:
            raise RuntimeError("evidence contains a failing positive compile")
        if row["stockImportNegativeControl"]["returnCode"] == 0:
            raise RuntimeError("evidence contains a passing negative control")
        for record in [row["artifacts"]["compiledSource"], *row["artifacts"]["compiledSidecars"]]:
            artifact_path = Path(record["path"])
            if artifact_path.is_symlink() or not artifact_path.is_relative_to(path.resolve().parent / "compiled"):
                raise RuntimeError(f"compiled evidence is not a local probe file: {artifact_path}")
        if row["occurrenceId"] == NONTRIVIALITY_ID:
            output = Path(row["callerCompile"]["log"]["path"]).read_text(encoding="utf-8")
            if enclosing_caller_evidence(output, row["evidence"]) != row["enclosingCallerEvidence"]:
                raise RuntimeError("saved enclosing provenance disagrees with the checked log")
    return {"allReferencedHashesVerified": True, "uniqueFilesChecked": len(checked),
            "sourceOccurrences": len(results), "enclosingExecutionOrderVerified": True}


def main() -> None:
    entries = load_entries()
    groups: dict[tuple[str, str], list[tuple[str, str]]] = {}
    for module, relative, occurrence_id, fixture in CASES:
        groups.setdefault((module, relative), []).append((occurrence_id, fixture))
    OUT.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix=datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ-"), dir=OUT))
    runtime = LeanRuntime(output)
    results: list[dict[str, object]] = []
    for (module, relative), cases in groups.items():
        results.extend(run_group(runtime, module, relative, cases, entries))
        print(f"observed {module}: {len(cases)} source occurrence(s)", flush=True)
    runtime.check_unchanged_inputs()
    report = {
        "schema": 1,
        "kind": "simp_engine_unresolved_caller_evidence",
        "claims": {"positiveCallerExecutionOnly": True, "translatedCoverage": False,
                   "semanticEquivalenceChecked": False, "corpusReclassified": False},
        "unresolvedNotProbed": ["87ef8f8d4afcf255"],
        "dependencyMode": "stock_olean_overlay_with_instrumented_defining_modules",
        "protectedInputsUnchanged": runtime.protected,
        "corpus": artifact(CORPUS),
        "driver": artifact(Path(__file__)),
        "scopeProbe": artifact(ROOT / "ExplicitLean/SimpEngine/Boundary/ScopeProbe.lean"),
        "scopeProbeOlean": artifact(ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine/Boundary/ScopeProbe.olean"),
        "pinnedLean": artifact(runtime.lean),
        "leanToolchain": artifact(ROOT / "lean-toolchain"),
        "results": results,
    }
    report_path = output / "caller-evidence.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"caller evidence: {report_path}")


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--verify":
        print(json.dumps(verify_evidence(Path(sys.argv[2])), indent=2))
    elif len(sys.argv) == 1:
        main()
    else:
        raise SystemExit("usage: check_simp_engine_unresolved_callers.py [--verify caller-evidence.json]")
