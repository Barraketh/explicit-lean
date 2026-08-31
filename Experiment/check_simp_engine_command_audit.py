#!/usr/bin/env python3
"""Validate actual-frontend command audits; no campaign acceptance is implied.

Library callers use parse_audits to obtain separate remaining-call counts, then
require_clear for a final absence check. The CLI checks an existing immutable
log; --self-test exercises the already-built native tools without building any
package or changing the toolchain/search path.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

import boundary_protocol as protocol
import check_simp_engine_boundary_scope as scope
from process_runner import run_process

ROOT = Path(__file__).resolve().parents[1]
MARKER = "SIMP_ENGINE_COMMAND_AUDIT "
KIND = "simp_engine_command_audit"
SCHEMA = 1
ENABLE_ENV = "SIMP_ENGINE_COMMAND_AUDIT"
FIELDS = {"kind", "schema", "label", "module", "isModule", "sourcePath", "source",
          "callbackCount", "commandCount", "rawCount", "occurrences", "declarations"}
OCCURRENCE_FIELDS = {"module", "startByte", "endByte", "line", "column", "kind", "source",
                     "ancestors", "commandKind", "commandStartByte", "commandEndByte"}
DECLARATION_FIELDS = {"module", "name", "startByte", "endByte", "isProof"}


@dataclass(frozen=True)
class ExpectedAudit:
    module: str
    source_path: Path
    source: bytes
    label: str = "standalone"
    is_module: bool | None = None


def _natural(value: object, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise RuntimeError(f"command audit {label} must be a natural number")
    return value


def _span(value: dict, source: bytes, label: str) -> tuple[int, int]:
    start = _natural(value["startByte"], label + ".startByte")
    end = _natural(value["endByte"], label + ".endByte")
    if not start <= end <= len(source):
        raise RuntimeError(f"command audit {label} has an invalid source span")
    try:
        source[:start].decode("utf-8")
        source[start:end].decode("utf-8")
    except UnicodeDecodeError as error:
        raise RuntimeError(f"command audit {label} span splits UTF-8") from error
    return start, end


def _classify(record: object, expected: ExpectedAudit) -> dict:
    if not isinstance(record, dict) or set(record) != FIELDS:
        raise RuntimeError("command audit has invalid record fields")
    if record["kind"] != KIND or type(record["schema"]) is not int or record["schema"] != SCHEMA:
        raise RuntimeError("command audit has invalid kind/schema")
    if (record["module"], record["label"], record["sourcePath"]) != (
        expected.module, expected.label, str(expected.source_path)
    ) or expected.label not in {"standalone", "stock", "applied"}:
        raise RuntimeError("command audit source/module/label identity mismatch")
    if not isinstance(record["isModule"], bool) or (
        expected.is_module is not None and record["isModule"] != expected.is_module
    ):
        raise RuntimeError("command audit module mode mismatch")
    if not isinstance(record["source"], str) or record["source"].encode("utf-8") != expected.source:
        raise RuntimeError("command audit exact source identity mismatch")
    if _natural(record["callbackCount"], "callbackCount") != 1:
        raise RuntimeError("command audit requires exactly one callback")
    _natural(record["commandCount"], "commandCount")
    if not isinstance(record["occurrences"], list) or not isinstance(record["declarations"], list):
        raise RuntimeError("command audit occurrence/declaration arrays are invalid")
    if _natural(record["rawCount"], "rawCount") != len(record["occurrences"]):
        raise RuntimeError("command audit raw occurrence count mismatch")
    for declaration in record["declarations"]:
        if not isinstance(declaration, dict) or set(declaration) != DECLARATION_FIELDS:
            raise RuntimeError("command audit declaration fields are invalid")
        if declaration["module"] != expected.module or not isinstance(declaration["name"], str) or \
                not declaration["name"] or not isinstance(declaration["isProof"], bool):
            raise RuntimeError("command audit declaration identity/type is invalid")
        _span(declaration, expected.source, "declaration")
    unique: dict[tuple, dict] = {}
    for occurrence in record["occurrences"]:
        if not isinstance(occurrence, dict) or set(occurrence) != OCCURRENCE_FIELDS:
            raise RuntimeError("command audit occurrence fields are invalid")
        start, end = _span(occurrence, expected.source, "occurrence")
        if start == end or occurrence["module"] != expected.module or \
                occurrence["kind"] not in {"simp", "simp_only"} or \
                occurrence["source"] != expected.source[start:end].decode("utf-8"):
            raise RuntimeError("command audit occurrence source identity is invalid")
        prefix = expected.source[:start].decode("utf-8")
        if _natural(occurrence["line"], "line") != prefix.count("\n") + 1 or \
                _natural(occurrence["column"], "column") != len(prefix.rsplit("\n", 1)[-1]):
            raise RuntimeError("command audit occurrence position mismatch")
        if not isinstance(occurrence["ancestors"], list) or not all(
            isinstance(kind, str) and kind for kind in occurrence["ancestors"]
        ):
            raise RuntimeError("command audit occurrence ancestry is invalid")
        command_fields = [occurrence[key] for key in
                          ("commandKind", "commandStartByte", "commandEndByte")]
        if command_fields != [None, None, None]:
            if not isinstance(command_fields[0], str) or not command_fields[0]:
                raise RuntimeError("command audit command kind is invalid")
            command_start = _natural(command_fields[1], "commandStartByte")
            command_end = _natural(command_fields[2], "commandEndByte")
            if not command_start <= start <= end <= command_end <= len(expected.source):
                raise RuntimeError("command audit command span does not contain occurrence")
        classified = scope.classify(occurrence, record["declarations"])
        scope.validate_scope_dimensions(classified["executionRole"], classified["declarationKind"],
                                        classified["action"])
        key = (start, end, occurrence["kind"], occurrence["source"])
        if key in unique:
            old = unique[key]
            if any(old[field] != classified[field] for field in
                   ("executionRole", "declarationKind", "action")):
                raise RuntimeError("command audit shared source paths disagree on classification")
        else:
            unique[key] = classified
    classified = list(unique.values())
    counts = Counter("unresolved" if row["action"] == "unresolved" else row["executionRole"]
                     for row in classified)
    return {"module": expected.module, "label": expected.label,
            "sourcePath": str(expected.source_path),
            "sourceSha256": hashlib.sha256(expected.source).hexdigest(),
            "rawOccurrencePathCount": record["rawCount"], "uniqueOccurrenceCount": len(classified),
            "directExecutableCount": counts["direct_executable"],
            "reusableExecutableCount": counts["reusable_executable"],
            "unresolvedCount": counts["unresolved"],
            "retainedSyntaxDataCount": counts["retained_syntax_data"],
            "classified": classified}


def parse_audits(output: str, *, expected_nonce: str,
                 expected: list[ExpectedAudit]) -> list[dict]:
    """Reject missing, duplicate, foreign, or malformed records, including errors.

    Expected source bytes must be the caller's immutable compiler input, not bytes
    inferred from the emitted record. Record order is part of the protocol.
    """
    if not expected or len({(e.label, e.module, str(e.source_path)) for e in expected}) != len(expected):
        raise RuntimeError("command audit expectations are empty or duplicated")
    protocol.check_replay_abort_markers(output, expected_nonce=expected_nonce)
    records = protocol.parse_framed_json_lines(output, marker=MARKER,
        expected_nonce=expected_nonce, label="command audit")
    if len(records) != len(expected):
        raise RuntimeError("command audit missing or duplicate record")
    return [_classify(record, identity) for record, identity in zip(records, expected)]


def require_clear(audit: dict) -> None:
    """No unresolved source call is exempt from the final absence check."""
    for field in ("unresolvedCount", "directExecutableCount", "reusableExecutableCount"):
        if _natural(audit.get(field), field):
            raise RuntimeError(f"command audit has remaining calls: {field}={audit[field]}")


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def self_test() -> Path:
    binary = ROOT / ".lake/build/bin/simpEngineCommandAudit"
    oracle = ROOT / ".lake/build/bin/simpEngineDeclarationOracle"
    if not binary.is_file() or not oracle.is_file():
        raise RuntimeError("build simpEngineCommandAudit and simpEngineDeclarationOracle first")
    work = Path(tempfile.mkdtemp(prefix="command-audit-", dir=ROOT / ".lake"))
    print(work, flush=True)
    paths = [Path(__file__).resolve(), binary, oracle, ROOT / "lakefile.toml", ROOT / "lean-toolchain",
             ROOT / "ExplicitLean/SimpEngine/CommandAudit.lean",
             ROOT / "Experiment/SimpEngineCommandAudit.lean",
             ROOT / "Experiment/SimpEngineDeclarationOracle.lean",
             ROOT / "Experiment/boundary_protocol.py",
             ROOT / "Experiment/check_simp_engine_boundary_scope.py"]
    inputs = {str(path): _sha(path) for path in paths}
    (work / "inputs-before.json").write_text(json.dumps(inputs, indent=2) + "\n")
    archive = work / "inputs"; archive.mkdir()
    for i, path in enumerate(paths):
        (archive / f"{i:03d}-{path.name}").write_bytes(path.read_bytes())
    events = []

    def run(name, command, *, enabled=False, nonce=True):
        env, token = protocol.recording_subprocess_environment()
        if not nonce:
            env.pop(protocol.RUN_NONCE_ENV, None)
        if enabled:
            env[ENABLE_ENV] = "1"
        else:
            env.pop(ENABLE_ENV, None)
        result = run_process(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=180, check=False)
        log = work / f"{name}.log"; log.write_text(result.stdout)
        events.append({"name": name, "command": command, "nonce": token if nonce else None,
                       "exitCode": result.returncode, "log": str(log), "logSha256": _sha(log)})
        return result, token

    fixtures = [
        ("Baseline", False, "import Lean\n", "theorem sample : True := by simp\n", (1, 0, 0, 0)),
        ("ModuleBaseline", True, "import Lean\n", "theorem sample : True := by simp\n", (1, 0, 0, 0)),
        ("LocalWrap", False, "import Lean\n", 'syntax "my_tactic " tactic : tactic\nmacro_rules\n  | `(tactic| my_tactic $t:tactic) => `(tactic| $t)\ntheorem sample : True := by my_tactic simp\n', (1, 0, 0, 0)),
        ("Reusable", False, "import Lean\n", 'macro "quoted_tactic" : tactic => `(tactic| simp)\ntheorem sample : True := by simp\ntheorem called : True := by quoted_tactic\n', (1, 1, 0, 0)),
        ("InertData", False, "import Lean\n", '#check `(tactic| simp)\ntheorem sample : True := by simp\n', (1, 0, 0, 1)),
        ("ActualHeader", True, "import Lean\nimport Mathlib.Tactic.SimpRw\n", 'theorem rw_import (n : Nat) : n = n + 0 := by simp_rw [Nat.add_zero]\ntheorem sample : True := by simp\n', (1, 0, 0, 0)),
        ("Empty", False, "import Lean\n", "", (0, 0, 0, 0)),
        ("UnknownQuote", False, "import Lean\n", 'def retained : Lean.MacroM (Lean.TSyntax `tactic) := `(tactic| simp)\n', (0, 0, 1, 0)),
        ("PartialOutput", False, "import Lean\n", '#eval IO.print "partial-output"\ntheorem sample : True := by simp\n', (1, 0, 0, 0)),
    ]
    good = None
    options = ["-DautoImplicit=false", "-DmaxSynthPendingDepth=3",
               "-Dweak.linter.unusedVariables=false", "-Dweak.linter.unusedSimpArgs=false",
               "-Dweak.linter.unreachableTactic=false", "-DmaxHeartbeats=0"]
    for name, module_mode, header, body, expected_counts in fixtures:
        module = "CommandAuditFixture." + name
        check = f'''run_cmd
  unless (← Lean.getEnv).mainModule == `{module} do throwError "module identity changed"
  unless (← Lean.getEnv).header.isModule == {str(module_mode).lower()} do throwError "module mode changed"
  unless Lean.Elab.async.get (← Lean.getOptions) do throwError "async changed"
  unless Lean.internal.cmdlineSnapshots.get (← Lean.getOptions) do throwError "snapshots changed"
'''
        path = work / "source" / "CommandAuditFixture" / f"{name}.lean"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(("module\n" if module_mode else "") + header + check + body)
        original = path.read_bytes()
        ordinary, _ = run(name + "-ordinary", ["lake", "env", "lean", *options,
                        "-R", str(work / "source"), str(path)])
        assert ordinary.returncode == 0, ordinary.stdout
        result, nonce = run(name, ["lake", "env", str(binary), module, str(path)])
        assert result.returncode == 0, result.stdout
        identity = ExpectedAudit(module, path, original, is_module=module_mode)
        audit = parse_audits(result.stdout, expected_nonce=nonce, expected=[identity])[0]
        assert tuple(audit[field] for field in ("directExecutableCount", "reusableExecutableCount",
                     "unresolvedCount", "retainedSyntaxDataCount")) == expected_counts, audit
        if name == "Empty":
            require_clear(audit)
        else:
            try: require_clear(audit)
            except RuntimeError: pass
            else: raise AssertionError("remaining call accepted as clear")
        assert path.read_bytes() == original
        if good is None: good = (result.stdout, nonce, identity)
        print(name, expected_counts, flush=True)

    for name, source in [
        ("LateError", "import Lean\ntheorem prefix : True := by simp\nnot a command\n"),
        ("ProofError", "import Lean\ntheorem bad : False := by simp\n"),
        ("MissingImport", "import NoSuchCommandAuditDependency\n"),
    ]:
        path = work / f"{name}.lean"; path.write_text(source)
        result, _ = run(name, ["lake", "env", str(binary), "CommandAuditFixture." + name, str(path)])
        assert result.returncode != 0 and not any(line.startswith(MARKER) for line in result.stdout.splitlines()), result.stdout

    output, nonce, identity = good
    payload = protocol.parse_framed_json_lines(output, marker=MARKER,
        expected_nonce=nonce, label="test")[0]
    framed = protocol.marker_prefix(MARKER, nonce) + json.dumps(payload) + "\n"
    mutations = {"wrong-nonce": framed.replace(nonce, "wrong", 1), "duplicate": framed + framed,
                 "missing": "", "unframed": MARKER + json.dumps(payload)}
    for field, value in [("schema", 2), ("module", "Wrong"), ("source", ""),
                         ("sourcePath", "wrong.lean"), ("callbackCount", 0), ("rawCount", True)]:
        changed = dict(payload); changed[field] = value
        mutations[field] = protocol.marker_prefix(MARKER, nonce) + json.dumps(changed)
    for name, mutated in mutations.items():
        try: parse_audits(mutated, expected_nonce=nonce, expected=[identity])
        except RuntimeError: pass
        else: raise AssertionError(f"wire mutation accepted: {name}")

    _lifecycle_test(work, run)
    for name, body, accepted in [("Same", "def value : Nat := 1\n", True),
                                 ("Changed", "def value : Nat := 2\n", False),
                                 ("ProofError", "theorem bad : False := by simp\n", False)]:
        stock = work / f"{name}-stock.lean"; stock.write_text("import Lean\ndef value : Nat := 1\n")
        applied = work / f"{name}-applied.lean"; applied.write_text("import Lean\n" + body)
        command = ["lake", "env", str(oracle), "CommandAuditOracle", str(stock), str(applied)]
        plain, _ = run(name + "-oracle-plain", command)
        observed, token = run(name + "-oracle-audit", command, enabled=True)
        prefix = "SIMP_ENGINE_DECLARATION_ORACLE "
        extract = lambda text: [json.loads(line[len(prefix):]) for line in text.splitlines() if line.startswith(prefix)]
        assert extract(plain.stdout) == extract(observed.stdout)
        assert (plain.returncode == observed.returncode == 0) == accepted
        assert not any(line.startswith(MARKER) for line in plain.stdout.splitlines())
        expected_audits = [ExpectedAudit("CommandAuditOracle", stock, stock.read_bytes(), "stock")]
        if name != "ProofError":
            expected_audits.append(ExpectedAudit("CommandAuditOracle", applied, applied.read_bytes(), "applied"))
        audits = parse_audits(observed.stdout, expected_nonce=token, expected=expected_audits)
        for audit in audits: require_clear(audit)
    missing, _ = run("missing-nonce", ["lake", "env", str(binary), identity.module,
                    str(identity.source_path)], nonce=False)
    assert missing.returncode != 0 and MARKER not in missing.stdout
    assert inputs == {path: _sha(Path(path)) for path in inputs}, "compiler inputs changed during tests"
    (work / "inputs-after.json").write_text(json.dumps(inputs, indent=2) + "\n")
    report = {"status": "passed", "acceptedCampaignCoverage": False, "inputs": inputs,
              "events": events, "wireMutationCount": len(mutations),
              "hashes": {str(p): _sha(p) for p in work.rglob("*") if p.is_file()}}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return work / "report.json"


def _lifecycle_test(work: Path, run) -> None:
    path = work / "Lifecycle.lean"
    path.write_text(r'''import ExplicitLean.SimpEngine.CommandAudit
open Lean ExplicitLean.SimpEngine.CommandAudit
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let before ← Elab.Command.moduleLintersRef.get
  let good := "import Lean\nrun_cmd Lean.Elab.Command.addModuleLinter { name := `CommandAuditImportedLinter, run := fun _ => pure () }\ntheorem sample : True := by simp\n"
  for _ in [:2] do
    let captured ← capture good {} "command-audit-lifecycle.lean" `CommandAuditLifecycle
    unless captured.environment.contains `sample do throw <| IO.userError "wrong returned environment"
  let current ← Elab.Command.moduleLintersRef.get
  unless current.size == before.size + 2 &&
      (current.filter (·.name == `CommandAuditImportedLinter)).size == 2 do
    throw <| IO.userError "collector removed an imported linter or leaked"
  for source in #["import Lean\ntheorem bad : False := by simp\n",
      "import NoSuchCommandAuditDependency\n",
      "import Lean\nrun_cmd Lean.Elab.Command.moduleLintersRef.modify fun ls => ls.filter fun l => !(`_explicitLeanCommandAuditCollector).isPrefixOf l.name\n",
      "import Lean\nrun_cmd do\n  let ls ← Lean.Elab.Command.moduleLintersRef.get\n  let some l := ls.find? fun l => (`_explicitLeanCommandAuditCollector).isPrefixOf l.name | throwError \"collector absent\"\n  Lean.Elab.Command.addModuleLinter l\n"] do
    let mut rejected := false
    try
      discard <| capture source {} "command-audit-lifecycle.lean" `CommandAuditLifecycle
    catch _ => rejected := true
    unless rejected do throw <| IO.userError "failed/absent/duplicate callback accepted"
    let after ← Elab.Command.moduleLintersRef.get
    unless (after.map (·.name)) == (current.map (·.name)) do
      throw <| IO.userError "collector cleanup failed"
  let source := "import Lean\ntheorem recovered : True := by simp\n"
  let recovered ← capture source {}
    "command-audit-lifecycle.lean" `CommandAuditLifecycle
  unless ((← Elab.Command.moduleLintersRef.get).map (·.name)) == (current.map (·.name)) do
    throw <| IO.userError "repeated capture leaked"
  IO.print "partial-without-newline"
  emit recovered "standalone" (← runNonce)
  IO.println "COMMAND_AUDIT_LIFECYCLE_OK"
''')
    result, nonce = run("lifecycle", ["lake", "env", "lean", "--run", str(path)])
    assert result.returncode == 0 and "COMMAND_AUDIT_LIFECYCLE_OK" in result.stdout, result.stdout
    parse_audits(result.stdout, expected_nonce=nonce, expected=[ExpectedAudit(
        "CommandAuditLifecycle", Path("command-audit-lifecycle.lean"),
        b"import Lean\ntheorem recovered : True := by simp\n")])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--module")
    parser.add_argument("--source", type=Path)
    parser.add_argument("--log", type=Path)
    parser.add_argument("--nonce")
    parser.add_argument("--label", choices=["standalone", "stock", "applied"], default="standalone")
    args = parser.parse_args()
    if args.self_test:
        print(self_test())
        return
    if not all([args.module, args.source, args.log, args.nonce]):
        parser.error("provide --module, --source, --log, --nonce (or --self-test)")
    # Match the filename spelling supplied to the compiler as well as its bytes.
    path = args.source
    audit = parse_audits(args.log.read_text(), expected_nonce=args.nonce,
        expected=[ExpectedAudit(args.module, path, path.read_bytes(), args.label)])[0]
    require_clear(audit)
    print(json.dumps(audit, indent=2))


if __name__ == "__main__":
    main()
