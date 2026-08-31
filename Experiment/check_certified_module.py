#!/usr/bin/env python3
"""Portable certification checks using already-built tools; never builds packages."""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from unittest.mock import patch

import boundary_protocol as protocol
import certified_module as certified
import check_simp_engine_command_audit as audit
from process_runner import run_process
from translated_imports import build_import_environment

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--oracle", type=Path, default=ROOT / ".lake/build/bin/simpEngineDeclarationOracle")
    parser.add_argument("--work-parent", type=Path, default=ROOT / ".lake")
    args = parser.parse_args()
    binary = args.oracle.resolve(strict=True)
    work = Path(tempfile.mkdtemp(prefix="certified-module-check-", dir=args.work_parent.resolve(strict=True)))
    sources, translated, runs = (work / name for name in ("sources", "translated", "runs"))
    for path in (sources, translated, runs):
        path.mkdir()
    imports = build_import_environment(sources, translated)
    dependency = "Mathlib.CertifiedDependency"
    dep_source = sources / "Mathlib/CertifiedDependency.lean"
    dep_source.parent.mkdir()
    dep_source.write_text("module\npublic import Std\npublic def dependencyMarker : Nat := 7\n")
    dep_output = translated / "Mathlib/CertifiedDependency.olean"
    dep_output.parent.mkdir()
    dep_nonce = protocol.fresh_run_nonce()
    dep_env = imports.environment(); dep_env[protocol.RUN_NONCE_ENV] = dep_nonce
    dep_command = [str(imports.lean_binary), "-R", str(sources), "-o", str(dep_output), str(dep_source)]
    built = run_process(dep_command, cwd=ROOT, env=dep_env, text=True, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, timeout=180, check=False)
    dep_log = work / "dependency.log"; dep_log.write_text(built.stdout)
    if built.returncode:
        raise RuntimeError(built.stdout)
    family = {str(dep_output.with_suffix(s)): certified.sha256(dep_output.with_suffix(s)) for s in certified.SUFFIXES}
    dependencies = {dependency: family}
    initial = {str(binary): certified.sha256(binary), str(Path(certified.__file__)): certified.sha256(Path(certified.__file__)),
               str(Path(__file__).resolve()): certified.sha256(Path(__file__).resolve()), **family}
    events = [{"case": "local-dependency-build", "command": dep_command, "nonce": dep_nonce,
               "exitCode": built.returncode, "log": str(dep_log), "logSha256": certified.sha256(dep_log)}]
    checks, successes = [], []
    header = "module\nimport Lean\nimport Mathlib.CertifiedDependency\npublic section\n"
    body = "@[expose] def oracleResult : Nat := 7\nprivate def secret : Nat := 3\ntheorem sample : (1 : Nat) = 1 := by rfl\n"
    simple = header + body
    fixtures = [
        ("Module", simple, simple, True, None),
        ("Legacy", simple.replace("module\n", "").replace("public section\n", ""), simple.replace("module\n", "").replace("public section\n", ""), True, None),
        ("Replacement", simple.replace("by rfl", "by simp"), simple, True, None),
        ("PartialOutput", header + '#eval IO.print "partial"\n' + body, header + '#eval IO.print "partial"\n' + body, True, None),
        ("ChangedData", simple, simple.replace(":= 7", ":= 8"), False, "exited with code"),
        ("FrontendError", simple, simple + "example : False := True.intro\n", False, "exited with code"),
        ("Remaining", simple.replace("by rfl", "by simp"), simple.replace("by rfl", "by simp"), False, "directExecutableCount"),
        ("Reusable", header + 'macro "quoted_tactic" : tactic => `(tactic| simp)\n', header + 'macro "quoted_tactic" : tactic => `(tactic| simp)\n', False, "reusableExecutableCount"),
        ("Unresolved", header + 'def retained : Lean.MacroM (Lean.TSyntax `tactic) := `(tactic| simp)\n', header + 'def retained : Lean.MacroM (Lean.TSyntax `tactic) := `(tactic| simp)\n', False, "unresolvedCount"),
        ("PostponedIR", simple.replace("public section", "set_option compiler.postponeCompile true\npublic section"), simple.replace("public section", "set_option compiler.postponeCompile true\npublic section"), False, "artifact family"),
        ("MissingImportEnvironment", "import Lean\n", "import Lean\nrun_cmd do\n  let env ← Lean.getEnv\n  Lean.setEnv <| Lean.Environment.ofKernelEnv env.toKernelEnv\n", False, "exited with code"),
    ]

    def call(name: str, stock_text: str = simple, applied_text: str = simple,
             *, expected: bool = True, detail: str | None = None, mutate=None,
             override: dict | None = None):
        folder = sources / name; folder.mkdir()
        stock, applied = folder / "stock.lean", folder / "applied.lean"
        stock.write_text(stock_text); applied.write_text(applied_text)
        params = dict(module="Certified." + name, stock=certified.InputFile(stock, certified.sha256(stock)),
                      applied=certified.InputFile(applied, certified.sha256(applied)),
                      is_module=stock_text.startswith("module\n"), oracle=certified.InputFile(binary, initial[str(binary)]),
                      imports=imports, dependencies=dependencies, work_parent=runs, timeout=180)
        if override:
            params.update(override)
        original_run = run_process

        def run(*a, **kw):
            if mutate in {"missing-nonce", "missing-audit"}:
                kw["env"] = dict(kw["env"])
                kw["env"].pop(protocol.RUN_NONCE_ENV if mutate == "missing-nonce" else audit.ENABLE_ENV)
            if mutate == "timeout":
                raise subprocess.TimeoutExpired(a[0], 0.01, output=b"partial timeout output\n")
            result = original_run(*a, **kw)
            if callable(mutate):
                mutate(params, a[0], result)
            return result

        result = None
        try:
            with patch.object(certified.process_runner, "run_process", side_effect=run):
                result = certified.certify_module(**params)
        except certified.CertificationError as error:
            if expected or (detail is not None and detail not in str(error)):
                raise RuntimeError(f"{name}: unexpected failure: {error}") from error
            if error.work_directory:
                if (error.work_directory / "receipt.json").exists():
                    raise RuntimeError("failed certification wrote a receipt")
                failure = json.loads((error.work_directory / "failure.json").read_text())
                assert failure["acceptedCampaignCoverage"] is False
                invocation = error.work_directory / "invocation.json"
                if invocation.exists():
                    event = json.loads(invocation.read_text()); event.update(case=name, expectedFailure=True)
                    log = error.work_directory / "oracle.log"
                    if log.exists():
                        event.update(log=str(log), logSha256=certified.sha256(log))
                    events.append(event)
            checks.append({"case": name, "status": "rejected", "detail": str(error)})
        else:
            if not expected:
                raise RuntimeError(f"{name}: accepted a negative control")
            assert result.receipt_sha256 == certified.sha256(result.receipt_path)
            receipt = json.loads(result.receipt_path.read_text())
            assert receipt == result.receipt and receipt["promoted"] is False
            assert not receipt["acceptedCampaignCoverage"] and not receipt["sourceCommentProvenanceAccepted"]
            assert receipt["dependencyScope"] == "caller_supplied_families"
            assert not (translated / certified._module_path(params["module"])).exists()
            successes.append(result)
            events.append({"case": name, "receipt": str(result.receipt_path), "receiptSha256": result.receipt_sha256,
                           "nonce": receipt["nonce"], "command": receipt["command"], "exitCode": 0,
                           "log": receipt["log"]["path"], "logSha256": receipt["log"]["sha256"]})
            checks.append({"case": name, "status": "certified_in_quarantine"})
        print(json.dumps(checks[-1]), flush=True)
        return result

    for name, stock, applied, expected, detail in fixtures:
        call(name, stock, applied, expected=expected, detail=detail)

    # Read emitted module and legacy families in separate downstream processes.
    # This temporary read-only search path does not publish or move the files.
    for success in successes[:2]:
        receipt = success.receipt
        consumer = work / (receipt["module"].replace(".", "-") + "-consumer.lean")
        consumer.write_text(f'import {receipt["module"]}\n#eval oracleResult + dependencyMarker\n')
        env = imports.environment()
        env["LEAN_PATH"] = os.pathsep.join([receipt["quarantine"], *(str(p) for p in imports.search_path)])
        nonce = protocol.fresh_run_nonce(); env[protocol.RUN_NONCE_ENV] = nonce
        command = [str(imports.lean_binary), str(consumer)]
        observed = run_process(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=180, check=False)
        log = consumer.with_suffix(".log"); log.write_text(observed.stdout)
        assert observed.returncode == 0 and observed.stdout.strip() == "14", observed.stdout
        events.append({"case": "read-" + receipt["module"], "command": command, "nonce": nonce,
                       "exitCode": observed.returncode, "log": str(log), "logSha256": certified.sha256(log)})
        checks.append({"case": "read-" + receipt["module"], "status": "computed_14"})

    call("MissingNonce", expected=False, detail="exited with code", mutate="missing-nonce")
    call("MissingAudit", expected=False, detail="exited with code", mutate="missing-audit")
    call("Timeout", expected=False, detail="timed out", mutate="timeout")
    call("WrongHeader", expected=False, detail="module mode mismatch", override={"is_module": False})

    def change_source(params, command, result):
        params["applied"].path.write_bytes(params["applied"].path.read_bytes() + b"\n-- changed\n")
    call("SourceMutation", expected=False, detail="input hash mismatch", mutate=change_source)
    dep_ir = dep_output.with_suffix(".ir"); saved = dep_ir.read_bytes()
    try:
        call("DependencyMutation", expected=False, detail="input hash mismatch",
             mutate=lambda *args: dep_ir.write_bytes(saved + b"changed"))
    finally:
        dep_ir.write_bytes(saved)
    tool_copy = work / "oracle-copy"; shutil.copyfile(binary, tool_copy); tool_copy.chmod(0o700)
    def change_tool(*args):
        with tool_copy.open("ab") as stream:
            stream.write(b"changed")
    call("ToolMutation", expected=False, detail="input hash mismatch",
         override={"oracle": certified.InputFile(tool_copy, certified.sha256(tool_copy))},
         mutate=change_tool)

    # Fail before starting a subprocess when caller inputs or output locations are invalid.
    call("BadSourceHash", expected=False, detail="input hash mismatch",
         override={"stock": certified.InputFile(dep_source, "0" * 64)})
    call("IncompleteDependency", expected=False, detail="incomplete dependency",
         override={"dependencies": {dependency: dict(list(family.items())[:3])}})
    call("InsideSearchPath", expected=False, detail="inside an import search root",
         override={"work_parent": translated})
    old_output = translated / "Certified/Existing.olean"; old_output.parent.mkdir(exist_ok=True); old_output.write_bytes(b"old output")
    call("Existing", expected=False, detail="already present")
    link = work / "linked-runs"; link.symlink_to(runs, target_is_directory=True)
    call("SymlinkWork", expected=False, detail="symlink path", override={"work_parent": link})
    shadow = work / "shadow"; (shadow / "Mathlib").mkdir(parents=True)
    call("ShadowRoot", expected=False, detail="stock or shadow",
         override={"imports": replace(imports, search_path=imports.search_path + (shadow,))})

    # Mutate genuine observations; no copied evidence becomes a new certification.
    valid = successes[0].receipt
    text = Path(valid["log"]["path"]).read_text()
    identities = {label: audit.ExpectedAudit(valid["module"], Path(valid[label]["path"]),
                  Path(valid[label]["path"]).read_bytes(), label, True) for label in ("stock", "applied")}
    frames = [line for line in text.splitlines() if line.startswith(audit.MARKER)]
    oracle_line = next(line for line in text.splitlines() if line.startswith("SIMP_ENGINE_DECLARATION_ORACLE "))
    mutations = {
        "wrong-nonce": (text, "wrong", 0),
        "duplicate-audit": (text + frames[0] + "\n", valid["nonce"], 0),
        "missing-audit": (text.replace(frames[0], ""), valid["nonce"], 0),
        "duplicate-oracle": (text + oracle_line + "\n", valid["nonce"], 0),
        "missing-oracle": (text.replace(oracle_line, ""), valid["nonce"], 0),
        "nonzero-exit": (text, valid["nonce"], 1),
    }
    for field, value in (("schema", True), ("module", "Wrong"), ("checkedDeclarationCount", True)):
        report = json.loads(oracle_line.split(" ", 1)[1]); report[field] = value
        mutations["oracle-" + field] = (text.replace(oracle_line, "SIMP_ENGINE_DECLARATION_ORACLE " + json.dumps(report)), valid["nonce"], 0)
    for name, (changed, nonce, code) in mutations.items():
        try:
            certified.validate_observation(changed, exit_code=code, module=valid["module"], nonce=nonce, **identities)
        except RuntimeError:
            checks.append({"case": name, "status": "rejected"})
        else:
            raise RuntimeError(f"observation mutation accepted: {name}")

    for name in ("missing", "stale", "directory", "empty", "symlink"):
        q = work / ("family-" + name); shutil.copytree(Path(valid["quarantine"]), q)
        output = q / certified._module_path(valid["module"])
        if name == "missing": output.with_suffix(".ir").unlink()
        if name == "stale": (q / "stale.olean").write_bytes(b"stale")
        if name == "directory": (q / "unexpected-directory").mkdir()
        if name == "empty": output.write_bytes(b"")
        if name == "symlink":
            output.unlink(); output.symlink_to(next(iter(valid["outputArtifactFamily"])))
        try:
            certified._artifact_family(q, output, True)
        except RuntimeError:
            checks.append({"case": "family-" + name, "status": "rejected"})
        else:
            raise RuntimeError(f"artifact mutation accepted: {name}")
    exclusive = work / "existing-record.json"; exclusive.write_text("existing")
    try:
        certified._publish_json(exclusive, {"new": True})
    except FileExistsError:
        assert exclusive.read_text() == "existing"
        checks.append({"case": "exclusive-receipt", "status": "rejected"})
    else:
        raise RuntimeError("overwrote an existing receipt")
    for path, digest in initial.items():
        assert certified.sha256(Path(path)) == digest, path
    result = {"status": "passed", "acceptedCampaignCoverage": False, "promoted": False,
              "oracle": str(binary), "inputs": initial, "checks": checks, "events": events,
              "hashes": {str(p): certified.sha256(p) for p in work.rglob("*") if p.is_file() and not p.is_symlink()}}
    report = work / "report.json"; report.write_text(json.dumps(result, indent=2) + "\n")
    print(str(report), flush=True)


if __name__ == "__main__":
    main()
