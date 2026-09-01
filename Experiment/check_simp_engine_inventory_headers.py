#!/usr/bin/env python3
"""Remaining-call scans must parse the replay syntax imported by the source."""
from pathlib import Path
import hashlib
import json
import shutil
import sys
import tempfile

import simp_engine_inventory as inventory

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "Experiment/SimpEngineInventoryHeaderFixture.lean"
CALL = "simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.toList_push]"
PACKAGE_OPTIONS_MODULE = "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic"
PACKAGE_LAKEFILE = ROOT / ".lake/packages/mathlib/lakefile.lean"
PACKAGE_LAKEFILE_SHA256 = "e3e8ac4d3ea441b062dbd29a2910165e55d8463c8bd9a3feb830cf6fb64a1b7a"
PACKAGE_OPTIONS_SOURCE = (
    ROOT
    / ".lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean"
)
PACKAGE_OPTIONS_SOURCE_SHA256 = "a02c592f5d685b6f4c3b3738de223883cc70a1b96f5c2ef0625ce2694e4d38be"
PACKAGE_OPTIONS_OCCURRENCES = 32
PRELOADED_RULE_MODULE = "Mathlib.Tactic.ContinuousFunctionalCalculus"
PRELOADED_RULE_SOURCE = ROOT / ".lake/packages/mathlib/Mathlib/Tactic/ContinuousFunctionalCalculus.lean"
PRELOADED_RULE_SOURCE_SHA256 = "af8d1f2d010194667a10f172edbacb9113ac6496ac52bf796b124bfbabf96d66"
PRELOADED_RULE_DECLARATIONS = 7
PRELOADED_RULE_DECLARATION_NAMES = {
    "_aux_Mathlib_Tactic_ContinuousFunctionalCalculus___macroRules_cfcContTac_1",
    "_aux_Mathlib_Tactic_ContinuousFunctionalCalculus___macroRules_cfcTac_1",
    "_aux_Mathlib_Tactic_ContinuousFunctionalCalculus___macroRules_cfcZeroTac_1",
    "_private.Mathlib.Tactic.ContinuousFunctionalCalculus.0.initFn._@.Mathlib.Tactic.ContinuousFunctionalCalculus.2038506681._hygCtx._hyg.3",
    "cfcContTac",
    "cfcTac",
    "cfcZeroTac",
}
PACKAGE_OPTION_ARGUMENTS = [
    "-Dpp.unicode.fun=true",
    "-DautoImplicit=false",
    "-DmaxSynthPendingDepth=3",
    "-Dweak.linter.mathlibStandardSet=true",
    "-Dweak.linter.style.header=true",
    "-Dweak.linter.checkInitImports=true",
    "-Dweak.linter.allScriptsDocumented=true",
    "-Dweak.linter.pythonStyle=true",
    "-Dweak.linter.style.longFile=1500",
]
LOCAL_SYNTAX_SOURCE = """\
import Mathlib.Data.Nat.Basic

namespace LocalInventorySyntax
scoped syntax "localInventoryTerm" : term
scoped macro_rules | `(localInventoryTerm) => `(0)
end LocalInventorySyntax

open scoped LocalInventorySyntax

example : True := by
  have : Nat := localInventoryTerm
  simp
"""


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parent = ROOT / ".lake/inventory-header-controls"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="controls-", dir=parent))
    source = FIXTURE.read_text()
    assert source.count(CALL) == 1
    if sha(PACKAGE_OPTIONS_SOURCE) != PACKAGE_OPTIONS_SOURCE_SHA256:
        raise RuntimeError("package-options regression source changed")
    if sha(PACKAGE_LAKEFILE) != PACKAGE_LAKEFILE_SHA256:
        raise RuntimeError("pinned Mathlib package options changed")
    if sha(PRELOADED_RULE_SOURCE) != PRELOADED_RULE_SOURCE_SHA256:
        raise RuntimeError("preloaded-rule regression source changed")
    for consumer in [
        ROOT / "Experiment/SimpEngineInventory.lean",
        ROOT / "Experiment/SimpEngineBoundaryScope.lean",
    ]:
        consumer_source = consumer.read_text()
        if consumer_source.count("ExplicitLean.SimpEngine.mathlibIncrementalParserOptions") != 1:
            raise RuntimeError(f"{consumer.name} does not use the incremental parser options")
        if consumer_source.count("ExplicitLean.SimpEngine.mathlibParserOptions") != 1:
            raise RuntimeError(f"{consumer.name} does not use the full parser options")
        if "verificationFrontendOptions" in consumer_source:
            raise RuntimeError(f"{consumer.name} uses verification-only frontend options")
    inputs = [Path(__file__).resolve(), FIXTURE, ROOT / "lean-toolchain",
              PACKAGE_LAKEFILE,
              ROOT / "Experiment/SimpEngineInventory.lean",
              ROOT / "Experiment/simp_engine_inventory.py",
              ROOT / "Experiment/boundary_materialize_shard.py",
              ROOT / "ExplicitLean/SimpEngine/Inventory.lean",
              ROOT / "ExplicitLean/SimpEngine/Boundary/Tactic.lean",
              ROOT / "ExplicitLean/SimpEngine/FrontendOptions.lean",
              ROOT / "Experiment/SimpEngineBoundaryScope.lean",
              ROOT / ".lake/build/bin/simpEngineInventory",
              ROOT / ".lake/build/bin/simpEngineBoundaryScope",
              PACKAGE_OPTIONS_SOURCE,
              PRELOADED_RULE_SOURCE]
    before = {str(path): sha(path) for path in inputs}
    archived = []
    for index, path in enumerate(inputs):
        destination = work / "inputs" / f"{index}-{path.name}"
        destination.parent.mkdir(exist_ok=True)
        shutil.copy2(path, destination)
        archived.append({"path": str(path), "archivedPath": str(destination), "sha256": sha(path)})
    records = []
    # Aggregate parsing lacks the replay syntax imported by this source. It must
    # now detect that recovery, use the full parser, and retain the occurrence.
    for label, text, header, allow_errors, expected_source, expect_fallback in [
        ("aggregate-diagnostic", source, False, True, CALL, True),
        ("actual-header-one-call", source, True, False, CALL, False),
        ("actual-header-no-calls", source.replace(CALL, "skip"), True, False, None, False),
        ("actual-header-local-syntax", LOCAL_SYNTAX_SOURCE, True, False, "simp", False),
    ]:
        path = work / f"{label}.lean"
        path.write_text(text)
        command = [sys.executable, str(ROOT / "Experiment/lean_toolchain_cache.py"), "inventory"]
        if allow_errors:
            command.append("--allow-elaboration-errors")
        if header:
            command.append("--header-imports")
        code, output, _ = inventory.run(command + [str(path)], timeout=120)
        log = path.with_suffix(".log")
        log.write_text(output)
        fallback = "FULL_FALLBACK" in output
        if code or fallback != expect_fallback:
            raise RuntimeError(f"{label}: expected a clean syntax parse; see {log}")
        entries = [json.loads(line) for line in output.splitlines() if line.startswith("{")]
        expected_count = int(expected_source is not None)
        if len(entries) != expected_count:
            raise RuntimeError(f"{label}: expected {expected_count} calls, got {len(entries)}")
        if expected_source is not None:
            entry = entries[0]
            actual_source = text.encode()[entry["startByte"]:entry["endByte"]].decode()
            if actual_source != expected_source:
                raise RuntimeError(
                    f"{label}: expected source {expected_source!r}, got {actual_source!r}"
                )
        records.append({"case": label, "expectedCount": expected_count,
                        "actualCount": len(entries),
                        "expectedFallback": expect_fallback, "actualFallback": fallback,
                        "source": str(path), "sourceSha256": sha(path),
                        "log": str(log), "logSha256": sha(log)})

    # This source forced the full fallback to elaborate parser-context
    # declarations.  With Lean's defaults it failed at valid `simp_rw`
    # commands; Mathlib's package options (notably autoImplicit=false) parse it
    # cleanly.  Pin both consumers so their parser semantics cannot drift.
    compiler_controls = [
        (
            "package-options-default-negative",
            [
                "lake", "env", "lean",
                "-R", str(ROOT / ".lake/packages/mathlib"),
                "-o", str(work / "package-options-default.olean"),
                str(PACKAGE_OPTIONS_SOURCE),
            ],
            False,
        ),
        (
            "package-options-positive",
            [
                "lake", "env", "lean",
                *PACKAGE_OPTION_ARGUMENTS,
                "-R", str(ROOT / ".lake/packages/mathlib"),
                "-o", str(work / "package-options-positive.olean"),
                str(PACKAGE_OPTIONS_SOURCE),
            ],
            True,
        ),
    ]
    for label, command, should_succeed in compiler_controls:
        code, output, _ = inventory.run(command, timeout=180)
        log = work / f"{label}.log"
        log.write_text(output)
        if (code == 0) != should_succeed:
            raise RuntimeError(f"{label}: unexpected compiler status; see {log}")
        if not should_succeed and "`simp` made no progress" not in output:
            raise RuntimeError(f"{label}: expected the option-sensitive failure; see {log}")
        records.append({
            "case": label,
            "expectedSuccess": should_succeed,
            "actualSuccess": code == 0,
            "source": str(PACKAGE_OPTIONS_SOURCE),
            "sourceSha256": sha(PACKAGE_OPTIONS_SOURCE),
            "log": str(log),
            "logSha256": sha(log),
        })

    package_commands = [
        (
            "package-options-inventory",
            [
                sys.executable,
                str(ROOT / "Experiment/lean_toolchain_cache.py"),
                "inventory",
                str(PACKAGE_OPTIONS_SOURCE),
            ],
            "SIMP_ENGINE_INVENTORY_FULL_FALLBACK file=",
            "inventory",
        ),
        (
            "package-options-scope",
            [
                sys.executable,
                str(ROOT / "Experiment/lean_toolchain_cache.py"),
                "scope",
                PACKAGE_OPTIONS_MODULE,
                str(PACKAGE_OPTIONS_SOURCE),
            ],
            f"SIMP_ENGINE_SCOPE_FULL_FALLBACK module={PACKAGE_OPTIONS_MODULE} file=",
            "scope",
        ),
    ]
    package_entries = {}
    source_bytes = PACKAGE_OPTIONS_SOURCE.read_bytes()
    for label, command, fallback_marker, consumer in package_commands:
        deferred_command = [*command[:3], "--defer-full-fallback", *command[3:]]
        code, deferred_output, _ = inventory.run(deferred_command, timeout=180)
        deferred_log = work / f"{label}-deferred.log"
        deferred_log.write_text(deferred_output)
        deferred_marker = (
            f"SIMP_ENGINE_INVENTORY_DEFERRED_FALLBACK file={PACKAGE_OPTIONS_SOURCE}"
            if consumer == "inventory"
            else f"SIMP_ENGINE_SCOPE_DEFERRED_FALLBACK module={PACKAGE_OPTIONS_MODULE} "
                 f"file={PACKAGE_OPTIONS_SOURCE}"
        )
        leaked_records = any(
            line.startswith("{") or line.startswith("SIMP_ENGINE_SCOPE_OCCURRENCE ")
            for line in deferred_output.splitlines()
        )
        if code or deferred_marker not in deferred_output or leaked_records or "FULL_FALLBACK" in deferred_output:
            raise RuntimeError(f"{label}: invalid deferred fallback; see {deferred_log}")
        records.append({
            "case": f"{label}-deferred",
            "expectedCount": 0,
            "actualCount": 0,
            "expectedDeferredFallback": True,
            "actualDeferredFallback": True,
            "source": str(PACKAGE_OPTIONS_SOURCE),
            "sourceSha256": sha(PACKAGE_OPTIONS_SOURCE),
            "log": str(deferred_log),
            "logSha256": sha(deferred_log),
        })

        full_command = [*command[:3], "--full-fallback-only", *command[3:]]
        code, output, _ = inventory.run(full_command, timeout=180)
        log = work / f"{label}.log"
        log.write_text(output)
        if consumer == "inventory":
            entries = [
                json.loads(line)
                for line in output.splitlines()
                if line.startswith("{")
            ]
            for entry in entries:
                if entry.pop("file", None) != str(PACKAGE_OPTIONS_SOURCE):
                    raise RuntimeError(f"{label}: occurrence names the wrong source; see {log}")
                entry["module"] = PACKAGE_OPTIONS_MODULE
        else:
            marker = "SIMP_ENGINE_SCOPE_OCCURRENCE "
            entries = [
                json.loads(line.split(marker, 1)[1])
                for line in output.splitlines()
                if line.startswith(marker)
            ]
            if any(entry.get("module") != PACKAGE_OPTIONS_MODULE for entry in entries):
                raise RuntimeError(f"{label}: occurrence names the wrong module; see {log}")
        for entry in entries:
            inventory.validate_occurrence(source_bytes, entry)
        ranges = [(entry["startByte"], entry["endByte"]) for entry in entries]
        if len(ranges) != len(set(ranges)):
            raise RuntimeError(f"{label}: duplicate occurrence ranges; see {log}")
        count = len(entries)
        fallback = fallback_marker in output
        if code or not fallback or count != PACKAGE_OPTIONS_OCCURRENCES:
            raise RuntimeError(
                f"{label}: expected a clean fallback with "
                f"{PACKAGE_OPTIONS_OCCURRENCES} occurrences; see {log}"
            )
        package_entries[consumer] = {
            (
                entry["startByte"], entry["endByte"], entry["line"], entry["column"],
                entry["kind"], entry["source"],
            )
            for entry in entries
        }
        records.append({
            "case": label,
            "expectedCount": PACKAGE_OPTIONS_OCCURRENCES,
            "actualCount": count,
            "expectedFallback": True,
            "actualFallback": fallback,
            "source": str(PACKAGE_OPTIONS_SOURCE),
            "sourceSha256": sha(PACKAGE_OPTIONS_SOURCE),
            "log": str(log),
            "logSha256": sha(log),
        })
    if package_entries["inventory"] != package_entries["scope"]:
        raise RuntimeError("package-options inventory and scope occurrences disagree")

    # The analysis executables must not statically preload aggregate Mathlib
    # extension state.  Otherwise elaborating this source in an isolated full
    # fallback redeclares its Aesop rule set and fails before returning syntax.
    preload_commands = [
        (
            "preloaded-rule-inventory",
            [
                sys.executable,
                str(ROOT / "Experiment/lean_toolchain_cache.py"),
                "inventory",
                "--full-fallback-only",
                str(PRELOADED_RULE_SOURCE),
            ],
            "SIMP_ENGINE_INVENTORY_FULL_FALLBACK file=",
            0,
            0,
        ),
        (
            "preloaded-rule-scope",
            [
                sys.executable,
                str(ROOT / "Experiment/lean_toolchain_cache.py"),
                "scope",
                "--full-fallback-only",
                PRELOADED_RULE_MODULE,
                str(PRELOADED_RULE_SOURCE),
            ],
            f"SIMP_ENGINE_SCOPE_FULL_FALLBACK module={PRELOADED_RULE_MODULE} file=",
            0,
            PRELOADED_RULE_DECLARATIONS,
        ),
    ]
    for label, command, fallback_marker, expected_occurrences, expected_declarations in preload_commands:
        code, output, _ = inventory.run(command, timeout=180)
        log = work / f"{label}.log"
        log.write_text(output)
        occurrences = sum(
            line.startswith("{") or line.startswith("SIMP_ENGINE_SCOPE_OCCURRENCE ")
            for line in output.splitlines()
        )
        declaration_marker = "SIMP_ENGINE_SCOPE_DECLARATION "
        declaration_entries = [
            json.loads(line.removeprefix(declaration_marker))
            for line in output.splitlines()
            if line.startswith(declaration_marker)
        ]
        declarations = len(declaration_entries)
        if (code or fallback_marker not in output or occurrences != expected_occurrences or
                declarations != expected_declarations):
            raise RuntimeError(f"{label}: aggregate extension state contaminated full fallback; see {log}")
        if expected_declarations:
            names = {entry.get("name") for entry in declaration_entries}
            source_size = PRELOADED_RULE_SOURCE.stat().st_size
            valid_ranges = all(
                entry.get("module") == PRELOADED_RULE_MODULE and
                type(entry.get("isProof")) is bool and
                all(type(entry.get(key)) is int for key in (
                    "startByte", "endByte", "selectionStartByte", "selectionEndByte"
                )) and
                0 <= entry["startByte"] <= entry["selectionStartByte"] <=
                    entry["selectionEndByte"] <= entry["endByte"] <= source_size
                for entry in declaration_entries
            )
            if names != PRELOADED_RULE_DECLARATION_NAMES or not valid_ranges:
                raise RuntimeError(f"{label}: malformed current-module declarations; see {log}")
        records.append({
            "case": label,
            "expectedOccurrences": expected_occurrences,
            "actualOccurrences": occurrences,
            "expectedDeclarations": expected_declarations,
            "actualDeclarations": declarations,
            "source": str(PRELOADED_RULE_SOURCE),
            "sourceSha256": sha(PRELOADED_RULE_SOURCE),
            "log": str(log),
            "logSha256": sha(log),
        })
    if {str(path): sha(path) for path in inputs} != before:
        raise RuntimeError("inventory inputs changed during validation")
    for item in archived:
        assert sha(Path(item["archivedPath"])) == item["sha256"]
    report = {"status": "passed", "acceptedCampaignCoverage": False,
              "records": records, "inputs": archived}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(work / "report.json")


if __name__ == "__main__":
    main()
