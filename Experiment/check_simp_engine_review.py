#!/usr/bin/env python3
"""Lock the manually reviewed fork-to-upstream declaration map and semantic core."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FORK = ROOT / "ExplicitLean" / "SimpEngine.lean"
REVIEWED_FILES = (
    "ExplicitLean/SimpEngine.lean",
    "ExplicitLean/SimpEngine/Fingerprint.lean",
    "ExplicitLean/SimpEngine/IR.lean",
    "ExplicitLean/SimpEngine/Inventory.lean",
    "ExplicitLean/SimpEngine/Reference.lean",
    "ExplicitLean/SimpEngine/Runtime.lean",
    "ExplicitLean/SimpEngine/Recording.lean",
    "ExplicitLean/SimpEngine/Replay.lean",
    "ExplicitLean/SimpEngine/Source.lean",
    "SIMP_ENGINE_COVERAGE.md",
)

# These values are changed only after a new source-level completeness review.
REVIEWED_HASHES: dict[str, str] = {
    "ExplicitLean/SimpEngine.lean":
        "70c98d057b9b3da087c10ed197ca836fdad9dab348b7843bcf5da7ad1379cd9e",
    "ExplicitLean/SimpEngine/Fingerprint.lean":
        "e2c1e4547133fee8e4a18bcd07de4fde3036e5b5fde9b8240e0a5fe01b4863ff",
    "ExplicitLean/SimpEngine/IR.lean":
        "85e3b9004bf227e6b7bb777471543161aa776cd0ed7db8296e84ee5eca0d3dac",
    "ExplicitLean/SimpEngine/Inventory.lean":
        "d08cefcb506f63b29c8c91f53fa089177d17b501473af554c4adf6c4002a44e8",
    "ExplicitLean/SimpEngine/Recording.lean":
        "1d5b3ab8ed2cc64d4ed8733b54d891d69d51edf8fa0c382e94efe7edf863e926",
    "ExplicitLean/SimpEngine/Reference.lean":
        "e3f59c3a7c5f01dec5a700eda0dad5d08199df7adee4ff557e548f4b5fca6bb0",
    "ExplicitLean/SimpEngine/Replay.lean":
        "ea34fe5b55040403cae4c38812afcc0fe36233bf87cd09e5f9a2253c725a5477",
    "ExplicitLean/SimpEngine/Runtime.lean":
        "5935c0f152933590a8a3d8fa6c6a67cb1b8cfcdb1f6c9dc588e712a78593627a",
    "ExplicitLean/SimpEngine/Source.lean":
        "7177faa4193c50ccbfab06fa9bba114748c8d0953714fdb4b62711d16fc4ea18",
    "SIMP_ENGINE_COVERAGE.md":
        "d995059eafa30d9bb489e60709af8d7311194a84dcf77e885774dcf44b1b0dbb",
}
EXPECTED_LINEAGE_DIGEST = (
    "789b8ce55475bffdf2a6088c13d0d5d3af8a43ed7d8c5fc50c3c6393c003fee9"
)
EXPECTED_CONTROLLED_DIGEST = (
    "4468214d507659884927cc3d61d0a4b5592905a01208831d21842b38985155bd"
)
EXPECTED_DECLARATION_COUNT = 227

MAIN = "Lean/Meta/Tactic/Simp/Main.lean"
REWRITE = "Lean/Meta/Tactic/Simp/Rewrite.lean"
TRANSFORM = "Lean/Meta/Transform.lean"
TYPES = "Lean/Meta/Tactic/Simp/Types.lean"
SIMPROC = "Lean/Meta/Tactic/Simp/Simproc.lean"

# (upstream file, upstream declaration, duplicate ordinal, fork declaration)
LINEAGE: tuple[tuple[str, str, int, str], ...] = (
    (TYPES, "Simproc", 0, "Simproc"),
    (TYPES, "DSimproc", 0, "DSimproc"),
    (TYPES, "Methods", 0, "Methods"),
    (TYPES, "MethodsRefPointed", 0, "MethodsRefPointed"),
    (TYPES, "MethodsRef", 0, "MethodsRef"),
    (TYPES, "Methods.toMethodsRefImpl", 0, "Methods.toMethodsRefImpl"),
    (TYPES, "Methods.toMethodsRef", 0, "Methods.toMethodsRef"),
    (TYPES, "MethodsRef.toMethodsImpl", 0, "MethodsRef.toMethodsImpl"),
    (TYPES, "MethodsRef.toMethods", 0, "MethodsRef.toMethods"),
    (TYPES, "getMethods", 0, "getMethods"),
    (TYPES, "pre", 0, "pre"),
    (TYPES, "post", 0, "post"),
    (TYPES, "getContext", 0, "getContext"),
    (TYPES, "getConfig", 0, "getConfig"),
    (TYPES, "getSimpTheorems", 0, "getSimpTheorems"),
    (TYPES, "getSimpCongrTheorems", 0, "getSimpCongrTheorems"),
    (TYPES, "inDSimp", 0, "inDSimp"),
    (TYPES, "withIncDischargeDepth", 0, "withIncDischargeDepth"),
    (TYPES, "withSimpTheorems", 0, "withSimpTheorems"),
    (TYPES, "withSimpIndexConfig", 0, "withSimpIndexConfig"),
    (TYPES, "withSimpMetaConfig", 0, "withSimpMetaConfig"),
    (TYPES, "withParent", 0, "withParent"),
    (TYPES, "withUserConfig", 0, "withUserConfig"),
    (TYPES, "withFreshCache", 0, "withFreshCache"),
    (TYPES, "withPreservedCache", 0, "withPreservedCache"),
    (TYPES, "withInDSimpWithCache", 0, "withInDSimpWithCache"),
    (TYPES, "recordTriedSimpTheorem", 0, "recordTriedSimpTheorem"),
    (TYPES, "recordSimpTheorem", 0, "recordSimpTheorem"),
    (TYPES, "recordCongrTheorem", 0, "recordCongrTheorem"),
    (TYPES, "withDischarger", 0, "withDischarger"),
    (TYPES, "andThen", 0, "andThen"),
    (TYPES, "dandThen", 0, "dandThen"),
    (TYPES, "simp", 0, "simp"),
    (TYPES, "dsimp", 0, "dsimp"),
    (TYPES, "mkCongrFun'", 0, "mkCongrFun'"),
    (TYPES, "mkCongrPrefix", 0, "mkCongrPrefix"),
    (TYPES, "mkCongrArg'", 0, "mkCongrArg'"),
    (TYPES, "mkCongr'", 0, "mkCongr'"),
    (REWRITE, "Discharge", 0, "Discharge"),
    (REWRITE, "dischargeUsingAssumption?", 0, "dischargeUsingAssumption?"),
    (REWRITE, "mkMethods", 0, "mkMethods"),
    (REWRITE, "mkDefaultMethodsCore", 0, "mkDefaultMethodsCore"),
    (REWRITE, "mkDefaultMethods", 0, "mkDefaultMethods"),
    (SIMPROC, "simprocCore", 0, "simprocCoreRecorded"),
    (SIMPROC, "dsimprocCore", 0, "dsimprocCoreRecorded"),
    (SIMPROC, "simprocArrayCore", 0, "simprocArrayRecorded"),
    (SIMPROC, "dsimprocArrayCore", 0, "dsimprocArrayRecorded"),
    (MAIN, "isOfNatNatLit", 0, "isOfNatNatLit"),
    (MAIN, "foldRawNatLit", 0, "foldRawNatLit"),
    (MAIN, "isOfScientificLit", 0, "isOfScientificLit"),
    (MAIN, "isCharLit", 0, "isCharLit"),
    (MAIN, "unfoldDefinitionAny?", 0, "unfoldDefinitionAny?"),
    (MAIN, "reduceProjFn?", 0, "reduceProjFn?"),
    (MAIN, "reduceFVar", 0, "reduceFVar"),
    (MAIN, "isMatchDef", 0, "isMatchDef"),
    (MAIN, "unfold?", 0, "unfold?"),
    (MAIN, "reduceStep", 0, "reduceStep"),
    (MAIN, "reduce", 0, "reduce"),
    (MAIN, "lambdaTelescopeDSimp", 0, "lambdaTelescopeDSimp"),
    (MAIN, "withNewLemmas", 0, "withNewLemmas"),
    (TYPES, "congrArgs", 0, "congrArgs"),
    (TYPES, "simpAppUsingCongr", 0, "simpAppUsingCongr"),
    (TYPES, "tryAutoCongrTheorem?", 0, "tryAutoCongrTheorem?"),
    (MAIN, "simpProj", 0, "simpProj"),
    (MAIN, "simpConst", 0, "simpConst"),
    (MAIN, "simpLambda", 0, "simpLambda"),
    (MAIN, "simpArrow", 0, "simpArrow"),
    (MAIN, "simpForall", 0, "simpForall"),
    (MAIN, "simpHaveTelescope", 0, "simpHaveTelescope"),
    (MAIN, "simpLet", 0, "simpLet"),
    (MAIN, "dsimpReduce", 0, "dsimpReduce"),
    (MAIN, "doNotVisitProofs", 0, "doNotVisitProofs"),
    (MAIN, "doNotVisit", 0, "doNotVisit"),
    (MAIN, "doNotVisitOfNat", 0, "doNotVisitOfNat"),
    (MAIN, "doNotVisitOfScientific", 0, "doNotVisitOfScientific"),
    (MAIN, "doNotVisitCharLit", 0, "doNotVisitCharLit"),
    (MAIN, "dsimpImpl", 0, "dsimpImpl"),
    (MAIN, "visitFn", 0, "visitFn"),
    (MAIN, "congrDefault", 0, "congrDefault"),
    (MAIN, "processCongrHypothesis", 0, "processCongrHypothesis"),
    (MAIN, "trySimpCongrTheorem?", 0, "trySimpCongrTheorem?"),
    (MAIN, "congr", 0, "congr"),
    (MAIN, "simpApp", 0, "simpApp"),
    (MAIN, "simpStep", 0, "simpStep"),
    (MAIN, "cacheResult", 0, "cacheResult"),
    (MAIN, "simpLoop", 0, "simpLoop"),
    (MAIN, "simpImpl", 0, "simpImpl"),
    (MAIN, "withCatchingRuntimeEx", 0, "withCatchingRuntimeEx"),
    (MAIN, "recordSimpUses", 0, "recordSimpUses"),
    (MAIN, "mainCore", 0, "mainCore"),
    (MAIN, "main", 0, "main"),
    (MAIN, "dsimpMainCore", 0, "dsimpMainCore"),
    (MAIN, "dsimpMain", 0, "dsimpMain"),
    (REWRITE, "discharge?'", 0, "dischargeRecorded?"),
    (REWRITE, "synthesizeArgs", 0, "synthesizeRecordedArgs"),
    (REWRITE, "useImplicitDefEqProof", 0, "useImplicitDefEqProofRecorded"),
    (REWRITE, "tryTheoremCore", 0, "tryTheoremCoreRecorded"),
    (REWRITE, "tryTheoremWithExtraArgs?", 0, "tryTheoremWithExtraArgsRecorded?"),
    (REWRITE, "tryTheorem?", 0, "tryTheoremRecorded?"),
    (REWRITE, "rewrite?", 0, "rewriteRecorded?"),
    (REWRITE, "simpUsingDecide", 0, "simpUsingDecideRecorded"),
    (REWRITE, "simpArith", 0, "simpArithRecorded"),
    (REWRITE, "simpMatchDiscrs?", 0, "simpMatchDiscrs?"),
    (REWRITE, "simpMatchCore", 0, "simpMatchCore"),
    (REWRITE, "simpMatch", 0, "simpMatch"),
    (REWRITE, "dischargeGround", 0, "dischargeGround"),
    (REWRITE, "sevalGround", 0, "sevalGround"),
    (REWRITE, "preSEval", 0, "preSEval"),
    (REWRITE, "postSEval", 0, "postSEval"),
    (REWRITE, "mkSEvalMethods", 0, "mkSEvalMethods"),
    (REWRITE, "mkSEvalContext", 0, "mkSEvalContext"),
    (REWRITE, "seval", 0, "seval"),
    (REWRITE, "simpGround", 0, "simpGround"),
    (REWRITE, "preDefault", 0, "preDefault"),
    (REWRITE, "postDefault", 0, "postDefault"),
    (REWRITE, "isEqnThmHypothesis", 0, "isEqnThmHypothesis"),
    (REWRITE, "dischargeEqnThmHypothesis?", 0, "dischargeEqnThmHypothesis?"),
    (REWRITE, "dischargeRfl", 0, "dischargeRfl"),
    (REWRITE, "dischargeDefault?", 0, "dischargeDefault?"),
    (TRANSFORM, "transformWithCache", 0, "dsimpTransformWithCache"),
)

DECL_RE = re.compile(
    r"^(?:(?:private|protected|unsafe|partial|noncomputable)\s+)*"
    r"(?:@\[[^\]]+\]\s+)?(?:(?:private|unsafe|partial)\s+)*"
    r"(def|opaque|abbrev|structure|inductive)\s+([A-Za-z_][A-Za-z0-9_.'?]*)",
    re.MULTILINE,
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declarations(path: Path) -> dict[str, list[tuple[str, str]]]:
    text = path.read_text(encoding="utf-8")
    matches = list(DECL_RE.finditer(text))
    result: dict[str, list[tuple[str, str]]] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        result.setdefault(match.group(2), []).append((match.group(1), text[match.start():end]))
    return result


def source_root() -> Path:
    completed = subprocess.run(
        ["lean", "--print-prefix"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30, check=True,
    )
    return Path(completed.stdout.strip()) / "src" / "lean"


def current_values() -> dict[str, object]:
    upstream_root = source_root()
    fork_decls = declarations(FORK)
    lineage_targets: set[str] = set()
    lineage_rows: list[str] = []
    upstream_cache: dict[str, dict[str, list[tuple[str, str]]]] = {}
    for relative, upstream_name, ordinal, fork_name in LINEAGE:
        upstream = upstream_cache.setdefault(
            relative, declarations(upstream_root / relative)
        )
        if upstream_name not in upstream or ordinal >= len(upstream[upstream_name]):
            raise RuntimeError(f"missing upstream lineage declaration: {relative}:{upstream_name}#{ordinal}")
        if fork_name not in fork_decls or len(fork_decls[fork_name]) != 1:
            raise RuntimeError(f"missing or duplicate fork lineage declaration: {fork_name}")
        lineage_targets.add(fork_name)
        upstream_kind, upstream_body = upstream[upstream_name][ordinal]
        fork_kind, fork_body = fork_decls[fork_name][0]
        lineage_rows.append(
            f"{relative}:{upstream_name}#{ordinal}:{upstream_kind}:{sha(upstream_body.encode())}:"
            f"{fork_name}:{fork_kind}:{sha(fork_body.encode())}"
        )
    controlled_rows = sorted(
        f"{name}:{kind}:{sha(body.encode())}"
        for name, entries in fork_decls.items()
        if name not in lineage_targets
        for kind, body in entries
    )
    declaration_count = sum(len(entries) for entries in fork_decls.values())
    return {
        "reviewedHashes": {
            relative: sha((ROOT / relative).read_bytes()) for relative in REVIEWED_FILES
        },
        "lineageDigest": sha("\n".join(sorted(lineage_rows)).encode()),
        "controlledDigest": sha("\n".join(controlled_rows).encode()),
        "declarationCount": declaration_count,
        "lineageCount": len(lineage_rows),
        "controlledCount": len(controlled_rows),
    }


def main() -> None:
    current = current_values()
    if "--print-current" in sys.argv:
        print(json.dumps(current, indent=2, sort_keys=True))
        return
    expected = {
        "reviewedHashes": REVIEWED_HASHES,
        "lineageDigest": EXPECTED_LINEAGE_DIGEST,
        "controlledDigest": EXPECTED_CONTROLLED_DIGEST,
        "declarationCount": EXPECTED_DECLARATION_COUNT,
    }
    for key, value in expected.items():
        if current[key] != value:
            raise RuntimeError(
                f"simp_engine_review_drift: {key}: {current[key]!r} != {value!r}"
            )
    fork = FORK.read_text(encoding="utf-8")
    forbidden = ("Reduction.projection `_unknown", "synthesizeArgs (.decl")
    found = [token for token in forbidden if token in fork]
    if found:
        raise RuntimeError(f"unidentified or ambient operations returned: {found}")
    print(
        "schema-17 source review: "
        f"{current['lineageCount']} upstream-lineage declarations, "
        f"{current['controlledCount']} controlled declarations: ok"
    )


if __name__ == "__main__":
    main()
