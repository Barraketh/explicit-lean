#!/usr/bin/env python3
"""Lock the frozen schema-27 fork, upstream map, and legacy contract."""

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
    "lakefile.toml",
    "ExplicitLean/SimpEngine.lean",
    "ExplicitLean/SimpEngine/Fingerprint.lean",
    "ExplicitLean/SimpEngine/IR.lean",
    "ExplicitLean/SimpEngine/Inventory.lean",
    "ExplicitLean/SimpEngine/Reference.lean",
    "ExplicitLean/SimpEngine/Runtime.lean",
    "ExplicitLean/SimpEngine/Recording.lean",
    "ExplicitLean/SimpEngine/Replay.lean",
    "ExplicitLean/SimpEngine/SemanticSimproc.lean",
    "ExplicitLean/SimpEngine/Source.lean",
    "ExplicitLeanMathlibAudit.lean",
    "ExplicitLeanMathlibAudit/FieldEq.lean",
    "SIMP_ENGINE_COVERAGE.md",
)

# Upstream implementations whose state-free negative branches and supported
# semantic simproc derivations are covered by the source-level review.
REVIEWED_UPSTREAM_HASHES: dict[str, str] = {
    "Init/Data/Fin/Basic.lean":
        "fcf6cfb3553deaf9eb88e62c51e7ab6c54c1d873953f65f2216b154034b7fc31",
    "Init/Prelude.lean":
        "44f86ebbb9ab743a05c6ebe2c674aadbf2c822bee874f1b16d7e6c8d56318dc9",
    "Init/SimpLemmas.lean":
        "43b85a7d431ed8966855f68bf7db7f36000f002cb2b191a9c87003e6a9506cea",
    "Lean/Elab/PreDefinition/WF/Preprocess.lean":
        "1288a4d870a94e30fad9f3d67a4488c29cb49dae947edcde2251ab51db69ddfa",
    "Lean/Expr.lean":
        "7d4418bf9fef6f72eac422db70613848f849f074573392e79fb86fe745e79f7e",
    "Lean/Meta/AppBuilder.lean":
        "2d11a3e6bf24e3572c340c58ae5250a9502720d8e2996b641b4c053b1696644c",
    "Lean/Meta/CtorRecognizer.lean":
        "1702e73c93bb81c978001a8206f6b22ec35186ed5f9e8313c70799a9b4b453cb",
    "Lean/Meta/LitValues.lean":
        "609f53f536b06d2b05d71c219cf0007064244084a82d9e88956f57e15eb72720",
    "Lean/Meta/Offset.lean":
        "b1322d582b1a8028325d8322968f40ade286526ecf0a142bcbbdba50510cee88",
    "Lean/Meta/Match/MatcherApp/Basic.lean":
        "d664d30764d31bb4cb6a0b58ab35e038b9e98e1b8b62233b60ce9c75c1229a1b",
    "Lean/Meta/Match/MatcherInfo.lean":
        "7a9067b5d788c656202c2e4cc74868f1f8531dfc73f3d8c94604c56f796d8d34",
    "Lean/Meta/Tactic/Simp/BuiltinSimprocs/Fin.lean":
        "5c8a2e3fd7c723c42abb0fdd16a77ebb05146e3aeca8f556a559831b7c3c9cba",
    "Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean":
        "c576304b94ae0969c058e084805ba359e2f5bd6158ef19c493c900e1405af4f4",
    "Lean/Meta/Tactic/Simp/BuiltinSimprocs/Int.lean":
        "5510cf5360d54ea45c957fb0411b87a497d6bb60b802d2ac2f7d523e9a1c8ff2",
    "Lean/Meta/Tactic/Simp/BuiltinSimprocs/Nat.lean":
        "6384d4df788555086a56e37c06731563d0d892d1c28ff15e3d61ca3a6169acea",
    "Lean/ToExpr.lean":
        "97ce56c718e5eeb86f308d10007485cac0803f92216d434a2aee3db6cfee7cd0",
    "Lean/Util/SafeExponentiation.lean":
        "8b8915c3a5892b125bc800023b5bd4f7eb5cdd4d08b9fcd84667e7196602b6eb",
    "Lean/AuxRecursor.lean":
        "c004ddcbd0d6475550e701e30b8035e146132f8f7c8d3d5c8486c1f465a6ff9f",
}

# Mathlib-owned implementations used by semantic interpreters are pinned
# independently from the Lean toolchain source root.
REVIEWED_MATHLIB_HASHES: dict[str, str] = {
    "Mathlib/Data/Fin/VecNotation.lean":
        "dffd4a79591dc0ca61e18c6babcecdcf2e3fc623e4b80981e84c60a60cefcbb0",
    "Mathlib/Tactic/Simproc/ExistsAndEq.lean":
        "8a96de10d08a39413ad7fa06d92a7e2312dbf922f1d30a22b523bc6835961b44",
    "Mathlib/Tactic/FieldSimp.lean":
        "7c4960c3c633aa093d2adf6b455449bd39f33342b52e48878cb058aa55ac00c2",
    "Mathlib/Tactic/FieldSimp/Discharger.lean":
        "87c89068d9bfda38de822505f93fc6b6f1b27d83e2085f27f950379416ad5c59",
}

# These values are changed only after a new source-level completeness review.
REVIEWED_HASHES: dict[str, str] = {
    "lakefile.toml":
        "a37efc6e358aaedadc967b5ddcfb639269ebf8613be8d235d529384d7cc5725e",
    "ExplicitLean/SimpEngine.lean":
        "8fe62915752b06e3f5eaf76146db67de3eda11d36e47df76c006629debcd7148",
    "ExplicitLean/SimpEngine/Fingerprint.lean":
        "6cbfb1377aa645224c8feb84e785274a3f2d3e04e77181d6dfc0ff1e06d82d77",
    "ExplicitLean/SimpEngine/IR.lean":
        "f790c9a13955a250fda5e6c1c1f92694f4d5000bef4f378fc11ee813eabdcfe6",
    "ExplicitLean/SimpEngine/Inventory.lean":
        "d08cefcb506f63b29c8c91f53fa089177d17b501473af554c4adf6c4002a44e8",
    "ExplicitLean/SimpEngine/Recording.lean":
        "098cb198a326e0efa6b3c74492f0001141d09a1a221363905b4d9f8770422a39",
    "ExplicitLean/SimpEngine/Reference.lean":
        "e3f59c3a7c5f01dec5a700eda0dad5d08199df7adee4ff557e548f4b5fca6bb0",
    "ExplicitLean/SimpEngine/Replay.lean":
        "ca06988d05c982db4ddccb48bd733c1c105ac02877f484002a552211537524a0",
    "ExplicitLean/SimpEngine/SemanticSimproc.lean":
        "62c8127196d33283a3d8c2b0191faec535047792358f49a1b476f9ecbcfed5e5",
    "ExplicitLean/SimpEngine/Runtime.lean":
        "03e71f3005a58dafdb12ad262634aa9a16e9cb689728aa604e547cd12192e5cd",
    "ExplicitLean/SimpEngine/Source.lean":
        "1808c85ae29a5508bde8b98bd6c886ca88ec8d074de8b95857b2a6133a09f5d3",
    "ExplicitLeanMathlibAudit.lean":
        "83d05f986e7bcab4c3a7a0b4c8af171cf5959ecf439550cda4468bf99e444a02",
    "ExplicitLeanMathlibAudit/FieldEq.lean":
        "c5c0ec09f153a7e73e804ec2093e85708c0bd3c38b2f8161a6355012d0019112",
    "SIMP_ENGINE_COVERAGE.md":
        "207bea3e5a7ac673d6616593a109d81d788d03db127662fd1de52bbe55c10d56",
}
EXPECTED_LINEAGE_DIGEST = (
    "60511e7930514efa28c4ce54b954ed7662baca737de447469781ffdbc035aab7"
)
EXPECTED_CONTROLLED_DIGEST = (
    "ff10456b202a198d347c917b70f058a4567298594af2f965f1463c1d7f70e6d3"
)
EXPECTED_DECLARATION_COUNT = 256

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
    mathlib_root = ROOT / ".lake" / "packages" / "mathlib"
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
        "reviewedUpstreamHashes": {
            relative: sha((upstream_root / relative).read_bytes())
            for relative in REVIEWED_UPSTREAM_HASHES
        },
        "reviewedMathlibHashes": {
            relative: sha((mathlib_root / relative).read_bytes())
            for relative in REVIEWED_MATHLIB_HASHES
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
        "reviewedUpstreamHashes": REVIEWED_UPSTREAM_HASHES,
        "reviewedMathlibHashes": REVIEWED_MATHLIB_HASHES,
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
        "legacy schema-27 source review: "
        f"{current['lineageCount']} upstream-lineage declarations, "
        f"{current['controlledCount']} controlled declarations: ok"
    )


if __name__ == "__main__":
    main()
