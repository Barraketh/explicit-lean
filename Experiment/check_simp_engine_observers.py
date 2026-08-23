#!/usr/bin/env python3
"""Mechanically bind every coverage-matrix row to schema-16 implementation text."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MATRIX = ROOT / "SIMP_ENGINE_COVERAGE.md"
ENGINE = (ROOT / "ExplicitLean/SimpEngine.lean").read_text(encoding="utf-8")
IR = (ROOT / "ExplicitLean/SimpEngine/IR.lean").read_text(encoding="utf-8")
RUNTIME = (ROOT / "ExplicitLean/SimpEngine/Runtime.lean").read_text(encoding="utf-8")
SOURCE = ENGINE + "\n" + IR + "\n" + RUNTIME


OBSERVERS: dict[str, tuple[str, ...]] = {
    "`simpLoop` cache": ("recordBranch \"struct.cacheHit\"", ".cacheHit sourcePath"),
    "`pre` step": ("withPhase .pre", "stepDisposition : StepDisposition"),
    "`post` step": ("withPhase .post", ".postRestart"),
    "`reduceStep`: mvar head": ("reduce.instantiateMVars", ".instantiateMVars"),
    "`reduceStep`: beta": ("reduce.beta", ".beta"),
    "`reduceStep`: native projection": ("reduce.projection\"", ".projection structureName field"),
    "`reduceStep`: projection function": ("reduce.projectionFunction", ".requestedClass", ".constructorClass"),
    "`reduceStep`: iota": ("reduce.iota", ".iota"),
    "`reduceStep`: zeta": ("reduce.zetaUsed", ".zetaUsed cfg.zetaHave"),
    "`reduceStep`: unused let": ("reduce.zetaUnused", ".zetaUnused"),
    "`unfold?`: requested": ("DeltaStrategy.requestedSmart", "DeltaStrategy.requestedPartial", "DeltaStrategy.requestedOrdinary"),
    "`unfold?`: auto": (".autoSmart", ".autoMatch"),
    "`foldRawNatLit`": ("reduce.foldRawNatLit", ".foldRawNatLit"),
    "`reduceFVar`": ("reduce.localDef", "localRefOfDecl", "LocalDefReason.zetaDelta"),
    "`simpProj`": ("struct.projectionMajor.simp", "struct.projectionMajor.dsimp"),
    "`simpApp`": ("CongruenceChoice", "struct.congruence.user", "struct.congruence.generated", "struct.congruence.generic"),
    "user congruence": (".user c.theoremName c.priority c.hypothesesPos", ".userCongrHypothesis"),
    "generated congruence": ("shapeFingerprint", "synthesizedAssignments", ".autoCongrArgument"),
    "generic congruence": (".generic modes", ".appArgument i .simp", ".appArgument i .dsimp"),
    "`simpMatch` direct reduction": ("reduce.matchIota", ".iota .visit"),
    "`simpMatchDiscrs?`": ("struct.matchDiscriminants", ".matchDiscriminant i"),
    "`simpMatchCore`": ("tryTheoremRecorded?", "origin := .decl matchEq"),
    "lambda traversal": ("struct.lambdaTelescope", ".lambdaDomain", ".lambdaBody"),
    "implication traversal": ("implicationContextual", "implicationPlain", ".contextualScope"),
    "forall traversal": ("propositionDomainTransport", "propositionDomainDSimp", "nonPropositionDSimp"),
    "dependent let": ("struct.letToHave", ".letBody"),
    "have telescope": ("struct.haveTelescope", "struct.dropUnusedHave", ".haveValue", ".haveBody"),
    "`dpre`/`dpost`": ("withPhase .dpre", "withPhase .dpost", "dpreDefaultRecorded", "dpostDefaultRecorded"),
    "`dsimpReduce`": ("private def dsimpReduce", "reduceFVar"),
    "dsimp transform": ("struct.dsimpTransform", "struct.dsimpCacheHit", "dsimpTransformWithCache"),
    "theorem preprocessing": ("variant", "ruleFingerprint", "lhsFingerprint"),
    "indexed rewrite": ("getMatchWithExtra", "getMatchLiberal", "indexMode"),
    "theorem match": ("MatchEnvelope", "binderAssignments", "thm.perm", "resolveBinderNameHint"),
    "instance arguments": ("instanceAssignments", "synthesizeInstance", "skipAssignedInstances"),
    "implicit defeq proof": ("useImplicitDefEqProofRecorded", "proofPresent"),
    "recursive premise simp": ("beginPremiseProgram", "finishPremiseProgram", "program := inner.program"),
    "default discharge terminals": (".localAssumption", ".equationHypothesis", ".dischargeRfl", ".isTrue"),
    "custom discharger": ("customDischarger", "deferRecording .customDischarger"),
    "`simpUsingDecide`": ("builtin.decideTrue", "builtin.decideFalse"),
    "`simpArith`": ("natConstraintHandler", "divisibilityHandler", "builtin.arith.intExpression"),
    "`simpGround`/`seval`": ("withPath .ground", "ground.delta", "mkSEvalMethods"),
    "pre/post simprocs": ("simprocCoreRecorded", "observeSimproc", "simproc.simp"),
    "dsimprocs": ("dsimprocCoreRecorded", "simproc.dsimp"),
    "target result": ("SubjectTerminal", "targetTrue", "targetTransport"),
    "local result": ("localFalse", "localDefEqReplace", "localAssertClear"),
    "`simpGoal` batching": ("structure SubjectProgram", "subjects : Array SubjectProgram"),
    "`failIfUnchanged`": ("inductive ExecutionOutcome", "success (changed : Bool)", "tacticFailure"),
}


def matrix_rows() -> list[str]:
    text = MATRIX.read_text(encoding="utf-8")
    section = text.split("## 4. Implementation-to-IR coverage matrix", 1)[1].split("## 5.", 1)[0]
    rows: list[str] = []
    for line in section.splitlines():
        match = re.match(r"\| (.+?) \|", line)
        if not match:
            continue
        name = match.group(1)
        if name not in {"Upstream site", "---"}:
            rows.append(name)
    return rows


def main() -> None:
    rows = matrix_rows()
    missing_manifest = sorted(set(rows) - set(OBSERVERS))
    stale_manifest = sorted(set(OBSERVERS) - set(rows))
    if missing_manifest or stale_manifest:
        raise RuntimeError(
            f"coverage manifest mismatch: missing={missing_manifest}, stale={stale_manifest}"
        )
    failures: list[str] = []
    for row in rows:
        missing = [pattern for pattern in OBSERVERS[row] if pattern not in SOURCE]
        if missing:
            failures.append(f"{row}: {missing}")
    if failures:
        raise RuntimeError("unobserved_transition:\n" + "\n".join(failures))
    print(f"schema-16 observer audit: {len(rows)} matrix rows: ok")


if __name__ == "__main__":
    main()
