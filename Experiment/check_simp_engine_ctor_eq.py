#!/usr/bin/env python3
"""Compile and run the focused reduceCtorEq semantic-fold probe."""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = "Experiment/CtorEqFoldProbe.lean"
POSITIVE_MARKER = "CTOR_EQ_DIRECT ordinary,replay,proof,JSON: ok"
MUTATION_MARKER = "CTOR_EQ_DIRECT_MUTATIONS rejected=78"


def without_comments(source: str) -> str:
    source = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", "", source)


def check_source_guard() -> None:
    forbidden = (
        "constructorApp'?",
        "litToCtor",
        "isOffset?",
        "evalNat",
        "whnf",
        "mkNoConfusion",
        "mkEqFalse'",
    )
    semantic_source = (
        ROOT / "ExplicitLean/SimpEngine/SemanticSimproc.lean"
    ).read_text()
    semantic_start = semantic_source.index("private def natOffsetOperator?")
    semantic_end = semantic_source.index("private def strictFinMkParts", semantic_start)
    semantic = without_comments(semantic_source[semantic_start:semantic_end])
    replay_source = (ROOT / "ExplicitLean/SimpEngine.lean").read_text()
    start = replay_source.index("private def replaySemanticSimprocOutput")
    end = replay_source.index("private def pathHasChild", start)
    implementation = without_comments(replay_source[start:end])
    for token in forbidden:
        if token in semantic:
            raise RuntimeError(
                f"constructor semantic implementation invokes forbidden token {token!r}"
            )
        if token in implementation:
            raise RuntimeError(
                f"constructor replay implementation invokes forbidden token {token!r}"
            )


def main() -> None:
    check_source_guard()
    build = subprocess.run(
        ["lake", "build", "ExplicitLean:shared"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    if build.returncode:
        raise RuntimeError(build.stdout)
    query = subprocess.run(
        ["lake", "query", "ExplicitLean:shared", "--json"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    if query.returncode:
        raise RuntimeError(query.stdout + query.stderr)
    dylib = json.loads(query.stdout.strip())
    run = subprocess.run(
        ["lake", "env", "lean", f"--load-dynlib={dylib}", PROBE],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=300,
    )
    if run.returncode:
        raise RuntimeError(run.stdout)
    missing = [
        marker
        for marker in (POSITIVE_MARKER, MUTATION_MARKER)
        if marker not in run.stdout
    ]
    if missing:
        raise RuntimeError(
            "reduceCtorEq semantic-fold probe markers missing: "
            + ", ".join(missing)
            + "\n"
            + run.stdout
        )
    print("reduceCtorEq semantic fold, proof replay, and 78 mutations: ok")


if __name__ == "__main__":
    main()
