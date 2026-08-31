#!/usr/bin/env python3
"""A generated-looking public theorem must not disappear during replay.

Both fixtures run stock simp through a discharger that adds a checked proof
declaration. Genuine private proof helpers may be omitted; public proof_1 may
not. The outer first catches recorder errors, so the negative must be rejected
by authenticated recording-abort evidence even though Lean exits successfully.
"""

from __future__ import annotations

import json
from pathlib import Path
import tempfile

import boundary_protocol as protocol
import check_simp_engine_boundary_source as source


ROOT = Path(__file__).resolve().parents[1]
MODULE = "Experiment.SimpEnginePrivateDeclarations"


def fixture(*, private: bool) -> str:
    name = "Lean.mkPrivateNameCore (← getEnv).mainModule `sample.proof_1" if private else "`sample.proof_1"
    return """module
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
open Lean Meta Elab Tactic

-- Keep namespace creation outside the observed boundary so this fixture
-- isolates the declaration policy, not a separate namespace-state change.
private theorem sample.warmup : True := True.intro
namespace sample
end sample

elab "add_checked_proof" : tactic => withMainContext do
  let name := NAME
  addDecl <| .thmDecl {
    name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
  evalTactic (← `(tactic| assumption))

theorem sample (p q : Prop) (h : p) (hpq : p → q) : q := by
  first
  | simp_engine_boundary_record "proof-declaration-test"
      (disch := add_checked_proof) [hpq]
  | exact hpq h
""".replace("NAME", name)


def check_case(work: Path, dylib: str, *, private: bool) -> None:
    label = "private-proof" if private else "public-proof_1"
    path = work / label / "Experiment" / "SimpEnginePrivateDeclarations.lean"
    path.parent.mkdir(parents=True)
    path.write_text(fixture(private=private), encoding="utf-8")
    output, nonce = source.compile_recording_source(dylib, path)
    path.with_suffix(".log").write_text(output, encoding="utf-8")
    path.with_suffix(".nonce.json").write_text(json.dumps({"nonce": nonce}) + "\n")
    artifacts = protocol.parse_framed_json_lines(
        output, marker=source.ARTIFACT_MARKER, expected_nonce=nonce,
        label="boundary artifact",
    )
    try:
        protocol.check_recording_abort_markers(
            output, expected_nonce=nonce, expected_module=MODULE,
            expected_occurrence="proof-declaration-test",
        )
    except RuntimeError as error:
        if private or "boundary_comparison_unsupported_environment_delta:sample.proof_1" not in str(error):
            raise
        if artifacts:
            raise RuntimeError("public proof mutation produced usable artifacts")
    else:
        if not private:
            raise RuntimeError("public theorem proof_1 was silently omitted by replay")
        if len(artifacts) != 1 or artifacts[0]["status"] != "success":
            raise RuntimeError(f"private helper did not produce one valid artifact: {artifacts}")
        protocol.validate_report(artifacts[0], "proof-declaration-test", MODULE)
    print(f"private declaration boundary: {label}: ok", flush=True)


def main() -> None:
    parent = ROOT / ".lake" / "week-2026-08-31" / "private-declarations"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="fixture-", dir=parent))
    print(f"private declaration evidence: {work}", flush=True)
    # Query does not request an unrelated build; the caller builds the affected
    # runtime first, as with the other focused boundary checks.
    dylib = source.query_json_string(
        source.run(["lake", "query", "ExplicitLean:shared", "--json"]), "shared query"
    )
    check_case(work, dylib, private=True)
    check_case(work, dylib, private=False)


if __name__ == "__main__":
    main()
