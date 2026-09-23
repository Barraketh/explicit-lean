#!/usr/bin/env python3
"""Check source-applied rewrite arguments survive validation and replay."""

from __future__ import annotations

import copy
import json
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "Experiment" / "pipeline"))
import render as R  # noqa: E402

FIXTURE = ROOT / "test" / "SimpTrace" / "SourceAppliedArguments.lean"
MARKERS = {
    "GLOBAL": "SOURCE_APPLIED_GLOBAL_TRACE_PATH",
    "METHOD": "SOURCE_APPLIED_METHOD_TRACE_PATH",
    "IF_NEG": "SOURCE_APPLIED_IF_NEG_TRACE_PATH",
    "LOCAL": "SOURCE_APPLIED_LOCAL_TRACE_PATH",
    "BARE_IF_NEG": "SOURCE_APPLIED_BARE_IF_NEG_TRACE_PATH",
}
CALLS = {
    "GLOBAL": 'simp_trace only [mul_inv_cancel_left₀ ha] =>trace "SOURCE_APPLIED_GLOBAL_TRACE_PATH"',
    "METHOD": 'simp_trace only [hf.eq_iff] =>trace "SOURCE_APPLIED_METHOD_TRACE_PATH"',
    "IF_NEG": 'simp_trace only [if_neg (not_le.mpr hx)] =>trace "SOURCE_APPLIED_IF_NEG_TRACE_PATH"',
    "LOCAL": 'simp_trace only [(h hp)] =>trace "SOURCE_APPLIED_LOCAL_TRACE_PATH"',
    "BARE_IF_NEG": 'simp_trace (discharger := assumption) only [if_neg] at hEq =>trace "SOURCE_APPLIED_BARE_IF_NEG_TRACE_PATH"',
}


def run_lean(path: pathlib.Path, *, success: bool = True) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        capture_output=True, text=True, timeout=1800,
    )
    if (proc.returncode == 0) != success:
        raise AssertionError(
            f"Lean returned {proc.returncode} for {path}:\n{proc.stdout}{proc.stderr}"
        )
    return proc


def render_trace(
    path: pathlib.Path, text: str, *, require_source_identity: bool = True
) -> tuple[str, dict]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    steps = raw["locations"][0]["steps"]
    if not steps:
        raise AssertionError("expected a source-backed rewrite, got no steps")
    step = steps[0]
    if "sourceValue" in step or "sourceValue?" in step:
        raise AssertionError("internal source validation evidence leaked into trace JSON")
    derivation = step.get("derivation", {})
    if require_source_identity and (
        derivation.get("source") != "simp-argument" or derivation.get("argId") is None
    ):
        raise AssertionError(f"rewrite lacks direct source-argument identity: {step!r}")
    if derivation.get("source") == "simp-argument" and "args" in step:
        raise AssertionError(f"source-backed replay duplicated validator args: {step!r}")
    # Recovered source applications are validation evidence only. The exact
    # source term remains the renderer's spelling and args are not duplicated.
    rendered, _ = R.render_trace(
        {"schema": "simp-trace-v2", "site": {"sourceArgs": raw["sourceArgs"]},
         "locations": raw["locations"]},
        source_text=text,
    )
    if len(rendered) != 1:
        raise AssertionError(f"expected one rendered location, got {rendered!r}")
    return rendered[0], raw


def main() -> None:
    run_dir = pathlib.Path(tempfile.mkdtemp(
        prefix="source-applied-arguments-", dir=ROOT / ".lake" / "private"
    ))
    traces = {name: run_dir / f"{name.lower()}.json" for name in MARKERS}
    source = FIXTURE.read_text(encoding="utf-8")
    recorded_source = source
    for name, marker in MARKERS.items():
        recorded_source = recorded_source.replace(marker, traces[name].as_posix())
    recorded = run_dir / "SourceAppliedArgumentsRecorded.lean"
    recorded.write_text(recorded_source, encoding="utf-8")
    run_lean(recorded)

    rendered: dict[str, str] = {}
    raw: dict[str, dict] = {}
    for name in MARKERS:
        rendered[name], raw[name] = render_trace(
            traces[name], recorded_source,
            require_source_identity=(name != "BARE_IF_NEG"),
        )

    expected_terms = {
        "GLOBAL": "mul_inv_cancel_left₀ ha",
        "METHOD": "hf.eq_iff",
        "IF_NEG": "if_neg (not_le.mpr hx)",
        "LOCAL": "(h hp)",
        "BARE_IF_NEG": "if_neg",
    }
    for name, term in expected_terms.items():
        if term not in rendered[name]:
            raise AssertionError(f"{name}: source term was not preserved: {rendered[name]}")
    if not raw["BARE_IF_NEG"]["locations"][0]["steps"][0].get("side"):
        raise AssertionError("bare if_neg should carry its recorded proof side trace")

    replay_source = source
    for name, call in CALLS.items():
        if call not in replay_source:
            raise AssertionError(f"fixture lost {name} replay marker")
        replay_source = replay_source.replace(call, rendered[name])
    replayed = run_dir / "SourceAppliedArgumentsReplayed.lean"
    replayed.write_text(replay_source, encoding="utf-8")
    run_lean(replayed)

    # A source entry `[h]` is not the application `(h hp)`. If simp discharges
    # h's explicit proof binder, that evidence must be the serialized ordered
    # side trace—not an inferred application hidden in validator-only state.
    split_trace = run_dir / "split-local.json"
    split_source = run_dir / "SplitLocalRecorded.lean"
    split_source.write_text(
        f"""import ExplicitLean.SimpTrace
import ExplicitLean.ExplicitRw

namespace ExplicitLean.SimpTrace.SourceAppliedArguments

example (P : Prop) (hp : P) (f g : Nat → Nat)
    (h : P → ∀ n, f n = g n) (n : Nat) : f n = g n := by
  simp_trace (discharger := assumption) only [h] =>trace \"{split_trace.as_posix()}\"

end ExplicitLean.SimpTrace.SourceAppliedArguments
""",
        encoding="utf-8",
    )
    run_lean(split_source)
    split_raw = json.loads(split_trace.read_text(encoding="utf-8"))
    split_step = split_raw["locations"][0]["steps"][0]
    if "sourceValue" in split_step or "sourceValue?" in split_step or "args" in split_step:
        raise AssertionError(f"split source leaked validator-only application data: {split_step!r}")
    split_derivation = split_step.get("derivation", {})
    if split_derivation.get("source") != "simp-argument" or split_derivation.get("argId") != 0:
        raise AssertionError(f"split term was not bound to exact source argument h: {split_step!r}")
    if not split_step.get("side"):
        raise AssertionError(f"bare h should carry its explicit proof as side evidence: {split_step!r}")
    split_call = (
        f'simp_trace (discharger := assumption) only [h] =>trace "{split_trace.as_posix()}"'
    )
    split_text = split_source.read_text(encoding="utf-8")
    split_replay_source, _ = R.render_trace(
        {"schema": "simp-trace-v2", "site": {"sourceArgs": split_raw["sourceArgs"]},
         "locations": split_raw["locations"]},
        source_text=split_text,
    )
    if len(split_replay_source) != 1:
        raise AssertionError(f"expected one split-argument replay, got {split_replay_source!r}")
    split_replay_text = split_text.replace(split_call, split_replay_source[0])
    if split_replay_text == split_text:
        raise AssertionError("split-argument source call was not replaced for replay")
    split_replay = run_dir / "SplitLocalReplayed.lean"
    split_replay.write_text(split_replay_text, encoding="utf-8")
    run_lean(split_replay)

    # Dropping the persisted side proof must not leave an apparently valid
    # source application `h` that silently relies on the validator snapshot.
    split_without_side = copy.deepcopy(split_raw)
    split_without_side["locations"][0]["steps"][0].pop("side", None)
    try:
        R.render_trace(
            {"schema": "simp-trace-v2", "site": {"sourceArgs": split_without_side["sourceArgs"]},
             "locations": split_without_side["locations"]},
            source_text=split_text,
        )
    except R.RenderError:
        print("  bare h without persisted proof side: renderer rejected")
    else:
        raise AssertionError("renderer accepted bare h without its persisted proof side")

    # Even outside the trace renderer, ordinary Lean replay `[h]` cannot
    # discharge the explicit `P` proof binder.
    split_missing_proof = run_dir / "SplitLocalMissingProof.lean"
    split_missing_proof.write_text(
        """import ExplicitLean.ExplicitRw

namespace ExplicitLean.SimpTrace.SourceAppliedArguments

example (P : Prop) (hp : P) (f g : Nat → Nat)
    (h : P → ∀ n, f n = g n) (n : Nat) : f n = g n := by
  explicit_rw [h at [0, 1]]

end ExplicitLean.SimpTrace.SourceAppliedArguments
""",
        encoding="utf-8",
    )
    replay_failure = run_lean(split_missing_proof, success=False)
    if "unassigned argument" not in (replay_failure.stdout + replay_failure.stderr):
        raise AssertionError("ordinary explicit_rw [h] did not expose its missing proof binder")
    print("  explicit_rw [h] without recorded proof side: compile rejected")

    # The source-backed bare `if_neg` has no proof application in the source;
    # its only proof is the ordered side trace. Removing it must not result in
    # an apparently valid bare `if_neg` replay.
    missing_side_raw = copy.deepcopy(raw["BARE_IF_NEG"])
    missing_side_raw["locations"][0]["steps"][0].pop("side", None)
    try:
        missing_side_rendered, _ = R.render_trace(
            {"schema": "simp-trace-v2",
             "site": {"sourceArgs": missing_side_raw["sourceArgs"]},
             "locations": missing_side_raw["locations"]},
            source_text=recorded_source,
        )
    except R.RenderError:
        # The v2 validator checks the side/binder pairing before emitting
        # source, which is the strongest fail-closed outcome.
        print("  bare if_neg without its recorded proof side: renderer rejected")
    else:
        missing_side_source = replay_source.replace(
            rendered["BARE_IF_NEG"], missing_side_rendered[0]
        )
        missing_side = run_dir / "SourceAppliedArgumentsMissingIfNegProof.lean"
        missing_side.write_text(missing_side_source, encoding="utf-8")
        failure = run_lean(missing_side, success=False)
        diagnostic = failure.stdout + failure.stderr
        if "if_neg" not in diagnostic or "error" not in diagnostic:
            raise AssertionError(f"bare if_neg unexpectedly avoided its missing proof: {diagnostic}")
        print("  bare if_neg without source argument or recorded side proof: compile rejected")

    print("source-applied argument recorder/render/replay: passed")
    for name in MARKERS:
        print(f"  {name}: {rendered[name]}")


if __name__ == "__main__":
    main()
