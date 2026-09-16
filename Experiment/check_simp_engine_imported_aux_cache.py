#!/usr/bin/env python3
"""Independent wire controls for imported auxiliary-cache descriptors.

The Lean capture/replay fixture is supplied by the isolated validation runner.
This checker deliberately validates the descriptor before any replay and then
exercises mutations that must be rejected by the independent decoder.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import tempfile

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
import check_simp_engine_boundary_source as source
from boundary_expr_codec import (_checked_auxiliary_validator, lean_json_compress,
                                 validate_realization_payload)

ROOT = Path(__file__).resolve().parents[1]
MAX_AUX_BYTES = 16 * 1024 * 1024

PROBE = r'''
public meta import ExplicitLean.SimpEngine.Boundary
meta import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
meta import all Lean.Environment
meta import all Lean.Meta.Basic
open Lean Meta Elab Tactic ExplicitLean.SimpEngine.Boundary

namespace ImportedAuxFixture
open Lean Meta Elab Tactic
meta section

private unsafe def warmImportedCacheImpl : MetaM Name := do
  let saved ← Meta.saveState
  let some firstKey ← getUnfoldEqnFor? `List.lookmap.go (nonRec := true)
    | throwError "fixture could not obtain imported unfold theorem"
  let firstEnv ← getEnv
  unless firstEnv.isImportedConst `List.lookmap.go do
    throwError "fixture owner is not imported"
  saved.restore
  -- Re-enter through the normal API. The first call populated the shared
  -- imported realization map; this call applies that completed task to the
  -- restored caller branch without invoking a producer again.
  let some key ← getUnfoldEqnFor? `List.lookmap.go (nonRec := true)
    | throwError "fixture could not reactivate imported unfold theorem"
  unless key == firstKey do throwError "fixture unfold theorem key changed"
  let env ← getEnv
  let some ctx := env.importRealizationCtx?
    | throwError "fixture missing import context after warmup"
  let map ← ctx.realizeMapRef.get
  let some raw := map.find? (TypeName.typeName Environment.RealizeConstKey)
    | throwError "fixture missing realization map after warmup"
  let entries := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
  let some task := entries.find? { constName := key }
    | throwError "fixture missing completed imported cache key"
  unless ← IO.hasFinished task do throwError "fixture imported cache remains pending"
  let some result := task.get.get? Environment.RealizeConstResult
    | throwError "fixture imported cache result type"
  unless result.newConsts.private.any (·.constInfo.name == key) do
    throwError "fixture imported cache key is not a member"
  saved.restore
  unless !(← getEnv).containsOnBranch key do
    throwError "fixture warmup leaked imported declaration onto caller branch"
  IO.println s!"IMPORTED_AUX_SETUP owner=List.lookmap.go key={key} cached=true branchAbsent=true producer=false"
  pure key

@[implemented_by warmImportedCacheImpl]
private opaque warmImportedCache : MetaM Name

private unsafe def mutateImportedAuxImpl (env : Environment) (keyName : Name) (mode : String) : IO Unit := do
  let some ctx := env.importRealizationCtx? | throw <| IO.userError "fixture missing import context"
  let mut map ← ctx.realizeMapRef.get
  let some raw := map.find? (TypeName.typeName Environment.RealizeConstKey)
    | throw <| IO.userError "fixture missing realization map"
  let entries := unsafeCast (β := PHashMap Environment.RealizeConstKey (Task Dynamic)) raw
  let key : Environment.RealizeConstKey := { constName := keyName }
  let some task := entries.find? key | throw <| IO.userError "fixture missing imported unfold cache"
  unless ← IO.hasFinished task do throw <| IO.userError "fixture cache pending"
  let some result := task.get.get? Environment.RealizeConstResult
    | throw <| IO.userError "fixture result type"
  let some member := result.newConsts.private.find? (fun member => member.constInfo.constInfo.get.isTheorem)
    | throw <| IO.userError "fixture theorem member"
  let .thmInfo info := member.constInfo.constInfo.get
    | throw <| IO.userError "fixture theorem info"
  let view ← memberEnvironment env member
  let cache := (auxLemmasExt.getState view).lemmas
  let changed := if mode == "inject" then
      let auxKey : AuxLemmaKey := { type := info.type, isPrivate := isPrivateName info.name, defeq := false }
      auxLemmasExt.setState view { lemmas := cache.insert auxKey (info.name, info.levelParams) }
    else if mode == "wrong-type" then
      let auxKey : AuxLemmaKey := { type := mkNatLit 0, isPrivate := isPrivateName info.name, defeq := false }
      auxLemmasExt.setState view { lemmas := cache.insert auxKey (info.name, info.levelParams) }
    else if mode == "wrong-name" then
      let auxKey : AuxLemmaKey := { type := info.type, isPrivate := isPrivateName info.name, defeq := false }
      auxLemmasExt.setState view { lemmas := cache.insert auxKey (`Relation.MissingAux, info.levelParams) }
    else
      auxLemmasExt.setState view { lemmas := {} }
  let member := { member with exts? := some (.pure changed.base.private.extensions) }
  let mut privateMembers := []
  for old in result.newConsts.private do
    privateMembers := privateMembers.concat (if old.constInfo.name == member.constInfo.name then member else old)
  let result := { result with newConsts.private := privateMembers }
  ctx.realizeMapRef.set (map.insert (TypeName.typeName Environment.RealizeConstKey)
    (unsafeCast (entries.insert key (.pure (.mk result)))))
@[implemented_by mutateImportedAuxImpl]
private opaque mutateImportedAux (env : Environment) (keyName : Name) (mode : String) : IO Unit
end

open Lean Meta Elab Tactic in
elab "mutate_imported_aux " mode:str : tactic => withMainContext do
  let key ← warmImportedCache
  discard <| mutateImportedAux (← getEnv) key mode.getString
end ImportedAuxFixture
'''


def _find_v3(value: object) -> tuple[list, object] | None:
    if isinstance(value, dict):
        for child in value.values():
            found = _find_v3(child)
            if found is not None:
                return found
    elif isinstance(value, list):
        if (value and isinstance(value[0], str) and
                value[0] in {"boundary_realization_batch_v1", "boundary_realization_batch_v2"}):
            for node in value[10] if len(value) > 10 and isinstance(value[10], list) else []:
                descriptor = node[5] if value[0] == "boundary_realization_batch_v2" and isinstance(node, list) and len(node) == 6 else node[4] if isinstance(node, list) and len(node) == 5 else None
                if descriptor:
                    if isinstance(descriptor, list) and descriptor and descriptor[0] == "completed_realization_v3":
                        anchor = node[2] if value[0] == "boundary_realization_batch_v2" else node[1]
                        return value, anchor
        for child in value:
            found = _find_v3(child)
            if found is not None:
                return found
    return None


def _batch_anchor_layout_controls() -> dict[str, object]:
    """Check the distinct v1/v2 realization-node anchor positions."""
    descriptor = ["completed_realization_v3"]
    v1_anchor = [["s", "V1"]]
    v1_node = [[["s", "Owner"]], v1_anchor, "equation", [], descriptor]
    v1 = ["boundary_realization_batch_v1"] + [None] * 9 + [[v1_node]]
    v2_anchor = [["s", "V2"]]
    v2_node = ["equation", [["s", "Owner"]], v2_anchor, "equation", [], descriptor]
    v2 = ["boundary_realization_batch_v2"] + [None] * 9 + [[v2_node], [0]]
    for label, payload, expected in (("v1", v1, v1_anchor), ("v2", v2, v2_anchor)):
        found = _find_v3(payload)
        if found is None or found[1] != expected:
            raise RuntimeError(f"{label} anchor layout regression")
        descriptors = _descriptors(payload)
        if len(descriptors) != 1 or descriptors[0][1] != expected:
            raise RuntimeError(f"{label} descriptor anchor regression")
    return {"status": "passed", "v1Anchor": v1_anchor, "v2Anchor": v2_anchor}


def _canonical_order_controls() -> dict[str, object]:
    """Exercise Lean's raw-Unicode compressed ordering independently."""
    expr_z = json.dumps(["expr_struct_dag_v1", [["t", "z"]], 0],
                        separators=(",", ":"), ensure_ascii=False)
    expr_alpha = json.dumps(["expr_struct_dag_v1", [["t", "α"]], 0],
                            separators=(",", ":"), ensure_ascii=False)
    ascii_name = [["s", "ProofZ"]]
    unicode_name = [["s", "ProofAlpha"]]
    proofs = [
        ["theorem", ascii_name, [], expr_z, expr_z, []],
        ["theorem", unicode_name, [], expr_alpha, expr_alpha, []],
    ]
    def entry(expr: str, name: list[list[object]], index: int) -> list[object]:
        return [expr, False, False, name, [], index]
    canonical = [entry(expr_z, ascii_name, 0), entry(expr_alpha, unicode_name, 1)]
    reversed_entries = list(reversed(canonical))
    ascii_alpha = json.dumps([expr_alpha, False, False, unicode_name, []],
                             separators=(",", ":"), ensure_ascii=True)
    lean_alpha = lean_json_compress([expr_alpha, False, False, unicode_name, []])
    ascii_z = json.dumps([expr_z, False, False, ascii_name, []],
                         separators=(",", ":"), ensure_ascii=True)
    lean_z = lean_json_compress([expr_z, False, False, ascii_name, []])
    if not (ascii_alpha < ascii_z and lean_z < lean_alpha):
        raise RuntimeError("canonical-order control did not expose Unicode encoding mismatch")
    if (lean_json_compress(["\t"]) != '["\\u0009"]' or
            lean_json_compress(["\\t"]) != '["\\\\t"]'):
        raise RuntimeError("Lean control-character escaping mismatch")
    validator = _checked_auxiliary_validator(proofs, "Unicode canonical order", require_sorted=True)
    used = validator(canonical)
    try:
        validator(reversed_entries)
    except RuntimeError as error:
        if "not canonical" not in str(error):
            raise
        rejected = str(error)
    else:
        raise RuntimeError("reversed Unicode auxiliary entries were accepted")
    aux_bytes = len(lean_json_compress([canonical, proofs]).encode("utf-8"))
    return {"status": "passed", "used": sorted(used),
            "reversedRejected": rejected, "rawUnicodeBytes": aux_bytes}


def _load(path: Path) -> tuple[list, str]:
    value = json.loads(path.read_text())
    if isinstance(value, str):
        value = json.loads(value)
    if isinstance(value, dict) and "environmentActions" in value:
        for action in value["environmentActions"]:
            if action.get("kind") != "realize_groups":
                continue
            payload = json.loads(action["declaration"])
            found = _find_v3(payload)
            if found is not None:
                return found
    found = _find_v3(value)
    if found is None:
        raise RuntimeError("no completed_realization_v3 descriptor found")
    return found


def _descriptors(payload: list) -> list[tuple[list, list]]:
    result = []
    if payload[0] not in {"boundary_realization_batch_v1", "boundary_realization_batch_v2"}:
        raise RuntimeError("expected a realization batch payload")
    for node in payload[10]:
        if not isinstance(node, list):
            continue
        descriptor = node[5] if payload[0] == "boundary_realization_batch_v2" and len(node) == 6 else node[4] if len(node) == 5 else None
        if isinstance(descriptor, list) and descriptor and descriptor[0] == "completed_realization_v3":
            anchor = node[2] if payload[0] == "boundary_realization_batch_v2" else node[1]
            result.append((descriptor, anchor))
    if not result:
        raise RuntimeError("v3 descriptor has no nodes")
    return result


def _aux_fields(descriptor: list) -> list[list]:
    fields = []
    for entries in descriptor[4:6]:
        for member in entries:
            if not isinstance(member, list) or len(member) != 3:
                raise RuntimeError("invalid v3 member")
            metadata = member[1]
            if not isinstance(metadata, list) or len(metadata) != 5:
                raise RuntimeError("v3 member metadata is not explicit")
            aux = metadata[4]
            if not isinstance(aux, list) or len(aux) != 2:
                raise RuntimeError("invalid v3 auxiliary witness")
            if len(lean_json_compress(aux).encode("utf-8")) > MAX_AUX_BYTES:
                raise RuntimeError("auxiliary witness exceeds bound")
            fields.append(aux)
    return fields


def _first_aux_path(payload: list) -> tuple[int, int, int]:
    for node_index, node in enumerate(payload[10]):
        if not isinstance(node, list):
            continue
        descriptor = node[5] if payload[0] == "boundary_realization_batch_v2" and len(node) == 6 else node[4] if len(node) == 5 else None
        if not (isinstance(descriptor, list) and descriptor and descriptor[0] == "completed_realization_v3"):
            continue
        for side in (4, 5):
            for member_index, member in enumerate(descriptor[side]):
                if isinstance(member, list) and len(member) == 3:
                    metadata = member[1]
                    if (isinstance(metadata, list) and len(metadata) == 5 and
                            isinstance(metadata[4], list) and len(metadata[4]) == 2 and
                            metadata[4][0]):
                        return node_index, side, member_index
    raise RuntimeError("v3 descriptor has no nonempty auxiliary member")


def _relation_source() -> tuple[str, str]:
    original = '''module
public import Batteries.Data.List.Basic
public import Mathlib.Init
import Lean
public meta import ExplicitLean.SimpEngine.Boundary
import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
import all Lean.Environment
import all Lean.Meta.Basic
'''
    needle = "simp [List.lookmap.go, List.lookmap]"
    return (original + PROBE + '''
example {α : Type} (f : α → Option α) (acc : Array α) :
    List.lookmap.go f [] acc = acc.toListAppend (List.lookmap f []) := by
  simp [List.lookmap.go, List.lookmap]

'''), needle


def _run_fixture() -> dict:
    anchor_layout = _batch_anchor_layout_controls()
    canonical_order = _canonical_order_controls()
    raw, needle = _relation_source()
    target = raw.find(needle)
    if target < 0:
        raise RuntimeError("Relation consumer fixture target disappeared")
    work = Path(tempfile.mkdtemp(prefix="imported-aux-", dir=ROOT / ".lake/replay-fixes"))
    dylib = source.query_json_string(
        source.run(["lake", "query", "ExplicitLean:shared", "--json"]),
        "lake query ExplicitLean:shared",
    )
    records = []

    def compile_case(label: str, text: str, recording: bool, expected: str | None = None):
        path = materializer._copy_at_module_root(work / label, "Experiment/RelationAux.lean", text.encode())
        env, nonce = (protocol.recording_subprocess_environment() if recording
                      else protocol.replay_subprocess_environment())
        code, output, elapsed = materializer._run_command(
            ["lake", "env", "lean", f"--load-dynlib={dylib}", "-R", str(path.parent.parent), str(path)],
            300, env=env)
        (work / f"{label}.log").write_text(output)
        check = protocol.check_recording_abort_markers if recording else protocol.check_replay_abort_markers
        if expected is None:
            check(output, expected_nonce=nonce)
        else:
            try:
                check(output, expected_nonce=nonce)
            except RuntimeError as error:
                if expected not in str(error):
                    raise
            else:
                raise RuntimeError(f"{label}: expected {expected} rejection")
        records.append({"label": label, "recording": recording, "exit": code,
                        "elapsed": elapsed, "nonce": nonce, "expected": expected,
                        "source": str(path), "log": str(work / f"{label}.log")})
        if code != 0 and expected is None:
            raise RuntimeError(f"{label} failed: {output[-6000:]}")
        return protocol.parse_framed_json_lines(output, marker=materializer.ARTIFACT_MARKER,
            expected_nonce=nonce, label=label) if recording else []

    recorded_text = (raw[:target] +
        'mutate_imported_aux "inject"\n  simp_engine_boundary_record "imported-aux" [List.lookmap.go, List.lookmap]' +
        raw[target + len(needle):])
    reports = compile_case("record", recorded_text, True)
    if len(reports) != 1:
        raise RuntimeError(f"expected one recording artifact, got {len(reports)}")
    report = reports[0]
    protocol.validate_report(report, "imported-aux", "Experiment.RelationAux")
    (work / "recorded-artifact.json").write_text(
        json.dumps(report, indent=2) + "\n")
    actions = [a for a in report["environmentActions"] if a["kind"] == "realize_groups"]
    if len(actions) != 1:
        raise RuntimeError("recording did not produce one realization action")
    payload = json.loads(actions[0]["declaration"])
    if (not isinstance(payload, list) or payload[0] not in {
            "boundary_realization_batch_v1", "boundary_realization_batch_v2"} or
            len(payload) < 2 or payload[1] is not False):
        raise RuntimeError(
            "imported-cache fixture did not exercise a cached task with a caller-branch activation delta")
    found = _find_v3(payload)
    if found is None:
        raise RuntimeError("recording did not produce completed_realization_v3")
    payload, anchor = found
    aux_count = sum(bool(entries) for descriptor, _ in _descriptors(payload)
                    for entries, _ in _aux_fields(descriptor))
    if aux_count == 0:
        raise RuntimeError("recording v3 descriptor has empty auxiliary cache")
    replacement = source.preserve_original_call(
        source.format_report_variants([report], "  "), needle, "  ")
    replay_base = raw[:target] + 'mutate_imported_aux "inject"\n  ' + replacement + raw[target + len(needle):]
    compile_case("replay", replay_base, False)
    mutation_results = {}
    for mode, expected in (("erase", "boundary_realization_cached_descriptor_conflict"),
                           ("wrong-type", "boundary_local_aux_type_conflict"),
                           ("wrong-name", "boundary_local_aux_missing_checked_proof")):
        text = replay_base.replace('mutate_imported_aux "inject"', f'mutate_imported_aux "{mode}"', 1)
        compile_case(mode, text, False, expected)
        mutation_results[mode] = expected
    result = {"kind": "imported_auxiliary_cache_fixture", "schema": 1,
              "status": "passed", "recording": records[0], "replay": records[1:],
              "auxiliaryEntries": aux_count,
              "freshProcessImportedActivation": True,
              "activationMode": "completed_imported_cache",
              "mutationResults": mutation_results,
              "anchorLayoutChecks": anchor_layout,
              "canonicalOrderChecks": canonical_order,
              "separateRequiredChecks": [
                  "Experiment/check_simp_engine_local_cached_aux.py (not run by this fixture)",
                  "existing local cached auxiliary v1/v2 descriptor checks (not run by this fixture)"],
              "acceptedCampaignCoverage": False,
              "limitations": [
                  "this fixture does not claim fresh producer-side auxiliary reconstruction"]}
    (work / "report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(work / "report.json")
    return result


def run_fixture() -> None:
    (ROOT / ".lake/replay-fixes").mkdir(parents=True, exist_ok=True)
    _run_fixture()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path, nargs="?", help="artifact JSON or serialized batch payload")
    parser.add_argument("--fixture", action="store_true", help="run the authentic imported-cache fixture")
    args = parser.parse_args()
    if args.fixture:
        run_fixture()
        return
    if args.payload is None:
        parser.error("payload is required unless --fixture is used")
    payload, anchor = _load(args.payload)
    anchor_layout = _batch_anchor_layout_controls()
    canonical_order = _canonical_order_controls()
    validate_realization_payload(json.dumps(payload, separators=(",", ":")), anchor, "imported auxiliary")
    descriptors = _descriptors(payload)
    aux = []
    for descriptor, _ in descriptors:
        aux.extend(_aux_fields(descriptor))
    if not any(entries for entries, _ in aux):
        raise RuntimeError("v3 descriptor contains no imported auxiliary entry")
    node_index, side, member_index = _first_aux_path(payload)
    descriptor_path = lambda p: p[10][node_index][5] if p[0] == "boundary_realization_batch_v2" else p[10][node_index][4]
    member_path = lambda p: descriptor_path(p)[side][member_index]
    aux_entry = lambda p: member_path(p)[1][4][0][0]

    mutations: list[tuple[str, object]] = []
    mutations.append(("legacy-v2-smuggled", lambda p: descriptor_path(p).__setitem__(0, "completed_realization_v2")))
    mutations.append(("missing-aux-field", lambda p: member_path(p)[1].pop(4)))
    mutations.append(("missing-cache-entry", lambda p: member_path(p)[1][4][0].pop()))
    mutations.append(("foreign-proof", lambda p: member_path(p)[1][4][0][0].__setitem__(3, [["s", "Foreign.aux"]])))
    mutations.append(("proof-index", lambda p: aux_entry(p).__setitem__(5, 4294967295)))
    mutations.append(("flag-type", lambda p: aux_entry(p).__setitem__(1, "true")))
    rejected = []
    for label, mutate in mutations:
        candidate = copy.deepcopy(payload)
        mutate(candidate)
        try:
            validate_realization_payload(json.dumps(candidate, separators=(",", ":")), anchor, f"mutation {label}")
        except RuntimeError as error:
            rejected.append({"label": label, "error": str(error)})
        else:
            raise RuntimeError(f"mutation accepted: {label}")

    report = {
        "kind": "imported_auxiliary_cache_wire_controls",
        "schema": 1,
        "payload": str(args.payload.resolve()),
        "payloadSha256": hashlib.sha256(args.payload.read_bytes()).hexdigest(),
        "descriptorCount": len(descriptors),
        "auxiliaryMemberCount": len(aux),
        "rejectedMutations": rejected,
        "anchorLayoutChecks": anchor_layout,
        "canonicalOrderChecks": canonical_order,
        "runtimeReplayAndCacheInstallation": "requires isolated Lean fixture",
        "acceptedCampaignCoverage": False,
    }
    out = ROOT / ".lake/replay-fixes/imported-aux-cache-check.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
