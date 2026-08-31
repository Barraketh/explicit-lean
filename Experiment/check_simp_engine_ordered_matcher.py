#!/usr/bin/env python3
"""Cold/cached exact-order matcher replay; closed declaration operations only."""
from pathlib import Path
import copy
import hashlib
import json
import tempfile

import boundary_materialize_shard as materializer
import boundary_protocol as protocol
from boundary_expr_codec import validate_matcher_payload

ROOT = Path(__file__).resolve().parents[1]
HEADER = '''module
import Mathlib.Init
import Batteries.Data.List.Basic
public meta import ExplicitLean.SimpEngine.Boundary.MatcherCodec
import all ExplicitLean.SimpEngine.Boundary.RealizationCodec
public meta import Lean.Meta.Match.MatchEqs
public meta import Lean.Meta.Constructions.SparseCasesOn
meta import all Lean.Meta.Constructions.SparseCasesOn
open Lean Meta Elab ExplicitLean.SimpEngine.Boundary
run_meta do
  let anchor := `List.modifyLast.go.match_1
  let before ← getEnv
  let splitter := mkPrivateName before anchor ++ `splitter
  BODY
  let some nonce ← IO.getEnv "SIMP_ENGINE_BOUNDARY_RUN_NONCE" | throwError "missing nonce"
  IO.println s!"\\nORDERED_MATCHER_OK {nonce}"
'''


def main():
    parent = ROOT / ".lake/single-child"
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="ordered-", dir=parent))
    print(work, flush=True)
    records = []
    payload = work / "payload.json"
    descriptor = work / "descriptor.json"
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    inputs = [Path(__file__), ROOT / "Experiment/boundary_expr_codec.py",
              ROOT / ".lake/build/lib/libexplicitLean_ExplicitLean.dylib"]
    inputs += list((ROOT / "ExplicitLean/SimpEngine/Boundary").glob("*.lean"))
    inputs += [ROOT / "ExplicitLean/SimpEngine/Boundary.lean"]
    inputs += [p for p in (ROOT / ".lake/build/lib/lean/ExplicitLean/SimpEngine").rglob("*")
               if p.is_file() and p.suffix in {".olean", ".private", ".server", ".ir"}]
    before = {str(p.resolve()): sha(p) for p in inputs}

    def run(label, body, expected=None):
        text = HEADER.replace("  BODY", "  " + body.replace("\n", "\n  "))
        path = materializer._copy_at_module_root(work / label, "Experiment/OrderedMatcher.lean", text.encode())
        env, nonce = protocol.replay_subprocess_environment()
        code, output, elapsed = materializer._run_command(["lake", "env", "lean",
            f"--load-dynlib={ROOT / '.lake/build/lib/libexplicitLean_ExplicitLean.dylib'}",
            "-R", str(path.parent.parent), str(path)], 120, env=env)
        log = work / f"{label}.log"
        log.write_text(output)
        if expected is None:
            assert code == 0 and f"ORDERED_MATCHER_OK {nonce}" in output, output[-4000:]
        else:
            assert code != 0 and expected in output, output[-4000:]
        records.append({"label": label, "source": str(path), "log": str(log), "nonce": nonce,
                        "compilerExit": code, "expectedFailure": expected, "elapsedSeconds": elapsed})
        print(label + ": passed", flush=True)

    run("scalar-roundtrip", '''let metadata : MData := { entries := [
  (`borrowed, .ofBool true), (`text, .ofString "literal"), (`name, .ofName (`a ++ Name.num `b 3)),
  (`nat, .ofNat 99), (`int, .ofInt (-7)), (`borrowed, .ofBool false)] }
let left := Expr.lam `left (mkConst ``Nat) (.bvar 0) .default
let right := Expr.lam `right (mkConst ``Nat) (.bvar 0) .implicit
let original := Expr.mdata metadata (.app left right)
let source ← encodeBoundaryStructExpr original
let decoded ← decodeBoundaryStructExpr source
unless Expr.equal original decoded do throwError "scalar structural roundtrip"
unless source == (← encodeBoundaryStructExpr decoded) do throwError "structural encoding not canonical"
unless !Expr.equal left right do throwError "fixture binder distinction"
let rejected ← try
  discard <| encodeBoundaryStructExpr (.mdata { entries := [(`syntax, .ofSyntax .missing)] } left)
  pure false
catch error => pure ((← error.toMessageData.toString).contains "syntax_metadata_unsupported")
unless rejected do throwError "unsupported syntax metadata accepted"''')
    run("capture", f'''let checked := before.constants.foldStage2 (fun s n _ => s.insert n) ({{}} : NameSet)
let eqns ← Match.getEquationsFor anchor
let env ← getEnv
let sparse := env.constants.foldStage2 (s := #[]) fun names name _ =>
  if !checked.contains name && (getSparseCasesOnInfoCore env name).isSome then names.push name else names
unless sparse.size == 1 do throwError "fixture helper count"
let source ← encodeBoundaryMatcher before checked anchor eqns #[] #[] sparse
IO.FS.writeFile {json.dumps(str(payload))} source
let descriptor ← completedCacheDescriptor env anchor splitter (structural := true)
IO.FS.writeFile {json.dumps(str(descriptor))} descriptor.compress''')
    raw = payload.read_text()
    value = json.loads(raw)
    assert value[0] == "boundary_matcher_bundle_v3"
    validate_matcher_payload(raw, value[1])
    assert value[19] == [value[3][0][0], value[3][0][1], value[15][0][0],
                         value[3][0][2], value[3][1]]

    def replay(source, cached=False):
        prefix = f"let source := {json.dumps(source)}\n"
        if cached:
            prefix += f"executeBoundaryMatcher anchor {json.dumps(raw)}\nsetEnv before\n"
        return prefix + f'''executeBoundaryMatcher anchor source
let expected ← ofExcept <| Json.parse (← IO.FS.readFile {json.dumps(str(descriptor))})
unless (← completedCacheDescriptor (← getEnv) anchor splitter (structural := true)) == expected do
  throwError "ORDERED_MATCHER_DESCRIPTOR_CONFLICT"'''

    run("fresh", replay(raw))
    run("cached", replay(raw, cached=True))
    legacy = ["boundary_matcher_bundle_v2", *value[1:19]]
    run("legacy-order-retained", replay(json.dumps(legacy)), "ORDERED_MATCHER_DESCRIPTOR_CONFLICT")
    mutations = []
    for label in ["helper-first", "missing-helper", "duplicate-member", "corrupt-sparse", "forward-dependency"]:
        mutated = copy.deepcopy(value)
        if label == "helper-first":
            mutated[19] = [mutated[15][0][0], *mutated[3][0], mutated[3][1]]
            expected = "ORDERED_MATCHER_DESCRIPTOR_CONFLICT"
        elif label == "missing-helper":
            mutated[15] = []
            expected = "boundary_matcher_declaration_order"
        elif label == "duplicate-member":
            mutated[19][2] = mutated[19][0]
            expected = "anonymous or duplicate name"
        elif label == "corrupt-sparse":
            mutated[17] = []
            expected = "boundary_matcher_sparse_cache_conflict"
        else:
            mutated[19] = [*mutated[3][0], mutated[15][0][0], mutated[3][1]]
            expected = "expression constant is unavailable without generation"
        source = json.dumps(mutated, separators=(",", ":"))
        run(label, replay(source), expected)
        mutations.append(source)
        if label == "helper-first":
            run("cached-wrong-order", replay(source, cached=True), "boundary_matcher_realized_order_conflict")
    for label in ["metadata-deleted", "metadata-changed", "metadata-key-changed", "metadata-unknown-kind"]:
        mutated = copy.deepcopy(value)
        helper = json.loads(mutated[15][0][1])
        definition = json.loads(helper[2])
        expression = json.loads(definition[7])
        nodes = expression[1]
        index = next(i for i, node in enumerate(nodes) if node[0] == "m")
        assert nodes[index][1] == [[[["s", "borrowed"]], ["bool", True]]]
        if label == "metadata-deleted":
            nodes[index] = copy.deepcopy(nodes[nodes[index][2]])
        elif label == "metadata-changed":
            nodes[index][1][0][1][1] = False
        elif label == "metadata-key-changed":
            nodes[index][1][0][0] = [["s", "unknownKey"]]
        else:
            nodes[index][1][0][1][0] = "syntax"
        definition[7] = json.dumps(expression, separators=(",", ":"))
        helper[2] = json.dumps(definition, separators=(",", ":"))
        mutated[15][0][1] = json.dumps(helper, separators=(",", ":"))
        source = json.dumps(mutated, separators=(",", ":"))
        run(label, replay(source, cached=True), "unsupported structural metadata value" if label == "metadata-unknown-kind"
            else "boundary_definition_existing_value_conflict")
    after = {str(p.resolve()): sha(p) for p in inputs}
    assert before == after
    report = {"kind": "ordered-matcher-controls", "acceptedCoverage": False,
              "records": records, "inputsBefore": before, "inputsAfter": after,
              "hashes": {str(p): sha(p) for p in work.rglob("*") if p.is_file()}}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(work / "report.json", flush=True)


if __name__ == "__main__":
    main()
