#!/usr/bin/env python3
"""Check expression wire rejection independently of the Lean type checker."""
import json

from boundary_expr_codec import (
    expr_is_constant, validate_expr_dag, validate_theorem_payload,
    validate_congruence_payload, validate_equation_payload,
)
from boundary_protocol import reject_forbidden_generated_text


def encoded(nodes, root=0):
    return json.dumps(["expr_dag_v1", nodes, root])


def main():
    assert expr_is_constant(encoded([["c", [["s", "True"]], []]]), "True")
    assert not expr_is_constant(encoded([["c", [["s", "False"]], []]]), "True")
    # Literal contents have no syntax/elaborator meaning in this encoding.
    source = encoded([["t", "by simp; @fun ⋯ ✝ ?m.123 sorryAx sorry admit"]])
    validate_expr_dag(source)
    reject_forbidden_generated_text({"input": source}, "literal contents")
    assert not expr_is_constant(source, "True")
    validate_expr_dag(encoded([
        ["s", ["s", ["max", ["z"], ["p", [["s", "u.v"], ["n", 1]]]]]],
        ["b", 0], ["l", [["s", "x"]], 3, 0, 1], ["a", 2, 1],
        ["e", [], 0, 1, 3, False], ["p", [["s", "Prod"]], 0, 4],
    ], 5))
    invalid = [
        "by simp", "null", "{}", '["expr_dag_v2",[],0]',
        encoded([]), encoded([["n", 1]], True), encoded([["n", True]]),
        encoded([["n", -1]]), encoded([["n", 1.0]]),
        encoded([["a", 0, 0]]), encoded([["a", 1, 1]]),
        encoded([["mvar", 0]]), encoded([["tactic", "simp"]]),
        encoded([["s", ["mvar", 0]]]), encoded([["s", ["max", ["z"]]]]),
        encoded([["c", [["n", "1"]], []]]), encoded([["c", [], [None]]]),
        encoded([["l", [], 4, 0, 0]]), encoded([["e", [], 0, 0, 0, 1]]),
        encoded([["b", 0, "extra"]]), encoded([["unknown"]]),
        encoded([["c", [["s", "sorryAx"]], []]]),
    ]
    for source in invalid:
        try:
            validate_expr_dag(source)
        except RuntimeError:
            pass
        else:
            raise AssertionError(f"accepted invalid wire format: {source}")
    name = [["s", "a.b"], ["n", 2]]
    typ = encoded([["c", [["s", "True"]], []]])
    proof = encoded([["c", [["s", "True"], ["s", "intro"]], []]])
    declaration = ["boundary_theorem_dag_v1", name, [], [], typ, proof]
    validate_theorem_payload(json.dumps(declaration), name)
    invalid_declarations = [
        declaration[:-1],
        [*declaration[:3], [name, name], *declaration[4:]],
        [*declaration[:4], "by simp", proof],
        [*declaration[:5], encoded([["c", [["s", "sorryAx"]], []]])],
    ]
    for payload in invalid_declarations:
        try:
            validate_theorem_payload(json.dumps(payload), name)
        except RuntimeError:
            pass
        else:
            raise AssertionError("accepted invalid theorem wire format")
    try:
        validate_theorem_payload(json.dumps(declaration), [["s", "foreign"]])
    except RuntimeError:
        pass
    else:
        raise AssertionError("accepted foreign theorem name")
    anchor = [["s", "a.b"], ["n", 2]]
    name = [*anchor, ["s", "congr_simp"]]
    declaration[1] = name
    congruence = ["boundary_congruence_v1", anchor, json.dumps(declaration),
                  ["fixed", "fixedNoParam", "eq", "cast", "heq", "subsingletonInst"]]
    validate_congruence_payload(json.dumps(congruence), name)
    reject_forbidden_generated_text({"declaration": json.dumps(congruence)}, "congruence")
    for bad_number in (True, 1.0):
        numbered_anchor = [["s", "Probe"], ["n", 1]]
        numbered_name = [*numbered_anchor, ["s", "congr_simp"]]
        declaration[1] = numbered_name
        numbered_payload = json.dumps([
            "boundary_congruence_v1", numbered_anchor, json.dumps(declaration), []])
        try:
            validate_congruence_payload(numbered_payload,
                [["s", "Probe"], ["n", bad_number], ["s", "congr_simp"]])
        except RuntimeError:
            pass
        else:
            raise AssertionError("accepted boolean/float external name component")
    invalid_congruences = [
        congruence[:-1],
        [*congruence[:3], ["synthesize"]],
        [congruence[0], [["s", "other"]], *congruence[2:]],
        [*congruence[:2], "[]", []],
    ]
    for payload in invalid_congruences:
        try:
            validate_congruence_payload(json.dumps(payload), name)
        except RuntimeError:
            pass
        else:
            raise AssertionError("accepted invalid congruence wire format")
    for suffix in ("hcongr_1_0", "hcongr__1", "hcongr_1_", "hcongr_1__0"):
        declaration[1] = [*anchor, ["s", suffix]]
        value = json.dumps(["boundary_congruence_v1", anchor, json.dumps(declaration), []])
        try:
            validate_congruence_payload(value, declaration[1])
        except RuntimeError:
            if suffix == "hcongr_1_0":
                raise
        else:
            if suffix != "hcongr_1_0":
                raise AssertionError("accepted malformed congruence numeric suffix")
    declaration[1] = [*anchor, ["s", "eq_1"]]
    equation = ["boundary_equation_v1", anchor, json.dumps(declaration), True, False, True]
    validate_equation_payload(json.dumps(equation), declaration[1])
    reject_forbidden_generated_text({"declaration": json.dumps(equation)}, "equation")
    for flags in ([1, False, True], [True, None, True], [True, False]):
        try:
            validate_equation_payload(json.dumps([*equation[:3], *flags]), declaration[1])
        except RuntimeError:
            pass
        else:
            raise AssertionError("accepted malformed equation metadata")
    print("expression DAG: structure, terminal constants, literal data, and malformed input checks passed")


if __name__ == "__main__":
    main()
