#!/usr/bin/env python3
"""Check expression wire rejection independently of the Lean type checker."""
import json

from boundary_expr_codec import expr_is_constant, validate_expr_dag


def encoded(nodes, root=0):
    return json.dumps(["expr_dag_v1", nodes, root])


def main():
    assert expr_is_constant(encoded([["c", [["s", "True"]], []]]), "True")
    assert not expr_is_constant(encoded([["c", [["s", "False"]], []]]), "True")
    # Literal contents have no syntax/elaborator meaning in this encoding.
    source = encoded([["t", "by simp; @fun ⋯ ✝ ?m.123"]])
    validate_expr_dag(source)
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
    ]
    for source in invalid:
        try:
            validate_expr_dag(source)
        except RuntimeError:
            pass
        else:
            raise AssertionError(f"accepted invalid wire format: {source}")
    print("expression DAG: structure, terminal constants, literal data, and malformed input checks passed")


if __name__ == "__main__":
    main()
