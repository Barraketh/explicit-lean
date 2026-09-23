#!/usr/bin/env python3

from __future__ import annotations

import unittest

from render_simp_operations import UnsupportedOperation, render_trace


def name(*parts: str) -> dict[str, object]:
    return {"name": [["str", part] for part in parts]}


def rewrite_event(position: list[int]) -> dict[str, object]:
    return {
        "position": position,
        "phase": "post",
        "action": {
            "rewrite": {
                "rule": {
                    "origin": {"decl": name("Nat", "add_zero")},
                    "inverse": False,
                    "phase": "post",
                    "variant": 0,
                    "numExtraArgs": 0,
                },
                "premises": [],
            }
        },
    }


class RenderOperationsTest(unittest.TestCase):
    def test_declaration_rewrite(self) -> None:
        self.assertEqual(
            render_trace({"events": [rewrite_event([0, 1])]}),
            "explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 at [0, 1] with []]",
        )

    def test_true_terminal_is_term_free(self) -> None:
        self.assertEqual(
            render_trace({"events": [rewrite_event([])], "terminal": "trueIntro"}),
            "explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 at [] with []] then true_intro",
        )

    def test_local_premise_is_a_reference_not_a_term(self) -> None:
        event = rewrite_event([])
        event["action"]["rewrite"]["premises"] = [
            {
                "terminal": {"localAssumption": {"contextIndex": 4}},
                "operationCount": 0,
            }
        ]
        self.assertIn("with [assumption local_ref 4]", render_trace({"events": [event]}))

    def test_reductions(self) -> None:
        trace = {
            "events": [
                {"position": [1], "action": {"reduce": {"reduction": "beta"}}},
                {
                    "position": [],
                    "action": {
                        "reduce": {
                            "reduction": {
                                "delta": {"name": name("Demo", "f"), "strategy": "regular"}
                            }
                        }
                    },
                },
            ]
        }
        self.assertEqual(
            render_trace(trace),
            "explicit_rw_v2 [beta at [1], unfold Demo.f at []]",
        )

    def test_simproc_is_residual(self) -> None:
        with self.assertRaisesRegex(UnsupportedOperation, "known residual"):
            render_trace(
                {
                    "events": [
                        {"position": [], "action": {"simproc": {"declarations": ["demo"]}}}
                    ]
                }
            )

    def test_unknown_position_is_not_searched(self) -> None:
        event = rewrite_event([])
        event["position"] = None
        with self.assertRaisesRegex(UnsupportedOperation, "no exact raw child position"):
            render_trace({"events": [event]})


if __name__ == "__main__":
    unittest.main()
