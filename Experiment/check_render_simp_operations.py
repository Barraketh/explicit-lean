#!/usr/bin/env python3

from __future__ import annotations

import unittest

from render_simp_operations import UnsupportedOperation, render_observation, render_trace


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

    def test_source_syntax_operand_is_rendered_as_ordinary_lean(self) -> None:
        event = rewrite_event([0, 1])
        event["action"]["rewrite"]["rule"]["origin"] = {
            "syntax": {"source": "localRule n"}
        }
        self.assertEqual(
            render_trace({"events": [event]}),
            "explicit_rw_v2 [source_rule lean_term(localRule n) variant 0 phase post "
            "fwd extra 0 at [0, 1] with []]",
        )

    def test_local_premise_is_a_reference_not_a_term(self) -> None:
        event = rewrite_event([])
        event["action"]["rewrite"]["premises"] = [
            {
                "terminal": {"localAssumption": {"contextIndex": 4}},
                "events": [],
            }
        ]
        self.assertIn("with [assumption local_ref 4]", render_trace({"events": [event]}))

    def test_single_hypothesis_location_uses_exact_context_identity(self) -> None:
        observation = {
            "subjects": [{
                "subject": {"namedLocal": {"source": "h"}},
                "trace": {"events": [rewrite_event([0, 1])]},
            }]
        }
        self.assertEqual(
            render_observation(observation),
            ["explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 "
             "at [0, 1] with []] at h"],
        )

    def test_multiple_locations_remain_a_structured_residual(self) -> None:
        with self.assertRaisesRegex(UnsupportedOperation, "simultaneous"):
            render_observation({
                "subjects": [
                    {"subject": "target", "trace": {"events": []}},
                    {"subject": "target", "trace": {"events": []}},
                ]
            })

    def test_local_false_closes_the_goal_from_the_same_subject(self) -> None:
        observation = {
            "subjects": [{
                "subject": {"namedLocal": {"source": "h"}},
                "trace": {"events": [rewrite_event([])], "terminal": "falseElim"},
            }]
        }
        self.assertEqual(
            render_observation(observation),
            ["explicit_rw_v2 [rule Nat.add_zero variant 0 phase post fwd extra 0 "
             "at [] with []] at h then false_elim"],
        )

    def test_nested_premise_operations_are_recursive(self) -> None:
        event = rewrite_event([])
        event["action"]["rewrite"]["premises"] = [
            {
                "terminal": "dischargeRfl",
                "events": [
                    {"position": [0, 1], "action": {"reduce": {"reduction": "beta"}}}
                ],
            }
        ]
        self.assertIn(
            "with [explicit_rw_v2 [beta at [0, 1]] then rfl]",
            render_trace({"events": [event]}),
        )

    def test_reductions(self) -> None:
        trace = {
            "events": [
                {"position": [0], "action": {"reduce": {"reduction": "instantiateMVars"}}},
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
            "explicit_rw_v2 [instantiate at [0], beta at [1], unfold Demo.f at []]",
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
