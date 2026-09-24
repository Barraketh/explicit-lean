#!/usr/bin/env python3

from __future__ import annotations

import unittest

from render_simp_operations import (
    UnsupportedOperation,
    render_observation,
    render_repeated_goal_traces,
    render_trace,
)


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
            "explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 at [0, 1] with []]",
        )

    def test_private_declaration_uses_its_source_scope_name(self) -> None:
        event = rewrite_event([])
        event["action"]["rewrite"]["rule"]["origin"] = {
            "decl": {"name": "_private._stdin.0.Example.hidden"}
        }
        self.assertIn(
            "rule Example.hidden variant",
            render_trace({"events": [event]}),
        )

    def test_true_terminal_is_term_free(self) -> None:
        self.assertEqual(
            render_trace({"events": [rewrite_event([])], "terminal": "trueIntro"}),
            "explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 at [] with []] then true_intro",
        )

    def test_nontrivial_true_without_operations_is_residual(self) -> None:
        with self.assertRaisesRegex(
            UnsupportedOperation, "without a recorded operation"
        ):
            render_trace({"events": [], "terminal": "trueIntro"})
        self.assertEqual(
            render_trace({
                "initialIsTrue": True, "events": [], "terminal": "trueIntro"
            }),
            "explicit_rw_v2 [] then true_intro",
        )

    def test_repeated_goal_traces_preserve_invocation_order(self) -> None:
        first = {"events": [rewrite_event([0])], "terminal": "open"}
        second = {"events": [rewrite_event([1])], "terminal": "trueIntro"}
        self.assertEqual(
            render_repeated_goal_traces([first, second]),
            ["explicit_rw_v2_goals [explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 at [0] with []], explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 at [1] with []] then true_intro]"],
        )

    def test_repeated_located_trace_is_one_closed_sequence_per_goal(self) -> None:
        located = {
            "subjects": [
                {"subject": {"namedLocal": {"source": "h"}},
                 "trace": {"events": [rewrite_event([])]}},
                {"subject": "target",
                 "trace": {"events": [rewrite_event([0, 1])]}}
            ]
        }
        self.assertEqual(
            render_repeated_goal_traces([located]),
            ["explicit_rw_v2_goals [explicit_rw_v2_sequence ["
             "explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 "
             "at [] with []] at h, explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 "
             "phase post fwd extra 0 at [0, 1] with []]]]"],
        )

    def test_raw_nat_literal_folding_has_an_exact_reduction(self) -> None:
        trace = {
            "events": [{
                "position": [0, 1],
                "action": {"reduce": {"reduction": "foldRawNatLit"}},
            }]
        }
        self.assertEqual(
            render_trace(trace), "explicit_rw_v2 [fold_nat_lit at [0, 1]]"
        )

    def test_forall_congruence_keeps_domain_and_bound_body_streams_nested(self) -> None:
        domain = rewrite_event([])
        body = rewrite_event([])
        body["action"]["rewrite"]["rule"]["origin"] = {
            "bound": {"ordinal": 0}
        }
        trace = {
            "events": [{
                "position": [0, 1],
                "action": {"forallCongruence": {
                    "domain": [domain],
                    "body": [body],
                }},
            }]
        }
        rendered = render_trace(trace)
        self.assertIn("forall_congr at [0, 1] domain [rule _root_.Nat.add_zero", rendered)
        self.assertIn("body [bound 0", rendered)

    def test_named_congruence_propagates_its_binder_scope_recursively(self) -> None:
        body = rewrite_event([])
        body["action"]["rewrite"]["rule"]["origin"] = {
            "bound": {"ordinal": 1}
        }
        trace = {
            "events": [{
                "position": [],
                "action": {"congruence": {
                    "theoremName": name("forall_congr"),
                    "children": [{
                        "argumentIndex": 0,
                        "binderCount": 2,
                        "events": [{
                            "position": [],
                            "action": {"autoCongruence": {
                                "children": [{"argumentIndex": 0, "events": [body]}]
                            }},
                        }],
                    }],
                    "premises": [],
                }},
            }]
        }
        rendered = render_trace(trace)
        self.assertIn("local __explicit_rw_v2_bound_1", rendered)

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

    def test_source_syntax_ordinary_tactic_block_is_visible_lean(self) -> None:
        event = rewrite_event([0, 1])
        event["action"]["rewrite"]["rule"]["origin"] = {
            "syntax": {"source": "(by omega : n + 0 = n)"}
        }
        self.assertIn(
            "source_rule lean_term((by omega : n + 0 = n))",
            render_trace({"events": [event]}),
        )

    def test_source_syntax_simp_family_tactic_is_rejected(self) -> None:
        event = rewrite_event([0, 1])
        event["action"]["rewrite"]["rule"]["origin"] = {
            "syntax": {"source": "(by simp : n + 0 = n)"}
        }
        with self.assertRaisesRegex(
            UnsupportedOperation, "forbidden simp-family tactic.*simp"
        ):
            render_trace({"events": [event]})

    def test_local_premise_is_a_reference_not_a_term(self) -> None:
        event = rewrite_event([])
        event["action"]["rewrite"]["premises"] = [
            {
                "terminal": {"localAssumption": {"contextIndex": 4}},
                "events": [],
            }
        ]
        self.assertIn("with [assumption local_ref 4]", render_trace({"events": [event]}))

    def test_congruence_bound_premise_uses_structural_ordinal(self) -> None:
        event = rewrite_event([])
        event["action"]["rewrite"]["premises"] = [
            {
                "terminal": {"boundAssumption": {"ordinal": 0}},
                "events": [],
            }
        ]
        self.assertIn("with [assumption bound 0]", render_trace({"events": [event]}))

    def test_equation_hypothesis_premise_is_an_exact_closed_operation(self) -> None:
        event = rewrite_event([])
        event["action"]["rewrite"]["premises"] = [
            {"terminal": "equationHypothesis", "events": []}
        ]
        self.assertIn(
            "with [equation_hypothesis]", render_trace({"events": [event]})
        )

    def test_single_hypothesis_location_uses_exact_context_identity(self) -> None:
        observation = {
            "subjects": [{
                "subject": {"namedLocal": {"source": "h"}},
                "trace": {"events": [rewrite_event([0, 1])]},
            }]
        }
        self.assertEqual(
            render_observation(observation),
            ["explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 "
             "at [0, 1] with []] at h"],
        )

    def test_named_locations_replay_in_recorded_order(self) -> None:
        observation = {
            "subjects": [
                {"subject": {"namedLocal": {"source": "h₁"}},
                 "trace": {"events": [rewrite_event([])]}},
                {"subject": {"namedLocal": {"source": "h₂"}},
                 "trace": {"events": [rewrite_event([0, 1])]}},
                {"subject": "target", "trace": {"events": []}},
            ]
        }
        self.assertEqual(
            render_observation(observation),
            [
                "explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 "
                "at [] with []] at h₁",
                "explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 "
                "at [0, 1] with []] at h₂",
            ],
        )

    def test_wildcard_locations_replay_in_recorded_order(self) -> None:
        self.assertEqual(
            render_observation({
                "subjects": [
                    {"subject": {"local": {"contextIndex": 2}}, "trace": {"events": []}},
                    {"subject": "target", "trace": {"events": []}},
                ]
            }),
            ["skip"],
        )

    def test_unchanged_location_is_skipped_but_closing_terminal_is_not(self) -> None:
        self.assertEqual(
            render_observation({
                "subjects": [
                    {"subject": {"namedLocal": {"source": "h"}},
                     "trace": {"events": [], "terminal": "falseElim"}},
                ]
            }),
            ["explicit_rw_v2 [] at h then false_elim"],
        )

    def test_local_false_closes_the_goal_from_the_same_subject(self) -> None:
        observation = {
            "subjects": [{
                "subject": {"namedLocal": {"source": "h"}},
                "trace": {"events": [rewrite_event([])], "terminal": "falseElim"},
            }]
        }
        self.assertEqual(
            render_observation(observation),
            ["explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 "
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

    def test_cache_reuse_names_its_exact_producing_operations(self) -> None:
        cached = rewrite_event([])
        trace = {
            "events": [{
                "position": [0, 1],
                "phase": "post",
                "action": {"cacheReuse": {"events": [cached]}},
            }]
        }
        self.assertEqual(
            render_trace(trace),
            "explicit_rw_v2 [cached [rule _root_.Nat.add_zero variant 0 phase post fwd "
            "extra 0 at [] with [] ] at [0, 1]]",
        )

    def test_named_congruence_indexes_its_recursive_child(self) -> None:
        trace = {
            "events": [{
                "position": [0, 1],
                "phase": "post",
                "action": {"congruence": {
                    "theoremName": name("Demo", "congr"),
                    "children": [{
                        "argumentIndex": 3,
                        "binderCount": 1,
                        "events": [rewrite_event([0, 1])],
                    }],
                    "premises": [],
                }},
            }]
        }
        self.assertEqual(
            render_trace(trace),
            "explicit_rw_v2 [congr_rule _root_.Demo.congr at [0, 1] with [arg 3 intro 1 ; "
            "explicit_rw_v2 [rule _root_.Nat.add_zero variant 0 phase post fwd extra 0 "
            "at [0, 1] with []] then rfl]]",
        )

    def test_automatic_congruence_keeps_child_operations_relative(self) -> None:
        trace = {
            "events": [{
                "position": [0, 1],
                "phase": "post",
                "action": {"autoCongruence": {"children": [{
                    "argumentIndex": 2,
                    "events": [rewrite_event([])],
                }]}},
            }]
        }
        self.assertEqual(
            render_trace(trace),
            "explicit_rw_v2 [auto_congr at [0, 1] with [arg 2 [rule "
            "_root_.Nat.add_zero variant 0 phase post fwd extra 0 at [] with []]]]",
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
                                "delta": {
                                    "name": name("Demo", "f"),
                                    "strategy": "requestedOrdinary",
                                }
                            }
                        }
                    },
                },
            ]
        }
        self.assertEqual(
            render_trace(trace),
            "explicit_rw_v2 [instantiate at [0], beta at [1], unfold _root_.Demo.f "
            "strategy requestedOrdinary at []]",
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

    def test_local_definition_reduction_is_explicit(self) -> None:
        self.assertEqual(
            render_trace({
                "events": [{
                    "position": [0, 1],
                    "action": {"reduce": {"reduction": {
                        "localDef": {"contextIndex": 3, "reason": "requested"}
                    }}},
                }]
            }),
            "explicit_rw_v2 [zeta_local local_ref 3 requested at [0, 1]]",
        )

    def test_unknown_position_is_not_searched(self) -> None:
        event = rewrite_event([])
        event["position"] = None
        with self.assertRaisesRegex(UnsupportedOperation, "no exact raw child position"):
            render_trace({"events": [event]})


if __name__ == "__main__":
    unittest.main()
