# End-to-end replay summary

Generated 2026-09-16T23:30:03.
T1 `task/T1-trace-capture` at `1d8ba00b6216b1558aabf92e4bc8137410a0013d`; T2 `task/T2-explicit-rw` at `7ccb98b25d72c2e2ec0f25a96e18bc5e880c9cd3` (dirty).

| module | sites | replayed | unresolved | render_failed | compile_failed | mode | s |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Logic/IsEmpty/Basic.lean` | 17 | 15 | 0 | 0 | 2 | per_site | 40 |
| `Logic/Nontrivial/Defs.lean` | 1 | 1 | 0 | 0 | 0 | whole_module | 5 |
| `Logic/Function/Defs.lean` | 2 | 1 | 0 | 1 | 0 | whole_module | 5 |
| `Logic/ExistsUnique.lean` | 8 | 8 | 0 | 0 | 0 | whole_module | 5 |
| `Logic/Function/Basic.lean` | 23 | 9 | 1 | 8 | 5 | per_site | 44 |
| `Logic/Basic.lean` | 31 | 11 | 0 | 18 | 2 | per_site | 41 |
| **total** | **82** | **45** | **1** | **27** | **9** | | |

## Failures, per site

| module | site | line | status | attribution | detail |
| --- | --- | --- | --- | --- | --- |
| `Logic/IsEmpty/Basic.lean` | 16 | 119 | `compile_failed` | t1 | explicit_rw: step 2: lemma `eq_true leftTotal_empty` does not match the subterm at position [0, 1, 0, 1]. |
| `Logic/IsEmpty/Basic.lean` | 17 | 122 | `compile_failed` | t1 | explicit_rw: step 3: lemma `eq_true rightTotal_empty` does not match the subterm at position [0, 1, 1]. |
| `Logic/Function/Defs.lean` | 2 | 139 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Function/Basic.lean` | 2 | 316 | `render_failed:name_is_syntax` | t1 | rw.name 'if_neg fun h ↦ hb ⟨a, h⟩' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Function/Basic.lean` | 3 | 390 | `compile_failed` | t1 | unknown free variable `_fvar.8351.163` |
| `Logic/Function/Basic.lean` | 5 | 428 | `render_failed:name_is_syntax` | t1 | rw.name 'hh _' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Function/Basic.lean` | 6 | 528 | `render_failed:name_is_syntax` | t1 | rw.name 'dif_pos h' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Function/Basic.lean` | 7 | 664 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Function/Basic.lean` | 8 | 683 | `unresolved:discharged by rewriting to True, steps not recorded` | t1 | the recorder classified this call as unresolved: discharged by rewriting to True, steps not recorded |
| `Logic/Function/Basic.lean` | 10 | 796 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Function/Basic.lean` | 11 | 847 | `compile_failed` | t1 | explicit_rw: step 1: lemma `eq_true exists_apply_eq_apply` does not match the subterm at position []. |
| `Logic/Function/Basic.lean` | 14 | 895 | `compile_failed` | t1 | unknown free variable `_fvar.17365.51` |
| `Logic/Function/Basic.lean` | 15 | 923 | `compile_failed` | t1 | unknown free variable `_fvar.17774.26` |
| `Logic/Function/Basic.lean` | 16 | 928 | `render_failed:name_is_syntax` | t1 | rw.name 'if_neg ne' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Function/Basic.lean` | 17 | 934 | `render_failed:name_is_syntax` | t1 | rw.name 'comp_assoc g _ f' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Function/Basic.lean` | 18 | 975 | `render_failed:multiple_invocations` | harness | the call ran 4 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Function/Basic.lean` | 19 | 982 | `compile_failed` | t1 | explicit_rw: step 6: lemma `Function.curry_uncurry` does not match the subterm at position [1, 1, 0, 0, 1]. |
| `Logic/Basic.lean` | 4 | 428 | `render_failed:name_is_syntax` | t1 | rw.name '@xor_not_right a' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Basic.lean` | 5 | 430 | `render_failed:name_is_syntax` | t1 | rw.name '@xor_not_left _ b' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Basic.lean` | 6 | 497 | `compile_failed` | t1 | explicit_rw: step 1: lemma `eq_true cast_heq` does not match the subterm at position []. |
| `Logic/Basic.lean` | 7 | 508 | `render_failed:name_is_syntax` | t1 | rw.name 'heq_comm (a := a)' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Basic.lean` | 8 | 552 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 11 | 597 | `render_failed:name_is_syntax` | t1 | rw.name '@forall_eq _ p a' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Basic.lean` | 14 | 663 | `render_failed:name_is_syntax` | t1 | rw.name '@exists_comm (κ₁ _)' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Basic.lean` | 16 | 752 | `render_failed:name_is_syntax` | t1 | rw.name 'Subsingleton.elim _ i' is written syntax, not a name (spec: '<lemma or hyp name>') |
| `Logic/Basic.lean` | 18 | 899 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 19 | 917 | `compile_failed` | t1 | explicit_rw: step 1: `unfold Ne` was applied where the head constant is `Iff`. |
| `Logic/Basic.lean` | 20 | 962 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 21 | 973 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 22 | 987 | `render_failed:multiple_invocations` | harness | the call ran 4 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 23 | 990 | `render_failed:multiple_invocations` | harness | the call ran 4 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 24 | 1007 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 25 | 1011 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 26 | 1015 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 27 | 1019 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 28 | 1051 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |
| `Logic/Basic.lean` | 29 | 1055 | `render_failed:multiple_invocations` | harness | the call ran 2 times at this site with different steps (one per branch), and one tactic cannot carry a different step list per branch |

## Attribution of non-replayed sites

- `harness`: 16
- `t1`: 21

## Lines over 100 characters that could not be broken


- `Mathlib/Logic/Function/Basic.lean` site 11: 1 line(s)
