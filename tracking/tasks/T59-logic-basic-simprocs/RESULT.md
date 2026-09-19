# T59 result

Status: blocked / fail-closed. No product replacement was integrated.

A proposed replacement returned the swapped Eq/Iff expression with
`Simp.Step.continue`, allowing the enclosing traversal to simplify operands
without a nested engine call. Initial direct examples passed, but independent
review found the differential accidentally invoked stock Lean through `lake
env` after constructing a replacement search path. Correct direct pinned-Lean
testing exposed a real semantic/termination mismatch.

With the proposed overlay enabled, compiling the required dependent
`Mathlib.Logic.Function.Basic` against translated `Mathlib.Logic.Basic` failed
at `eq_update_self_iff` (`by simp [eqComm]`) with maximum recursion depth. The
proposal cannot reproduce stock's lexical `withoutTheorems` exclusions, so the
swap is revisited indefinitely.

The two `eqComm`/`iffComm` overlay entries and helper were removed and withheld.
The T59 task branch retains a 17-case fixture and exact failure experiments for
future work, but none is merged as acceptance evidence. Current main therefore
keeps the two original dormant Meta `simp symmExpr` bodies visibly unresolved.

Required next design: preserve the exclusion context and continuation state
without invoking/copying Simp, then pass the direct differential, the
`Function.Basic` dependent probe, strict certification and no-new-axiom gate.
Do not reinstate the continuation-only overlay.
