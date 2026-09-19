import Mathlib.Logic.Basic
import ExplicitLean.Grind.Metadata
import Lean.Elab.Tactic.Grind.Main
open Lean
open Lean.Meta
open Lean.Meta.Grind

reset_grind_attrs%
explicit_grind_eq_lhs xor_def
namespace T58
variable {α : Sort*}
variable (P : α → Prop)
explicit_grind_pattern Exists.choose_spec => P.choose
end T58

run_cmd do
  let compact (value : String) := value.replace "\n" "\\n"
  let env ← getEnv
  let s := grindExt.getState env
  for n in [``xor_def, ``Exists.choose_spec] do
    for t in s.ematch.find (.decl n) do
      IO.println s!"T58-METADATA|{n}|levels={compact (reprStr t.levelParams)}|proof={compact (reprStr t.proof)}|origin={compact (reprStr t.origin)}|kind={compact (reprStr t.kind)}|num={t.numParams}|patterns={compact (reprStr t.patterns)}|symbols={compact (reprStr t.symbols)}|cnstrs={compact (reprStr t.cnstrs)}|min={t.minIndexable}"
