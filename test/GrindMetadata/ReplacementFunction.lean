import Mathlib.Logic.Function.Basic
import ExplicitLean.Grind.Metadata
import Lean.Elab.Tactic.Grind.Main
open Lean
open Lean.Meta
open Lean.Meta.Grind

reset_grind_attrs%
explicit_grind_def Function.update

run_cmd do
  let compact (value : String) := value.replace "\n" "\\n"
  let s := grindExt.getState (← getEnv)
  for t in s.ematch.find (.decl ``Function.update.eq_1) do
    IO.println s!"T60-METADATA|{compact (reprStr t.levelParams)}|proof={compact (reprStr t.proof)}|origin={compact (reprStr t.origin)}|kind={compact (reprStr t.kind)}|num={t.numParams}|patterns={compact (reprStr t.patterns)}|symbols={compact (reprStr t.symbols)}|cnstrs={compact (reprStr t.cnstrs)}|min={t.minIndexable}"
