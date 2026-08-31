/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Logic
public import Batteries.Data.List.Basic
public import Mathlib.Init
import all Init.Data.Array.Basic
import ExplicitLean.SimpEngine.Boundary.Tactic

/-! Parser-only regression reduced from a translated `lookmap.go_append`.
The replay payload strings are placeholders; this file is inventoried, not
elaborated. Its later `none` branch contains exactly one executable simp call.
An aggregate Mathlib parser silently missed it without reporting recovery. -/

public section

variable {α β : Type*}

namespace List

variable (f : α → Option α)

private theorem lookmap.go_append (l : List α) (acc : Array α) :
    lookmap.go f l acc = acc.toListAppend (lookmap f l) := by
  cases l with
  | nil => simp_engine_boundary_select
             -- Original simp:
             -- simp [go, lookmap]
(artifact_kind := "fixture" artifact_schema := 2 selector_schema := 2 semantic_contract := "fixture" occurrence_id := "fixture" recorded_module := "fixture")
             | "fixture" "fixture" "fixture" "fixture" 1 "fixture" "fixture" => apply_encoded_with_actions [declare_equation "fixture" "fixture", declare_equation "fixture" "fixture", declare_equation "fixture" "fixture", declare_equation "fixture" "fixture", declare_matcher "fixture" "fixture", declare_matcher "fixture" "fixture"] ("fixture" ==> "fixture" using "fixture")
  | cons hd tl =>
    rw [lookmap, go, go]
    cases f hd with
    | none =>
      simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.toList_push]
      rfl
    | some a => rfl


end List
