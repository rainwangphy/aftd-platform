import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOn
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOnMem
import AFTD.Kb.GameTheoryEconomics.GameTreeMemValueListIff
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.value_Node_eq_some_child_value

Topic: equilibria   Node: 04943aec66d9

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value_Node_eq_some_child_value`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The value at a node is itself the value of some child (the argmax). Specifically, `argMaxOn ... ∈ value h :: valueList t`, so it equals `value c` for some `c ∈ h :: t`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [TotalPreorder U] [DecidableLE U] in
/-- The value at a node is itself the value of some child (the argmax). Specifically, `argMaxOn ... ∈ value h :: valueList t`, so it equals `value c` for some `c ∈ h :: t`. -/
theorem GameTree.value_Node_eq_some_child_value (m : N) (h : GameTree N U)
    (t : List (GameTree N U)) :
    ∃ c ∈ h :: t, value (Node m h t) = value c := by
  rw [value_Node]
  have hmem := List.argMaxOn_mem (fun v => v m) (value h) (valueList t)
  rcases List.mem_cons.mp hmem with heq | hmem'
  · exact ⟨h, List.mem_cons_self, heq⟩
  · rw [mem_valueList_iff] at hmem'
    obtain ⟨c, hc_mem, hc_eq⟩ := hmem'
    refine ⟨c, List.mem_cons.mpr (Or.inr hc_mem), ?_⟩
    exact hc_eq.symm
