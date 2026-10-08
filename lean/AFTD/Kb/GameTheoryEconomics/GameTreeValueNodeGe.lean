import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListEqMap
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOn
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOnGe

/-!
# GameTree.value_Node_ge

Topic: equilibria   Node: 7044022555d8

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value_Node_ge`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Key optimality lemma**: at a `Node m h t`, the mover `m`'s coordinate of the backward-induction value dominates every child's.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [TotalPreorder U] [DecidableLE U] in
/-- **Key optimality lemma**: at a `Node m h t`, the mover `m`'s coordinate of the backward-induction value dominates every child's. -/
theorem GameTree.value_Node_ge (m : N) (h : GameTree N U) (t : List (GameTree N U))
    (c : GameTree N U) (hmem : c ∈ h :: t) :
    (value c) m ≤ (value (Node m h t)) m := by
  rw [value_Node]
  -- The argmax is chosen from (value h :: valueList t) w.r.t. `(·) m`.
  -- We need: `value c m ≤ argMaxOn (·m) (value h) (valueList t) m`.
  -- Since `c ∈ h :: t`, `value c ∈ value h :: valueList t`.
  have hcv : value c ∈ value h :: valueList t := by
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact List.mem_cons_self
    · refine List.mem_cons.mpr (Or.inr ?_)
      rw [valueList_eq_map]
      exact List.mem_map_of_mem hmem'
  exact List.argMaxOn_ge (fun v => v m) (value h) (valueList t) (value c) hcv
