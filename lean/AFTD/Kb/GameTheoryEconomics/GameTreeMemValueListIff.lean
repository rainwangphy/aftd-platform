import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListEqMap
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# GameTree.mem_valueList_iff

Topic: equilibria   Node: e211910031f5

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.mem_valueList_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Membership in `valueList` via membership in the source list.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [TotalPreorder U] [DecidableLE U] in
/-- Membership in `valueList` via membership in the source list. -/
theorem GameTree.mem_valueList_iff {v : N → U} {l : List (GameTree N U)} :
    v ∈ valueList l ↔ ∃ c ∈ l, value c = v := by
  rw [valueList_eq_map]
  simp [List.mem_map, eq_comm]
