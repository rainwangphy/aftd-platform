import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeSize
import AFTD.Kb.GameTheoryEconomics.GameTreeSizeHeadLt
import AFTD.Kb.GameTheoryEconomics.GameTreeSizeMemTailLt
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeSize

/-!
# GameTree.size_mem_children_lt

Topic: equilibria   Node: 2526bd03c5fd

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.size_mem_children_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any child (head or in tail) is structurally smaller than the node.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} in
/-- Any child (head or in tail) is structurally smaller than the node. -/
theorem GameTree.size_mem_children_lt (m : N) (h : GameTree N U) (t : List (GameTree N U))
    {c : GameTree N U} (hmem : c ∈ children (Node m h t)) :
    c.size < (Node m h t).size := by
  simp [children, List.mem_cons] at hmem
  rcases hmem with rfl | hmem'
  · exact size_head_lt m c t
  · exact size_mem_tail_lt m h t hmem'
