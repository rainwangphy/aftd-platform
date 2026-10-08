import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSize
import AFTD.Kb.GameTheoryEconomics.GameTreeSizePos
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeSize

/-!
# GameTree.size_mem_tail_lt

Topic: equilibria   Node: 0185503fa40d

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.size_mem_tail_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any tail child is structurally smaller.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} in
/-- Any tail child is structurally smaller. -/
theorem GameTree.size_mem_tail_lt (m : N) (h : GameTree N U) (t : List (GameTree N U))
    {c : GameTree N U} (hmem : c ∈ t) :
    c.size < (Node m h t).size := by
  simp only [size]
  have hsum : c.size ≤ (t.map size).sum := by
    induction t with
    | nil => cases hmem
    | cons x xs ih =>
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · simp [List.sum_cons]
        · simp [List.sum_cons]
          have := ih hmem'
          omega
  have : 0 < h.size := size_pos h
  omega
