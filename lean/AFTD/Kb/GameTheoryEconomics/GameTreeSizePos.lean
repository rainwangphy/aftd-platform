import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSize
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.Tcs.G
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeSize
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeSizePos

/-!
# GameTree.size_pos

Topic: equilibria   Node: 114fb088f056

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.size_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Size is always positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} in
/-- Size is always positive. -/
theorem GameTree.size_pos (g : GameTree N U) : 0 < g.size := by
  cases g with
  | Leaf _ => simp [size]
  | Node _ _ _ => simp [size] <;> omega
