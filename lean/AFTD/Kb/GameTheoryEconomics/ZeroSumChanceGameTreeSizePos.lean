import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChancePlayer
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceInstInhabitedGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeSize

/-!
# ZeroSumChance.GameTree.size_pos

Topic: equilibria   Node: 166b85a771e0

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.GameTree.size_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every game tree has positive size.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Every game tree has positive size. -/
lemma ZeroSumChance.GameTree.size_pos (t : GameTree) : 1 ≤ t.size := by
  induction t with
  | Leaf _      => simp [size]
  | Pnode _ L R => simp [size]; linarith
  | Nnode _ L R => simp [size]; linarith
