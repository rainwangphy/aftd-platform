import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceSelect
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceInstInhabitedGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeValue
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeStrategy

/-!
# ZeroSumChance.GameTree.DStrategy

Topic: equilibria   Node: fd0a99a3d6ef

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.GameTree.DStrategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**A's dominant strategy**: at each A-node, move to whichever child has the higher value; ties go left.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- **A's dominant strategy**: at each A-node, move to whichever child has the higher value; ties go left. -/
def ZeroSumChance.GameTree.DStrategy : Strategy :=
  fun L R => if L.value < R.value then .r else .l
