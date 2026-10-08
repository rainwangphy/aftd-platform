import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChancePlayer
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceInstInhabitedGameTree
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# ZeroSumChance.GameTree.size

Topic: equilibria   Node: aeb8d60ad961

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.GameTree.size`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Structural size of a game tree (used internally for well-founded reasoning).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Structural size of a game tree (used internally for well-founded reasoning). -/
def ZeroSumChance.GameTree.size : GameTree → ℕ
  | Leaf _      => 1
  | Pnode _ L R => L.size + R.size
  | Nnode _ L R => L.size + R.size
