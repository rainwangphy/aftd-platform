import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChancePlayer
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceInstInhabitedGameTree

/-!
# ZeroSumChance.GameTree.value

Topic: equilibria   Node: 9b65782c84e3

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.GameTree.value`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The backward-induction value of the game tree for player A. * A-node: A maximizes, so we take the max of both children's values. * B-node: B minimizes, so we take the min of both children's values. * Nature node: probability-weighted average (rational arithmetic).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The backward-induction value of the game tree for player A. * A-node: A maximizes, so we take the max of both children's values. * B-node: B minimizes, so we take the min of both children's values. * Nature node: probability-weighted average (rational arithmetic). -/
def ZeroSumChance.GameTree.value : GameTree → ℚ
  | Leaf r      => r
  | Pnode p L R => match p with
    | .A => max L.value R.value
    | .B => min L.value R.value
  | Nnode prob L R => prob * L.value + (1 - prob) * R.value
