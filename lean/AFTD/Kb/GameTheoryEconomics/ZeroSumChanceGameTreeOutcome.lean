import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChancePlayer
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceSelect
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceInstInhabitedGameTree
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# ZeroSumChance.GameTree.outcome

Topic: equilibria   Node: 1e819bc7c278

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.GameTree.outcome`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The realized payoff for player A when A plays `SA` and B plays `SB`. Nature's moves are resolved by their fixed probabilities.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The realized payoff for player A when A plays `SA` and B plays `SB`. Nature's moves are resolved by their fixed probabilities. -/
def ZeroSumChance.GameTree.outcome (SA SB : Strategy) : GameTree → ℚ
  | Leaf r      => r
  | Pnode p L R => match p with
    | .A => match SA L R with
      | .l => outcome SA SB L
      | .r => outcome SA SB R
    | .B => match SB L R with
      | .l => outcome SA SB L
      | .r => outcome SA SB R
  | Nnode prob L R => prob * outcome SA SB L + (1 - prob) * outcome SA SB R
