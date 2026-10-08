import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeExpectedPayoff
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeHeadStrategy
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeFairCoinGame
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeExpectedPayoffWithFuel
import AFTD.Kb.GameTheoryEconomics.StochasticGameTree
import AFTD.Kb.GameTheoryEconomics.StochasticGameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode

/-!
# StochasticGameTree.fairCoin_expected_player0

Topic: equilibria   Node: 4e4f3e4760ba

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree.fairCoin_expected_player0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StochasticGameTree.fairCoin_expected_player0
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open StochasticGameTree in
variable {N : Type*} in
theorem StochasticGameTree.fairCoin_expected_player0 :
    expectedPayoff (headStrategy : Strategy (Fin 2)) fairCoinGame 0 = 1 / 2 := by
  norm_num [expectedPayoff, expectedPayoffWithFuel, fairCoinGame, headStrategy]
