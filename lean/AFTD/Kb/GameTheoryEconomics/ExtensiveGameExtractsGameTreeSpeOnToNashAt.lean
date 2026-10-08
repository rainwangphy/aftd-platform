import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameExtractsGameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfectOn
import AFTD.Kb.GameTheoryEconomics.GameTreeIsNashAt
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfectOnToNashAt
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaToArena
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaInit
import AFTD.Kb.GameTheoryEconomics.ControlledGameOfArenaMover
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGamePayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfControlledGameToControlledGameSelf
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaToArena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaInit
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaMover
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameOfArenaPayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsPlayerStateIffToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsNonPlayerStateIffToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameNoChanceIffToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsReachableIffToControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtInit
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtMover
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtPayoff
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtNext
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeStrategy

/-!
# ExtensiveGame.ExtractsGameTree.spe_on_to_nash_at

Topic: equilibria   Node: 8ce198652b18

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ExtractsGameTree.spe_on_to_nash_at`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

On any extracted tree, root-scoped subgame perfection implies root Nash equilibrium through the ordinary `GameTree` equilibrium API.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ExtensiveGame in
variable {N U : Type*} (G : ExtensiveGame N U) in
/-- On any extracted tree, root-scoped subgame perfection implies root Nash equilibrium through the ordinary `GameTree` equilibrium API. -/
theorem ExtensiveGame.ExtractsGameTree.spe_on_to_nash_at [TotalPreorder U]
    {s : G.State} {tree : GameTree N U}
    (_h : ExtractsGameTree G s tree) {σ : GameTree.Strategy N U}
    (hspe : GameTree.IsSubgamePerfectOn σ tree) :
    GameTree.IsNashAt σ tree :=
  hspe.toNashAt
