import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorStrategy

Topic: equilibria   Node: 99ee5152b927

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorStrategy`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A behavior strategy for player `i`: at every nonterminal state controlled by `i`, choose a probability distribution over the actions available there. This is a state-based primitive. A later imperfect-information layer can impose the usual information-set consistency condition by requiring equal distributions across states in the same information set. The nonterminal premise prevents a semantically ignored terminal mover label from creating an impossible simplex coordinate over an empty action type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- A behavior strategy for player `i`: at every nonterminal state controlled by `i`, choose a probability distribution over the actions available there. This is a state-based primitive. A later imperfect-information layer can impose the usual information-set consistency condition by requiring equal distributions across states in the same information set. The nonterminal premise prevents a semantically ignored terminal mover label from creating an impossible simplex coordinate over an empty action type. -/
def ExtensiveGame.BehaviorStrategy (G : ExtensiveGame iota U) (i : iota)
    [(s : G.State) -> Fintype (G.Action s)] : Type _ :=
  (s : G.State) -> G.mover s = some i ->
    ¬ G.isTerminal s -> stdSimplex Real (G.Action s)
