import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorStrategy
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame

/-!
# ExtensiveGame.BehaviorStrategy.IsCompletelyMixed

Topic: equilibria   Node: 09d58ec1e9cc

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorStrategy.IsCompletelyMixed`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A behavior strategy is completely mixed if every available action at every state controlled by the player receives positive probability. This is the state-based behavior-strategy part of MSZ Definition 7.6. The later imperfect-information layer can identify states inside the same information set; this predicate is already the local full-support condition used by the current Arena-based behavior-strategy API.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- A behavior strategy is completely mixed if every available action at every state controlled by the player receives positive probability. This is the state-based behavior-strategy part of MSZ Definition 7.6. The later imperfect-information layer can identify states inside the same information set; this predicate is already the local full-support condition used by the current Arena-based behavior-strategy API. -/
def ExtensiveGame.BehaviorStrategy.IsCompletelyMixed {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota}
    (beta : G.BehaviorStrategy i) : Prop :=
  forall (s : G.State) (h : G.mover s = some i)
    (hnonterminal : ¬ G.isTerminal s) (a : G.Action s),
    0 < (beta s h hnonterminal).val a
