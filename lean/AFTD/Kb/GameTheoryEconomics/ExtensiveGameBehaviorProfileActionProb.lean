import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileProbAt
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.BehaviorProfile.actionProb

Topic: equilibria   Node: 5c346b5015e9

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.BehaviorProfile.actionProb`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The action probability induced by a behavior profile at a state. At a player-controlled state this reads the controlling player's behavior strategy. At a chance state it returns `0`; this placeholder is compatible with the `NoChance` layer and can be replaced by explicit chance probabilities in a later stochastic layer.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- The action probability induced by a behavior profile at a state. At a player-controlled state this reads the controlling player's behavior strategy. At a chance state it returns `0`; this placeholder is compatible with the `NoChance` layer and can be replaced by explicit chance probabilities in a later stochastic layer. -/
def ExtensiveGame.BehaviorProfile.actionProb {G : ExtensiveGame iota U} [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (s : G.State) (a : G.Action s) : Real :=
  match h : G.mover s with
  | some i =>
      (beta i s h (fun hterminal => hterminal.false a)).val a
  | none => 0
