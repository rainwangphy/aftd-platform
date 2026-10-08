import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfile
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameBehaviorProfileActionProb
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameSubgameAtIsEmptyDecidable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtActionFintype
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameReachableSubgameAtIsEmptyDecidable

/-!
# ExtensiveGame.reachProbFrom

Topic: equilibria   Node: 65ee20f86478

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.reachProbFrom`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite-fuel probability of reaching `target` from `start` under a behavior profile. The definition records the probability of hitting `target` within the remaining fuel. It is intentionally fuel-indexed, matching `ExtensiveGame.Play`, because the Arena framework also supports infinite games.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- Finite-fuel probability of reaching `target` from `start` under a behavior profile. The definition records the probability of hitting `target` within the remaining fuel. It is intentionally fuel-indexed, matching `ExtensiveGame.Play`, because the Arena framework also supports infinite games. -/
noncomputable def ExtensiveGame.reachProbFrom {G : ExtensiveGame iota U}
    [DecidableEq G.State] [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (start target : G.State) : Nat -> Real
  | 0 => if start = target then 1 else 0
  | fuel + 1 =>
      if start = target then
        1
      else
        Finset.univ.sum fun a : G.Action start =>
          beta.actionProb start a * reachProbFrom beta (G.next start a) target fuel
