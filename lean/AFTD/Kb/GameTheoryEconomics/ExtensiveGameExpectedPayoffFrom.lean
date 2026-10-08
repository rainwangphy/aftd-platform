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
# ExtensiveGame.expectedPayoffFrom

Topic: equilibria   Node: ff7709a51bbd

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.expectedPayoffFrom`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BehaviorStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite-fuel expected payoff from `start` under a behavior profile. If the fuel runs out, or if a terminal state is reached, the current state's payoff is used. At a chance state without explicit chance probabilities, the current payoff is also used; the intended no-chance use case rules out nonterminal chance states by assuming `NoChance G`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {iota U : Type*} in
/-- Finite-fuel expected payoff from `start` under a behavior profile. If the fuel runs out, or if a terminal state is reached, the current state's payoff is used. At a chance state without explicit chance probabilities, the current payoff is also used; the intended no-chance use case rules out nonterminal chance states by assuming `NoChance G`. -/
noncomputable def ExtensiveGame.expectedPayoffFrom {G : ExtensiveGame iota Real}
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    (beta : G.BehaviorProfile) (start : G.State) : Nat -> iota -> Real
  | 0, who => G.payoff start who
  | fuel + 1, who =>
      if IsEmpty (G.Action start) then
        G.payoff start who
      else
        match G.mover start with
        | some _ =>
            Finset.univ.sum fun a : G.Action start =>
              beta.actionProb start a * expectedPayoffFrom beta (G.next start a) fuel who
        | none => G.payoff start who
