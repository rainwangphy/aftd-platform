import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameStrategyProfile
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal

/-!
# ExtensiveGame.StrategyProfile.actionAt

Topic: equilibria   Node: e2f76dcc4dc1

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.StrategyProfile.actionAt`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Strategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a strategy profile, extract the action at a nonterminal player-controlled state. Returns `none` when the state is non-player-controlled. Terminal states cannot be queried: their mover labels are semantically irrelevant and their action fibers are empty.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- Given a strategy profile, extract the action at a nonterminal player-controlled state. Returns `none` when the state is non-player-controlled. Terminal states cannot be queried: their mover labels are semantically irrelevant and their action fibers are empty. -/
def ExtensiveGame.StrategyProfile.actionAt {G : ExtensiveGame N U}
    (σ : StrategyProfile G) (s : G.State)
    (hnonterminal : ¬ G.isTerminal s) :
    Option (Σ _ : N, G.Action s) :=
  match h : G.mover s with
  | some i => some ⟨i, σ i s h hnonterminal⟩
  | none => none
