import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameStrategy

/-!
# ExtensiveGame.StrategyProfile

Topic: equilibria   Node: 8e54e43744d1

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.StrategyProfile`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Strategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strategy profile: a strategy for each player.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N : Type*} {U : Type*} in
/-- A strategy profile: a strategy for each player. -/
def ExtensiveGame.StrategyProfile (G : ExtensiveGame N U) :=
  (i : N) → G.Strategy i
