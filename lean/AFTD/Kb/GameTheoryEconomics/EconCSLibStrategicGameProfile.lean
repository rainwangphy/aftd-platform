import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.Profile

Topic: equilibria   Node: 3bebe1cd9776

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.Profile`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The type of strategy profiles for game `G`: each player picks a strategy. This is a dependent function `∀ i, G.strategy i`. The profile type is bound to the game, making it explicit that a profile belongs to a specific strategic game.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- The type of strategy profiles for game `G`: each player picks a strategy. This is a dependent function `∀ i, G.strategy i`. The profile type is bound to the game, making it explicit that a profile belongs to a specific strategic game. -/
abbrev EconCSLib.StrategicGame.Profile (G : EconCSLib.StrategicGame N U) := ∀ i, G.strategy i
