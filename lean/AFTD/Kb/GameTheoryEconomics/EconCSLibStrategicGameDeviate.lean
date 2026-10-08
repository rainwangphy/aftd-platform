import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Deviate
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.deviate

Topic: equilibria   Node: dbcdf8cd355f

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.deviate`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Unilateral deviation in a game-bound profile: player `i` switches to `s'`, while all other players keep their current strategies.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- Unilateral deviation in a game-bound profile: player `i` switches to `s'`, while all other players keep their current strategies. -/
abbrev EconCSLib.StrategicGame.deviate {G : EconCSLib.StrategicGame N U} [DecidableEq N]
    (σ : G.Profile) (i : N) (s' : G.strategy i) : G.Profile :=
  Function.update σ i s'
