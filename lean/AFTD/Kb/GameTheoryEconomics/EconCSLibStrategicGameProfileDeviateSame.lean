import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate
import AFTD.Kb.GameTheoryEconomics.ProfileDeviateSame

/-!
# EconCSLib.StrategicGame.Profile.deviate_same

Topic: equilibria   Node: 830096440023

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.Profile.deviate_same`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

At the deviated player, the updated profile returns the new strategy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
variable {G : EconCSLib.StrategicGame N U} [DecidableEq N] in
/-- At the deviated player, the updated profile returns the new strategy. -/
@[simp]
theorem EconCSLib.StrategicGame.Profile.deviate_same (σ : G.Profile) (i : N) (s' : G.strategy i) :
    deviate σ i s' i = s' := by
  simp [EconCSLib.StrategicGame.deviate]
