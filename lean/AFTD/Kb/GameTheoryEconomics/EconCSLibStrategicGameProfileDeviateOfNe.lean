import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate
import AFTD.Kb.GameTheoryEconomics.ProfileDeviateOfNe

/-!
# EconCSLib.StrategicGame.Profile.deviate_of_ne

Topic: equilibria   Node: 700d3b5b10ec

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.Profile.deviate_of_ne`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

At every other player, the updated profile is unchanged.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
variable {G : EconCSLib.StrategicGame N U} [DecidableEq N] in
/-- At every other player, the updated profile is unchanged. -/
@[simp]
theorem EconCSLib.StrategicGame.Profile.deviate_of_ne (σ : G.Profile) (i : N) (s' : G.strategy i) {j : N} (h : j ≠ i) :
    deviate σ i s' j = σ j := by
  simp [EconCSLib.StrategicGame.deviate, h]
