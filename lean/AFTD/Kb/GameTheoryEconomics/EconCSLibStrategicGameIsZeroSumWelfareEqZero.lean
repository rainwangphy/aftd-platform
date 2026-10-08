import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameWelfare
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.IsZeroSum.welfare_eq_zero

Topic: equilibria   Node: d27687a8a5b6

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsZeroSum.welfare_eq_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Two-player zero-sum games have zero social welfare at every profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- Two-player zero-sum games have zero social welfare at every profile. -/
theorem EconCSLib.StrategicGame.IsZeroSum.welfare_eq_zero [AddCommMonoid U]
    {G : EconCSLib.StrategicGame (Fin 2) U} (hzs : IsZeroSum G) (σ : G.Profile) :
    welfare G σ = 0 := by
  unfold welfare
  rw [Fin.sum_univ_two]
  exact hzs σ
