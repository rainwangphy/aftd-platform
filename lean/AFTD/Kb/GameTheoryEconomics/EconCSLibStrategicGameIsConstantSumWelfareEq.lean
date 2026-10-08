import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameWelfare
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsConstantSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsConstantSum.welfare_eq

Topic: equilibria   Node: 4eb352a051b0

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsConstantSum.welfare_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Two-player constant-sum games have constant social welfare at every profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- Two-player constant-sum games have constant social welfare at every profile. -/
theorem EconCSLib.StrategicGame.IsConstantSum.welfare_eq [AddCommMonoid U]
    {G : EconCSLib.StrategicGame (Fin 2) U} {c : U} (hcs : IsConstantSum G c) (σ : G.Profile) :
    welfare G σ = c := by
  unfold welfare
  rw [Fin.sum_univ_two]
  exact hcs σ
