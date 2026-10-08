import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMContinuity
import AFTD.Kb.GameTheoryEconomics.VNMNotCompletePref
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.Indiff
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.NotComplete.continuous

Topic: general_equilibrium   Node: c3276d2b7931

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotComplete.continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotComplete.continuous
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotComplete.continuous : Continuity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  simp only [pref] at h₁₂ h₂₃
  subst h₁₂; subst h₂₃
  refine ⟨(1 : ℚ), by norm_num, le_refl 1, ?_⟩
  constructor <;> {
    simp only [pref]
    ext i
    simp [Lottery.mix, stdSimplex.mix]
  }
