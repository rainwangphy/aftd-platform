import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMContinuity
import AFTD.Kb.GameTheoryEconomics.VNMNotIndependentPref
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.Indiff
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.NotIndependent.continuous

Topic: general_equilibrium   Node: f62873880e62

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotIndependent.continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotIndependent.continuous
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotIndependent.continuous : Continuity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  rcases le_or_gt (1/2 : ℚ) (L₂.val 0) with h₂_high | h₂_low
  · -- L₂ is "high" (L₂(0) ≥ 1/2). Use θ=1: mix = L₁.
    -- From pref L₁ L₂ with L₂ high: L₁ must also be high.
    have h₁_high : L₁.val 0 ≥ 1/2 := by
      simp only [pref] at h₁₂; rcases h₁₂ with h | h <;> linarith
    refine ⟨1, by norm_num, le_refl 1, ?_⟩
    simp only [indiff, pref, Lottery.mix, stdSimplex.mix]
    exact ⟨Or.inl (by nlinarith), Or.inl (by nlinarith)⟩
  · -- L₂ is "low" (L₂(0) < 1/2). Use θ=0: mix = L₃.
    -- From pref L₂ L₃ with L₂ low: L₃ must also be low.
    have h₃_low : L₃.val 0 < 1/2 := by
      simp only [pref] at h₂₃; rcases h₂₃ with h | h <;> linarith
    refine ⟨0, le_refl 0, by norm_num, ?_⟩
    simp only [indiff, pref, Lottery.mix, stdSimplex.mix]
    exact ⟨Or.inr (by nlinarith), Or.inr (by nlinarith)⟩
