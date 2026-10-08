import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMContinuity
import AFTD.Kb.GameTheoryEconomics.VNMNotTransitivePref
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.Indiff
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.NotTransitive.continuous

Topic: general_equilibrium   Node: cf6fb06d9721

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotTransitive.continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotTransitive.continuous
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotTransitive.continuous : Continuity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  -- Try θ=0 (mix = L₃): works if pref L₃ L₂
  by_cases h₃₂ : pref L₃ L₂
  · refine ⟨0, le_refl 0, by norm_num, ?_⟩
    exact ⟨by simp only [pref, Lottery.mix, stdSimplex.mix] at h₂₃ ⊢; rcases h₂₃ with h | h <;> [left; right] <;> nlinarith,
           by simp only [pref, Lottery.mix, stdSimplex.mix] at h₃₂ ⊢; rcases h₃₂ with h | h <;> [left; right] <;> nlinarith⟩
  -- Try θ=1 (mix = L₁): works if pref L₂ L₁
  · by_cases h₂₁ : pref L₂ L₁
    · refine ⟨1, by norm_num, le_refl 1, ?_⟩
      exact ⟨by simp only [pref, Lottery.mix, stdSimplex.mix] at h₂₁ ⊢; rcases h₂₁ with h | h <;> [left; right] <;> nlinarith,
             by simp only [pref, Lottery.mix, stdSimplex.mix] at h₁₂ ⊢; rcases h₁₂ with h | h <;> [left; right] <;> nlinarith⟩
    · -- Neither endpoint works ⟹ L₁ strictly dominates L₂ strictly dominates L₃ on both coords
      simp only [pref] at h₃₂ h₂₁
      push_neg at h₃₂ h₂₁
      obtain ⟨h₃₂_0, h₃₂_1⟩ := h₃₂
      obtain ⟨h₂₁_0, h₂₁_1⟩ := h₂₁
      -- Match component 0: θ = (L₂(0) - L₃(0)) / (L₁(0) - L₃(0))
      have hden_pos : L₁.val 0 - L₃.val 0 > 0 := by linarith
      have hnum_pos : L₂.val 0 - L₃.val 0 > 0 := by linarith
      have hnum_lt : L₂.val 0 - L₃.val 0 < L₁.val 0 - L₃.val 0 := by linarith
      set θ := (L₂.val 0 - L₃.val 0) / (L₁.val 0 - L₃.val 0)
      refine ⟨θ, le_of_lt (div_pos hnum_pos hden_pos),
              le_of_lt (by rwa [div_lt_one hden_pos]), ?_⟩
      -- At this θ, mix.val 0 = L₂.val 0 (by construction)
      have hmix0 : θ * L₁.val 0 + (1 - θ) * L₃.val 0 = L₂.val 0 := by
        have hne : L₁.val 0 - L₃.val 0 ≠ 0 := ne_of_gt hden_pos
        simp only [θ]; field_simp; ring
      simp only [indiff, pref, Lottery.mix, stdSimplex.mix]
      exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
