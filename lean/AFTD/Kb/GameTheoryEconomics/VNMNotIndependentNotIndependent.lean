import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VNMIndependence
import AFTD.Kb.GameTheoryEconomics.VNMNotIndependentPref
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousPref
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.NotIndependent.not_independent

Topic: general_equilibrium   Node: c72541847398

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotIndependent.not_independent`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

VNM.NotIndependent.not_independent
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotIndependent.not_independent : ¬ Independence pref := by
  intro h
  -- L₁ = (2/5, 3/5, 0): L₁(0) = 2/5 < 1/2 (low)
  -- L₂ = (3/5, 2/5, 0): L₂(0) = 3/5 ≥ 1/2 (high)
  -- ¬pref L₁ L₂: 2/5 < 1/2 and 3/5 ≥ 1/2
  -- N = (4/5, 1/5, 0): N(0) = 4/5
  -- mix 1/2 L₁ N: val 0 = 3/5 ≥ 1/2 → pref (mix L₁ N) anything
  -- So pref (mix L₁ N) (mix L₂ N) but ¬pref L₁ L₂. Independence fails.
  let L₁ : Lottery ℚ (Fin 3) := ⟨![2/5, 3/5, 0], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  let L₂ : Lottery ℚ (Fin 3) := ⟨![3/5, 2/5, 0], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  let N : Lottery ℚ (Fin 3) := ⟨![4/5, 1/5, 0], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  have h_not : ¬ pref L₁ L₂ := by
    simp only [pref]; push_neg; constructor <;> norm_num [L₁, L₂]
  have h_mix : pref (Lottery.mix (1/2) (by norm_num) (by norm_num) L₁ N)
                     (Lottery.mix (1/2) (by norm_num) (by norm_num) L₂ N) := by
    simp only [pref, Lottery.mix, stdSimplex.mix]; left; norm_num [L₁, N]
  exact h_not ((h L₁ L₂ N (1/2) (by norm_num) (by norm_num)).mpr h_mix)
