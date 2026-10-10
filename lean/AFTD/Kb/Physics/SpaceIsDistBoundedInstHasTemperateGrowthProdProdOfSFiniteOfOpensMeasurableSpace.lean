import AFTD.Prelude

/-!
# Space.IsDistBounded.instHasTemperateGrowthProdProdOfSFiniteOfOpensMeasurableSpace

Topic: classical_mechanics   Node: 2352c54a086e

Provenance: formalization of a published result. Source: Physlib, `Space.IsDistBounded.instHasTemperateGrowthProdProdOfSFiniteOfOpensMeasurableSpace`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/IsDistBounded.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.IsDistBounded.instHasTemperateGrowthProdProdOfSFiniteOfOpensMeasurableSpace
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SchwartzMap NNReal in
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F] [NormedSpace ℝ F'] in
variable [NormedSpace ℝ E] in
open MeasureTheory in
noncomputable instance Space.IsDistBounded.instHasTemperateGrowthProdProdOfSFiniteOfOpensMeasurableSpace {D1 : Type} [NormedAddCommGroup D1] [MeasurableSpace D1]
    {D2 : Type} [NormedAddCommGroup D2] [MeasurableSpace D2]
    (μ1 : Measure D1) (μ2 : Measure D2)
    [Measure.HasTemperateGrowth μ1] [Measure.HasTemperateGrowth μ2] [SFinite μ2]
    [OpensMeasurableSpace (D1 × D2)] :
    Measure.HasTemperateGrowth (μ1.prod μ2) where
  exists_integrable := by
    obtain ⟨rt1, h1⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := μ1)
    obtain ⟨rt2, h2⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := μ2)
    use rt1 + rt2
    apply Integrable.mono' (h1.mul_prod h2)
    · apply AEMeasurable.aestronglyMeasurable
      fun_prop
    filter_upwards with x
    simp only [Nat.cast_add, neg_add_rev, Real.norm_eq_abs, Real.rpow_neg_natCast, zpow_neg,
      zpow_natCast]
    calc _
      _ = |(1 + ‖x‖) ^ (-(rt1 : ℝ)) * (1 + ‖x‖) ^ (-(rt2 : ℝ))| := by
        rw [Real.rpow_add (by positivity), mul_comm]
      _ = (1 + ‖x‖) ^ (-(rt1 : ℝ)) * (1 + ‖x‖) ^ (-(rt2 : ℝ)) := by
        rw [abs_of_nonneg (by positivity)]
    simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · exact inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (by simpa using norm_fst_le x) rt1)
    · exact inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (by simpa using norm_snd_le x) rt2)
