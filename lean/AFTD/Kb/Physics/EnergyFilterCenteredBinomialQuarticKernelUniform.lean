import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterSequenceCentralBinomAsymptotic
import AFTD.Kb.Physics.EnergyFilterFloorKernelNonnegBound
import AFTD.Kb.Physics.EnergyFilterFloorKernelMeasurable
import AFTD.Kb.Physics.EnergyFilterCenteredKernelStepIntegral

/-!
# energy_filter_centered_binomial_quartic_kernel_uniform

Topic: statistical_mechanics   Node: 25ba8a8ab6a8

Provenance: helper lemma. OP-892: alternative reduction via centered binomial correlations; experiment 26245.

There is a positive constant uniformly bounding, for every k ≥ 1 and all integer shifts u, v and w, the absolute quartic shifted centered-binomial sum divided by √k.
-/

theorem energy_filter_centered_binomial_quartic_kernel_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ u v w : ℤ,
      |(∑' t : ℤ, energy_filter_centered_binomial_weight k t *
        energy_filter_centered_binomial_weight k (t + u) *
        energy_filter_centered_binomial_weight k (t + v) *
        energy_filter_centered_binomial_weight k (t + w)) / Real.sqrt (k : ℝ)| ≤ C := by
  let G : ℝ → ℝ := fun x => Real.exp (1/2) * Real.exp (-(x^2/4))
  have hG : MeasureTheory.Integrable G := by
    have hi := (integrable_exp_neg_mul_sq (b := (1/4:ℝ)) (by norm_num)).const_mul (Real.exp (1/2))
    simpa [G, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hi
  have hG0 : 0 ≤ ∫ x : ℝ, G x := by
    apply MeasureTheory.integral_nonneg
    intro x
    dsimp [G]
    positivity
  refine ⟨(∫ x : ℝ, G x)+1, by linarith, ?_⟩
  intro k hk u v w
  let F : ℝ → ℝ := fun x => let t := Int.floor (Real.sqrt (k:ℝ)*x)
    energy_filter_centered_binomial_weight k t *
      energy_filter_centered_binomial_weight k (t+u) *
      energy_filter_centered_binomial_weight k (t+v) *
      energy_filter_centered_binomial_weight k (t+w)
  have hpos (x : ℝ) : 0 ≤ F x := (energy_filter_floor_kernel_nonneg_bound k u v w x hk).1
  have hle (x : ℝ) : F x ≤ G x := (energy_filter_floor_kernel_nonneg_bound k u v w x hk).2
  have hF : MeasureTheory.Integrable F := by
    apply hG.mono' (energy_filter_floor_kernel_measurable k u v w).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hh : ‖F x‖ ≤ G x := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos x)]
      exact hle x
    exact hh
  have hi0 : 0 ≤ ∫ x : ℝ, F x := MeasureTheory.integral_nonneg hpos
  have hile : (∫ x : ℝ, F x) ≤ ∫ x : ℝ, G x := MeasureTheory.integral_mono hF hG hle
  rw [← energy_filter_centered_kernel_step_integral k u v w hk]
  rw [abs_of_nonneg hi0]
  linarith
