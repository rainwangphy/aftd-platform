import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialFourthMassAsymptotic
import AFTD.Kb.Physics.EnergyFilterSequenceChooseRatioTendstoOne
import AFTD.Kb.Physics.EnergyFilterFloorWeightPointwise
import AFTD.Kb.Physics.EnergyFilterFloorOffsetWeightPointwise
import AFTD.Kb.Physics.EnergyFilterFloorKernelNonnegBound
import AFTD.Kb.Physics.EnergyFilterFloorKernelMeasurable
import AFTD.Kb.Physics.EnergyFilterCenteredKernelStepIntegral

/-!
# energy_filter_centered_binomial_quartic_kernel_limit

Topic: statistical_mechanics   Node: a56b14a6656f

Provenance: helper lemma. OP-892: alternative reduction via centered binomial correlations; experiment 26245.

For any fixed integer shifts u, v and w, the sum of the product of four shifted centered binomial weights, divided by √k, tends to √π/2.
-/

theorem energy_filter_centered_binomial_quartic_kernel_limit (u v w : ℤ) :
    Filter.Tendsto (fun k : ℕ =>
      (∑' t : ℤ, energy_filter_centered_binomial_weight k t *
        energy_filter_centered_binomial_weight k (t + u) *
        energy_filter_centered_binomial_weight k (t + v) *
        energy_filter_centered_binomial_weight k (t + w)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds (Real.sqrt Real.pi / 2)) := by
  let F : ℕ → ℝ → ℝ := fun k x => let t := Int.floor (Real.sqrt (k:ℝ)*x)
    energy_filter_centered_binomial_weight k t *
      energy_filter_centered_binomial_weight k (t+u) *
      energy_filter_centered_binomial_weight k (t+v) *
      energy_filter_centered_binomial_weight k (t+w)
  let G : ℝ → ℝ := fun x => Real.exp (1/2) * Real.exp (-(x^2/4))
  let f : ℝ → ℝ := fun x => Real.exp (-(4:ℝ)*x^2)
  have hmeas : ∀ᶠ k : ℕ in Filter.atTop, MeasureTheory.AEStronglyMeasurable (F k) :=
    Filter.Eventually.of_forall (fun k => (energy_filter_floor_kernel_measurable k u v w).aestronglyMeasurable)
  have hint : MeasureTheory.Integrable G := by
    have hi := (integrable_exp_neg_mul_sq (b := (1/4:ℝ)) (by norm_num)).const_mul (Real.exp (1/2))
    simpa [G, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hi
  have hbound : ∀ᶠ k : ℕ in Filter.atTop, ∀ᵐ x : ℝ, ‖F k x‖ ≤ G x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    apply Filter.Eventually.of_forall
    intro x
    have h := energy_filter_floor_kernel_nonneg_bound k u v w x hk
    simpa only [F,G, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hlim : ∀ᵐ x : ℝ, Filter.Tendsto (fun k : ℕ => F k x) Filter.atTop (nhds (f x)) := by
    apply Filter.Eventually.of_forall
    intro x
    have h := (((energy_filter_floor_weight_pointwise x).mul
      (energy_filter_floor_offset_weight_pointwise x u)).mul
      (energy_filter_floor_offset_weight_pointwise x v)).mul
      (energy_filter_floor_offset_weight_pointwise x w)
    have he : Real.exp (-x^2)*Real.exp (-x^2)*Real.exp (-x^2)*Real.exp (-x^2) =
        Real.exp (-(4:ℝ)*x^2) := by
      calc
        _ = (Real.exp (-x^2))^4 := by ring
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; norm_num
    rw [he] at h
    exact h
  have ht := MeasureTheory.tendsto_integral_filter_of_dominated_convergence G hmeas hbound hint hlim
  have hi : (∫ x : ℝ, f x) = Real.sqrt Real.pi / 2 := by
    dsimp [f]
    rw [integral_gaussian, Real.sqrt_div Real.pi_pos.le]
    norm_num
  rw [hi] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  exact energy_filter_centered_kernel_step_integral k u v w hk
