import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFloorWeightPointwise
import AFTD.Kb.Physics.EnergyFilterFloorFourthMajorant
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeightBounds

/-!
# energy_filter_floor_fourth_integral_limit

Topic: statistical_mechanics   Node: 0e5e7d8821a2

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

The integral of the fourth power of the centered binomial weight at floor(√k x) tends to √π/2.
-/

theorem energy_filter_floor_fourth_integral_limit :
    Filter.Tendsto
      (fun k : ℕ => ∫ x : ℝ,
        energy_filter_centered_binomial_weight k (Int.floor (Real.sqrt (k:ℝ)*x)) ^ 4)
      Filter.atTop (nhds (Real.sqrt Real.pi / 2)) := by
  let F : ℕ → ℝ → ℝ := fun k x =>
    energy_filter_centered_binomial_weight k (Int.floor (Real.sqrt (k:ℝ)*x)) ^ 4
  let G : ℝ → ℝ := fun x => Real.exp 2 * Real.exp (-x^2)
  let f : ℝ → ℝ := fun x => Real.exp (-(4:ℝ)*x^2)
  have hmeas : ∀ᶠ k : ℕ in Filter.atTop,
      MeasureTheory.AEStronglyMeasurable (F k) := by
    apply Filter.Eventually.of_forall
    intro k
    have hflo : Measurable (fun x : ℝ => Int.floor (Real.sqrt (k:ℝ)*x)) :=
      Int.measurable_floor.comp (measurable_const.mul measurable_id)
    have hweight : Measurable (energy_filter_centered_binomial_weight k) := measurable_of_countable _
    exact ((hweight.comp hflo).pow_const 4).aestronglyMeasurable
  have hint : MeasureTheory.Integrable G := by
    have hi := (integrable_exp_neg_mul_sq (b := (1:ℝ)) (by norm_num)).const_mul (Real.exp 2)
    simpa [G] using hi
  have hbound : ∀ᶠ k : ℕ in Filter.atTop, ∀ᵐ x : ℝ, ‖F k x‖ ≤ G x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    apply Filter.Eventually.of_forall
    intro x
    dsimp [F,G]
    rw [abs_of_nonneg (pow_nonneg (energy_filter_centered_binomial_weight_bounds _ _).1 _)]
    exact energy_filter_floor_fourth_majorant k x hk
  have hlim : ∀ᵐ x : ℝ, Filter.Tendsto (fun k : ℕ => F k x) Filter.atTop (nhds (f x)) := by
    apply Filter.Eventually.of_forall
    intro x
    have h := (energy_filter_floor_weight_pointwise x).pow 4
    have he : (Real.exp (-x^2))^4 = Real.exp (-(4:ℝ)*x^2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    rw [he] at h
    exact h
  have ht := MeasureTheory.tendsto_integral_filter_of_dominated_convergence G hmeas hbound hint hlim
  have hi : (∫ x : ℝ, f x) = Real.sqrt Real.pi / 2 := by
    dsimp [f]
    rw [integral_gaussian, Real.sqrt_div Real.pi_pos.le]
    norm_num
  rw [hi] at ht
  exact ht
