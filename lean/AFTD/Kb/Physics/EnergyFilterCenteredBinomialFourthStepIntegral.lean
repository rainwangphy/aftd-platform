import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterStepSumIntegral
import AFTD.Kb.Physics.EnergyFilterStepSumEqFloor
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# energy_filter_centered_binomial_fourth_step_integral

Topic: statistical_mechanics   Node: 638a87febd06

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

For k≥1, the integral of the fourth power of the centered binomial weight at floor(√k x) equals the finite sum of the fourth powers over integer offsets from −k to k, divided by √k.
-/

theorem energy_filter_centered_binomial_fourth_step_integral
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ x : ℝ, energy_filter_centered_binomial_weight k (Int.floor (Real.sqrt (k:ℝ)*x)) ^ 4) =
      (∑ i ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), energy_filter_centered_binomial_weight k i ^ 4) /
        Real.sqrt (k:ℝ) := by
  let s : Finset ℤ := Finset.Icc (-(k:ℤ)) (k:ℤ)
  let w : ℤ → ℝ := fun i => energy_filter_centered_binomial_weight k i ^ 4
  have hh : 0 < Real.sqrt (k:ℝ) := by positivity
  have hw : ∀ i ∉ s, w i = 0 := by
    intro i hi
    have hi' : ¬ (-(k:ℤ) ≤ i ∧ i ≤ (k:ℤ)) := by simpa [s] using hi
    simp [w, energy_filter_centered_binomial_weight, hi']
  have he (x : ℝ) := energy_filter_step_sum_eq_floor s w (Real.sqrt (k:ℝ)) x hh hw
  have hint := energy_filter_step_sum_integral s w (Real.sqrt (k:ℝ)) hh
  calc
    _ = ∫ x : ℝ, ∑ i ∈ s,
      (Set.Ico ((i:ℝ)/Real.sqrt (k:ℝ)) (((i:ℝ)+1)/Real.sqrt (k:ℝ))).indicator (fun _ : ℝ => w i) x := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (he x).symm)
    _ = _ := hint
