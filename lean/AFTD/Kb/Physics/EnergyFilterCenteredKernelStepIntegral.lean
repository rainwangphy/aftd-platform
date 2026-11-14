import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight
import AFTD.Kb.Physics.EnergyFilterStepSumIntegral
import AFTD.Kb.Physics.EnergyFilterStepSumEqFloor
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# energy_filter_centered_kernel_step_integral

Topic: statistical_mechanics   Node: f3058d3f7fd7

Provenance: helper lemma. OP-892: direct shifted-binomial kernel limit and uniform bound.

For k≥1 and integer shifts u,v,w, the integral of the four shifted binomial weights at floor(√k x) equals their integer sum divided by √k.
-/

theorem energy_filter_centered_kernel_step_integral
    (k : ℕ) (u v w : ℤ) (hk : 1 ≤ k) :
    (∫ x : ℝ, let t := Int.floor (Real.sqrt (k:ℝ)*x)
      energy_filter_centered_binomial_weight k t *
      energy_filter_centered_binomial_weight k (t+u) *
      energy_filter_centered_binomial_weight k (t+v) *
      energy_filter_centered_binomial_weight k (t+w)) =
      (∑' t : ℤ, energy_filter_centered_binomial_weight k t *
        energy_filter_centered_binomial_weight k (t+u) *
        energy_filter_centered_binomial_weight k (t+v) *
        energy_filter_centered_binomial_weight k (t+w)) / Real.sqrt (k:ℝ) := by
  let s : Finset ℤ := Finset.Icc (-(k:ℤ)) (k:ℤ)
  let z : ℤ → ℝ := fun t => energy_filter_centered_binomial_weight k t *
      energy_filter_centered_binomial_weight k (t+u) *
      energy_filter_centered_binomial_weight k (t+v) *
      energy_filter_centered_binomial_weight k (t+w)
  have hh : 0 < Real.sqrt (k:ℝ) := by positivity
  have hz : ∀ i ∉ s, z i = 0 := by
    intro i hi
    have hi' : ¬ (-(k:ℤ) ≤ i ∧ i ≤ (k:ℤ)) := by simpa [s] using hi
    simp [z, energy_filter_centered_binomial_weight, hi']
  have he (x : ℝ) := energy_filter_step_sum_eq_floor s z (Real.sqrt (k:ℝ)) x hh hz
  have hint := energy_filter_step_sum_integral s z (Real.sqrt (k:ℝ)) hh
  have hsum : (∑' i : ℤ, z i) = ∑ i ∈ s, z i := by
    apply tsum_eq_sum
    intro i hi
    exact hz i hi
  calc
    _ = ∫ x : ℝ, ∑ i ∈ s,
      (Set.Ico ((i:ℝ)/Real.sqrt (k:ℝ)) (((i:ℝ)+1)/Real.sqrt (k:ℝ))).indicator (fun _ : ℝ => z i) x := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (he x).symm)
    _ = _ := by rw [hsum]; exact hint
