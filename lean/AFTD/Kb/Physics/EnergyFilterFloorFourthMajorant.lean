import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeightGaussianBound
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeightBounds
import AFTD.Kb.Physics.EnergyFilterRescaledFourthMajorant
import AFTD.Kb.Physics.EnergyFilterFloorDistanceLeOne
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_floor_fourth_majorant

Topic: statistical_mechanics   Node: be9fa89b3410

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

For k≥1, the fourth power of the centered binomial weight at floor(√k x) is at most exp(2)exp(−x²).
-/

theorem energy_filter_floor_fourth_majorant (k : ℕ) (x : ℝ) (hk : 1 ≤ k) :
    energy_filter_centered_binomial_weight k (Int.floor (Real.sqrt (k:ℝ)*x)) ^ 4 ≤
      Real.exp 2 * Real.exp (-x^2) := by
  let s : ℤ := Int.floor (Real.sqrt (k:ℝ)*x)
  let h : ℝ := Real.sqrt (k:ℝ)
  have hkreal : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hh : 1 ≤ h := Real.one_le_sqrt.mpr hkreal
  have hp : 0 < h := by linarith
  have hsquare : h^2 = (k:ℝ) := Real.sq_sqrt (by positivity)
  have hdist : |x - (s:ℝ)/h| ≤ 1 := energy_filter_floor_distance_le_one h x hh
  have hbound := energy_filter_centered_binomial_weight_gaussian_bound k s hk
  have hbound' : energy_filter_centered_binomial_weight k s ≤ Real.exp (-(((s:ℝ)/h)^2/2)) := by
    convert hbound using 1
    congr 1
    field_simp
    nlinarith [hsquare]
  exact energy_filter_rescaled_fourth_majorant _ x ((s:ℝ)/h)
    (energy_filter_centered_binomial_weight_bounds k s).1 hbound' hdist
