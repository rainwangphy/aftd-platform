import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterRescaledWeightMajorant
import AFTD.Kb.Physics.EnergyFilterFloorDistanceLeOne
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeightGaussianBound
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_floor_weight_majorant

Topic: statistical_mechanics   Node: eb447b124e09

Provenance: helper lemma. OP-892: direct shifted-binomial kernel limit and uniform bound.

For k≥1, the centered binomial weight at floor(√k x) is at most exp(1/2)exp(−x²/4).
-/

theorem energy_filter_floor_weight_majorant (k : ℕ) (x : ℝ) (hk : 1 ≤ k) :
    energy_filter_centered_binomial_weight k (Int.floor (Real.sqrt (k:ℝ)*x)) ≤
      Real.exp (1/2) * Real.exp (-(x^2/4)) := by
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
  exact energy_filter_rescaled_weight_majorant _ x ((s:ℝ)/h) hbound' hdist
