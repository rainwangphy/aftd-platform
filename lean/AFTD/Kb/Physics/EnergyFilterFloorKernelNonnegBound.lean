import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeightBounds
import AFTD.Kb.Physics.EnergyFilterFloorWeightMajorant
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_floor_kernel_nonneg_bound

Topic: statistical_mechanics   Node: da50f21735b6

Provenance: helper lemma. OP-892: direct shifted-binomial kernel limit and uniform bound.

For k≥1 and all integer shifts, the product of the four floor-scaled centered binomial weights is nonnegative and at most exp(1/2)exp(−x²/4).
-/

theorem energy_filter_floor_kernel_nonneg_bound (k : ℕ) (u v w : ℤ) (x : ℝ) (hk : 1 ≤ k) :
    let t := Int.floor (Real.sqrt (k:ℝ)*x)
    0 ≤ energy_filter_centered_binomial_weight k t *
      energy_filter_centered_binomial_weight k (t+u) *
      energy_filter_centered_binomial_weight k (t+v) *
      energy_filter_centered_binomial_weight k (t+w) ∧
    energy_filter_centered_binomial_weight k t *
      energy_filter_centered_binomial_weight k (t+u) *
      energy_filter_centered_binomial_weight k (t+v) *
      energy_filter_centered_binomial_weight k (t+w) ≤ Real.exp (1/2) * Real.exp (-(x^2/4)) := by
  let t := Int.floor (Real.sqrt (k:ℝ)*x)
  let A := energy_filter_centered_binomial_weight k t
  let B := energy_filter_centered_binomial_weight k (t+u)
  let C := energy_filter_centered_binomial_weight k (t+v)
  let D := energy_filter_centered_binomial_weight k (t+w)
  have hA : 0 ≤ A ∧ A ≤ 1 := energy_filter_centered_binomial_weight_bounds k t
  have hB : 0 ≤ B ∧ B ≤ 1 := energy_filter_centered_binomial_weight_bounds k (t+u)
  have hC : 0 ≤ C ∧ C ≤ 1 := energy_filter_centered_binomial_weight_bounds k (t+v)
  have hD : 0 ≤ D ∧ D ≤ 1 := energy_filter_centered_binomial_weight_bounds k (t+w)
  have hprod : A*B*C*D ≤ A := by
    calc
      _ ≤ A*B*C := mul_le_of_le_one_right (mul_nonneg (mul_nonneg hA.1 hB.1) hC.1) hD.2
      _ ≤ A*B := mul_le_of_le_one_right (mul_nonneg hA.1 hB.1) hC.2
      _ ≤ A := mul_le_of_le_one_right hA.1 hB.2
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg hA.1 hB.1) hC.1) hD.1
  · exact hprod.trans (energy_filter_floor_weight_majorant k x hk)
