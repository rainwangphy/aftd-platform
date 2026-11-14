import AFTD.Prelude
import AFTD.Kb.Tcs.ShiftedGeometricDistribution

/-!
# shifted_geometric_distribution_nonneg

Topic: information   Node: d5238ded8838

Provenance: helper lemma. arXiv:2611.16066, Theorem 5.1

For any parameter 0 ≤ a ≤ 1 and shift L ∈ ℤ, the shifted geometric distribution G_L(s) is nonnegative for every integer s.
-/

/-- The shifted geometric distribution G_L is nonnegative everywhere when 0 ≤ a ≤ 1. -/
lemma shifted_geometric_distribution_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (L s : ℤ) :
    0 ≤ shifted_geometric_distribution a L s := by
  rw [shifted_geometric_distribution]
  split_ifs with h
  · exact mul_nonneg (sub_nonneg.mpr ha1) (zpow_nonneg ha0 (s - L))
  · exact le_refl 0
