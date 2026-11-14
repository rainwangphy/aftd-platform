import AFTD.Prelude
import AFTD.Kb.Tcs.ShiftedGeometricDistribution
import AFTD.Kb.Tcs.ShiftedGeometricDistributionNonneg

/-!
# shifted_geometric_distribution_ratio_ge

Topic: information   Node: d7da840fbb73

Provenance: helper lemma. arXiv:2611.16066, Theorem 5.1

For any parameter 0 < a < 1 and shift L ∈ ℤ, the shifted geometric distribution G_L satisfies G_L(s) ≥ a * G_L(s - 1) for all s ∈ ℤ.
-/

/-- The shifted geometric distribution satisfies the ratio inequality G_L(s) ≥ a * G_L(s - 1) for all s. -/
lemma shifted_geometric_distribution_ratio_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (L s : ℤ) :
    a * shifted_geometric_distribution a L (s - 1) ≤ shifted_geometric_distribution a L s := by
  by_cases h : L ≤ s - 1
  · have hLs : L ≤ s := by omega
    rw [shifted_geometric_distribution, if_pos h, shifted_geometric_distribution, if_pos hLs]
    have h_rw : s - L = (s - 1 - L) + 1 := by omega
    rw [h_rw, zpow_add_one₀ (ne_of_gt ha0)]
    ring_nf
    exact le_rfl
  · rw [shifted_geometric_distribution, if_neg h, mul_zero]
    exact shifted_geometric_distribution_nonneg (le_of_lt ha0) (le_of_lt ha1) L s
