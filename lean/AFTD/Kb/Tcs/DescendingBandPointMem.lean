import AFTD.Prelude
import AFTD.Kb.Tcs.DescendingBandPoints
import AFTD.Kb.Tcs.DescendingBandVulnerability
import AFTD.Kb.Tcs.DescendingBandCost

/-!
# descending_band_point_mem

Topic: information   Node: d642a5ff5c72

Provenance: helper lemma. OP-1702

For any integer d and natural numbers r and L with 1 ≤ r and r ≤ L, the pair (descending_band_cost d r L, descending_band_vulnerability d r L) belongs to descending_band_points d.
-/

/-- Every descending band set with 1 ≤ r ≤ L generates a point in descending_band_points -/
theorem descending_band_point_mem (d : ℤ) {r L : ℕ} (hr : 1 ≤ r) (hrL : r ≤ L) : (descending_band_cost d r L, descending_band_vulnerability d r L) ∈ descending_band_points d := ⟨r, L, hr, hrL, rfl⟩
