import AFTD.Prelude
import AFTD.Kb.Tcs.DescendingBandCost
import AFTD.Kb.Tcs.DescendingBandVulnerability

/-!
# descending_band_points

Topic: information   Node: 9f89e51f5043

Provenance: original. Related work: knowledgebase, OP-1702

For an integer d, descending_band_points d is the set of all pairs (descending_band_cost d r L, descending_band_vulnerability d r L) in ℝ × ℝ for natural numbers r and L satisfying 1 ≤ r and r ≤ L.
-/

/-- Set of descending band points (C_{r,L}, W_{r,L}) for 1 ≤ r ≤ L -/
def descending_band_points (d : ℤ) : Set (ℝ × ℝ) := { (descending_band_cost d r L, descending_band_vulnerability d r L) | (r : ℕ) (L : ℕ) (_ : 1 ≤ r) (_ : r ≤ L) }
