import AFTD.Prelude
import AFTD.Kb.Tcs.StarOccupancy

/-!
# star_occupancy_envelope

Topic: graphs   Node: 62c989a498ac

Provenance: formalization of a published result. Source: arXiv:2208.10475v2; OP-542

The star envelope at activity lam is the supremum over all integers k ≥ 1 of the star occupancy star_occupancy k lam.
-/

/-- The supremum of normalized lambda-biased dominating occupancies over all stars K_{1,k} for k ≥ 1. -/
noncomputable def star_occupancy_envelope (lam : ℝ) : ℝ := sSup {star_occupancy k lam | (k : ℕ) (_ : 1 ≤ k)}
