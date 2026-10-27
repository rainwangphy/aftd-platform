import AFTD.Prelude

/-!
# star_occupancy

Topic: graphs   Node: af4f9e582174

Provenance: formalization of a published result. Source: arXiv:2208.10475v2; OP-542

The normalized lambda-biased dominating occupancy of the star graph K_{1,k} with k leaves at activity lam > 0, given by (lam * (1 + lam)^k + k * lam^2 * (1 + lam)^(k - 1) + k * lam^k) / ((k + 1) * (lam * (1 + lam)^k + lam^k)).
-/

/-- The normalized lambda-biased dominating occupancy of the star graph K_{1,k}. -/
noncomputable def star_occupancy (k : ℕ) (lam : ℝ) : ℝ := (lam * (1 + lam) ^ k + (k : ℝ) * lam ^ 2 * (1 + lam) ^ (k - 1) + (k : ℝ) * lam ^ k) /
  (((k : ℝ) + 1) * (lam * (1 + lam) ^ k + lam ^ k))
