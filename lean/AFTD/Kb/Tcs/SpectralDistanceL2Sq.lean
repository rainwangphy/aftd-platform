import AFTD.Prelude

/-!
# spectral_distance_l2_sq

Topic: graphs   Node: 8ca2af067764

Provenance: formalization of a published result. Source: arXiv:2610.18636 Section 1, p. 3

The squared Euclidean spectral distance between two eigenvalue sequences of length m is the sum of the squared differences of their coordinates.
-/

/-- Squared Euclidean spectral distance between two eigenvalue sequences of length m. -/
def spectral_distance_l2_sq {m : ℕ} (s₁ s₂ : Fin m → ℝ) : ℝ := ∑ i : Fin m, (s₁ i - s₂ i) ^ 2
