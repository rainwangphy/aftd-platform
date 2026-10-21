import AFTD.Prelude

/-!
# spectral_distance_l1

Topic: graphs   Node: b8a358035738

Provenance: formalization of a published result. Source: arXiv:2610.18636 Section 1, p. 3

The Manhattan spectral distance between two eigenvalue sequences of length m is the sum of the absolute differences of their coordinates.
-/

/-- Manhattan spectral distance between two eigenvalue sequences of length m. -/
def spectral_distance_l1 {m : ℕ} (s₁ s₂ : Fin m → ℝ) : ℝ := ∑ i : Fin m, |s₁ i - s₂ i|
