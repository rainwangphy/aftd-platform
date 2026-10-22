import AFTD.Prelude

/-!
# metric_distortion_1d_ratio

Topic: social_choice   Node: 1c2fbc284221

Provenance: formalization of a published result. Source: arXiv:2610.26535 Lemma 5, Equation (1)

For natural numbers n1 and n2, metric_distortion_1d_ratio n1 n2 is the real number ((n1 : ℝ) + 2 * (n2 : ℝ)) / (n1 : ℝ).
-/

/-- The distortion ratio expression ((n1 : ℝ) + 2 * (n2 : ℝ)) / (n1 : ℝ) for voter counts n1 and n2. -/
noncomputable def metric_distortion_1d_ratio (n₁ n₂ : ℕ) : ℝ :=
  ((n₁ : ℝ) + 2 * (n₂ : ℝ)) / (n₁ : ℝ)
