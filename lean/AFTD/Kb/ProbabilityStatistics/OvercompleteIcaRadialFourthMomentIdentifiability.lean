import AFTD.Prelude

/-!
# overcomplete_ica_radial_fourth_moment_identifiability

Topic: estimation   Node: c0a9c232de4f

Provenance: formalization of a published result. Source: arXiv:2611.11852 Sec. 5

For every natural number q with 2 ≤ q, and all real numbers a₁ and a₂, the fourth moment 8 + 4 * a₁ / (q : ℝ) equals 8 + 4 * a₂ / (q : ℝ) if and only if a₁ = a₂.
-/

/-- The radial fourth moment 8 + 4a/q identifies the source parameter a in the equally spaced overcomplete ICA model. -/
theorem overcomplete_ica_radial_fourth_moment_identifiability (q : ℕ) (hq : 2 ≤ q) (a₁ a₂ : ℝ) : 8 + 4 * a₁ / (q : ℝ) = 8 + 4 * a₂ / (q : ℝ) ↔ a₁ = a₂ := by
  constructor
  · intro h
    have hq_ne : (q : ℝ) ≠ 0 := by positivity
    have h1 : 4 * a₁ / (q : ℝ) = 4 * a₂ / (q : ℝ) := by linarith
    have h2 : 4 * a₁ = 4 * a₂ := (div_left_inj' hq_ne).mp h1
    linarith
  · rintro rfl
    rfl
