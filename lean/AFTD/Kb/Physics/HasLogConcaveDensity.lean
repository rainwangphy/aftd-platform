import AFTD.Prelude

/-!
# has_log_concave_density

Topic: classical_mechanics   Node: 6873b4333836

Provenance: formalization of a published result. Source: Saumard & Wellner 2014, "Log-concavity and strong log-concavity: a review", Section 2

A probability measure μ on ℝ has a log-concave density if it is given by μ = volume.withDensity f for some measurable nonnegative function f : ℝ → ℝ with ∫ f = 1 such that f((1 - t)x + ty) ≥ (fx)^(1 - t) * (fy)^t for all x, y ∈ ℝ and t ∈ [0, 1].
-/

/-- A probability measure on the real line has a log-concave density if it is absolutely continuous with respect to Lebesgue measure with a nonnegative log-concave density integrating to 1. -/
def has_log_concave_density (μ : MeasureTheory.Measure ℝ) : Prop := ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫ x, f x) = 1 ∧
    (∀ (x y : ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      (f x) ^ (1 - t) * (f y) ^ t ≤ f ((1 - t) * x + t * y)) ∧
    μ = MeasureTheory.volume.withDensity (fun x ↦ ENNReal.ofReal (f x))
