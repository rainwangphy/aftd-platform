import AFTD.Prelude

/-!
# points_in_general_position

Topic: online_algorithms   Node: bc6b2c8183f3

Provenance: formalization of a published result. Source: arXiv:2610.23130, Section 1

A set S of points in the real plane ℝ × ℝ is in general position if for all pairwise distinct points p₁, p₂, p₃ in S, the three-element set {p₁, p₂, p₃} is not collinear over ℝ.
-/

/-- A set of points in the plane ℝ × ℝ is in general position if no three distinct points are collinear. -/
def points_in_general_position (S : Set (ℝ × ℝ)) : Prop := ∀ ⦃p₁ p₂ p₃ : ℝ × ℝ⦄, p₁ ∈ S → p₂ ∈ S → p₃ ∈ S →
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ → ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (ℝ × ℝ))
