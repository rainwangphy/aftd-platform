import AFTD.Prelude

/-!
# are_mutually_unbiased_bases

Topic: quantum   Node: 38b2cfdd1103

Provenance: formalization of a published result. Source: arXiv:2611.18232 Def. 1

Two families of vectors B₁ and B₂ of type Fin d → EuclideanSpace ℂ (Fin d) are mutually unbiased bases if both B₁ and B₂ are orthonormal (Orthonormal ℂ B₁ and Orthonormal ℂ B₂) and for all indices i, j : Fin d, the squared norm of the complex inner product ‖inner ℂ (B₁ i) (B₂ j)‖^2 equals (1 : ℝ) / d.
-/

/-- Two orthonormal bases in EuclideanSpace ℂ (Fin d) are mutually unbiased if all squared overlaps equal 1/d. -/
def are_mutually_unbiased_bases {d : ℕ} (B₁ B₂ : Fin d → EuclideanSpace ℂ (Fin d)) : Prop :=
  Orthonormal ℂ B₁ ∧ Orthonormal ℂ B₂ ∧
  ∀ i j : Fin d, ‖inner ℂ (B₁ i) (B₂ j)‖ ^ 2 = (1 : ℝ) / d
