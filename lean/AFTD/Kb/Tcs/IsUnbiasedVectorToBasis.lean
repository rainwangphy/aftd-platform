import AFTD.Prelude

/-!
# is_unbiased_vector_to_basis

Topic: quantum   Node: a21b001b6fa1

Provenance: formalization of a published result. Source: arXiv:2611.18232 Sec. II and Sec. IV

A vector v : EuclideanSpace ℂ (Fin d) is unbiased with respect to a family of vectors B : Fin d → EuclideanSpace ℂ (Fin d) if B is orthonormal (Orthonormal ℂ B), v has unit norm (‖v‖ = 1), and for all j : Fin d, the squared norm of the complex inner product ‖inner ℂ v (B j)‖^2 equals (1 : ℝ) / d.
-/

/-- A unit vector is unbiased to an orthonormal basis in EuclideanSpace ℂ (Fin d) if all squared overlaps equal 1/d. -/
def is_unbiased_vector_to_basis {d : ℕ} (v : EuclideanSpace ℂ (Fin d))
    (B : Fin d → EuclideanSpace ℂ (Fin d)) : Prop :=
  Orthonormal ℂ B ∧ ‖v‖ = 1 ∧ ∀ j : Fin d, ‖inner ℂ v (B j)‖ ^ 2 = (1 : ℝ) / d
