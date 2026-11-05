import AFTD.Prelude

/-!
# is_isotropic_position

Topic: combinatorics   Node: 1db75640a027

Provenance: formalization of a published result. Source: arXiv:2611.04644, Appendix A, line 1271

A finite, nonempty subset A of ℝ^d is in isotropic position if (1/|A|) ∑_{a ∈ A} a = 0 and (1/|A|) ∑_{a ∈ A} (a · v)^2 = ‖v‖^2 for all v ∈ ℝ^d.
-/

/-- A finite nonempty subset of Euclidean space is in isotropic position if its mean is zero and its covariance matrix is the identity. -/
def is_isotropic_position (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  A.Nonempty ∧ (∑ a ∈ A, a = 0) ∧ ∀ v : EuclideanSpace ℝ (Fin d), ∑ a ∈ A, (inner (𝕜 := ℝ) a v) ^ 2 = (A.card : ℝ) * ‖v‖ ^ 2
