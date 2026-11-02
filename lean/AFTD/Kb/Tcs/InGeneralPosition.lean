import AFTD.Prelude

/-!
# in_general_position

Topic: combinatorics   Node: 42549d5fae0a

Provenance: formalization of a published result. Source: arXiv:2610.38368, Section 1

A finite subset S of Euclidean space ℝ^d is in general position if no d + 1 of its points lie in an affine hyperplane (every subset of size d + 1 is affine independent) and no d + 2 of its points lie on a metric sphere.
-/

/-- General position for a finite subset in d-dimensional Euclidean space: no d+1 points in an affine hyperplane and no d+2 on a sphere. -/
def in_general_position (d : ℕ) (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ s ⊆ S, s.card = d + 1 → AffineIndependent ℝ ((↑) : s → EuclideanSpace ℝ (Fin d))) ∧
  (∀ s ⊆ S, s.card = d + 2 → ¬ ∃ (c : EuclideanSpace ℝ (Fin d)) (r : ℝ), ∀ x ∈ s, dist x c = r)
