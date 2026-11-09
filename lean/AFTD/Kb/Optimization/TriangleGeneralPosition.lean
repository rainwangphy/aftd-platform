import AFTD.Prelude

/-!
# triangle_general_position

Topic: convex_analysis   Node: 0ae2897333d6

Provenance: formalization of a published result. Source: arXiv:2611.08835 Section 4

A finite set of points $P \subset \mathbb{R}^2$ is in general position for the triangle $\triangle$ if no two distinct points share an $x$-coordinate, a $y$-coordinate, or the sum of their coordinates.
-/

/-- General position predicate for points in ℝ² with respect to the triangle Δ. -/
def triangle_general_position (P : Finset (ℝ × ℝ)) : Prop := ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2 ∧ p.1 + p.2 ≠ q.1 + q.2
