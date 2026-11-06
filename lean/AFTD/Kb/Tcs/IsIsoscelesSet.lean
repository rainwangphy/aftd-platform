import AFTD.Prelude

/-!
# is_isosceles_set

Topic: combinatorics   Node: 50b62b4f107c

Provenance: formalization of a published result. Source: arXiv:2611.05421, Section 1

A finite subset S of a metric space is isosceles if for every three points x, y, z in S, at least two of the three pairwise distances dist(x, y), dist(y, z), and dist(x, z) are equal.
-/

/-- A finite subset of a metric space is isosceles if among any three points at least two pairwise distances are equal. -/
def is_isosceles_set {M : Type*} [MetricSpace M] (S : Finset M) : Prop := ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, dist x y = dist y z ∨ dist y z = dist x z ∨ dist x z = dist x y
