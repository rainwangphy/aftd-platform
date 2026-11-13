import AFTD.Prelude

/-!
# kmeans_cost_one

Topic: algorithms   Node: 6314550f2d3a

Provenance: formalization of a published result. Source: arXiv:2611.14573 Section 2

The 1-means clustering cost of a finite set of points X in a normed group with respect to a single center c is the sum over x in X of ||x - c||².
-/

/-- The 1-means cost of a finite point set X with respect to a single center c. -/
noncomputable def kmeans_cost_one {E : Type*} [NormedAddCommGroup E] (X : Finset E) (c : E) : ℝ := ∑ x ∈ X, ‖x - c‖^2
