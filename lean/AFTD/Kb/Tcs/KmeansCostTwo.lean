import AFTD.Prelude

/-!
# kmeans_cost_two

Topic: algorithms   Node: db1e0d4bc2ea

Provenance: formalization of a published result. Source: arXiv:2611.14573 Section 2

The 2-means clustering cost of a finite set of points X in a normed group with respect to two centers c₁ and c₂ is the sum over x in X of min(||x - c₁||², ||x - c₂||²).
-/

/-- The 2-means cost of a finite point set X with respect to two centers c₁ and c₂. -/
noncomputable def kmeans_cost_two {E : Type*} [NormedAddCommGroup E] (X : Finset E) (c₁ c₂ : E) : ℝ := ∑ x ∈ X, min (‖x - c₁‖^2) (‖x - c₂‖^2)
