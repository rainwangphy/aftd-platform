import AFTD.Prelude
import AFTD.Kb.Tcs.KmeansCostTwo

/-!
# kmeans_opt_two

Topic: algorithms   Node: c16b36bacd39

Provenance: formalization of a published result. Source: arXiv:2611.14573 Section 2

The optimal 2-means cost OPT₂(X) of a finite set of points X is the infimum over all pairs of centers c₁, c₂ of the 2-means cost of X with centers c₁, c₂.
-/

/-- The optimal 2-means cost of a finite point set X. -/
noncomputable def kmeans_opt_two {E : Type*} [NormedAddCommGroup E] (X : Finset E) : ℝ := ⨅ (c₁ : E) (c₂ : E), kmeans_cost_two X c₁ c₂
