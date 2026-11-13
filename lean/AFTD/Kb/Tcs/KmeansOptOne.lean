import AFTD.Prelude
import AFTD.Kb.Tcs.KmeansCostOne

/-!
# kmeans_opt_one

Topic: algorithms   Node: 7adbf94ffdd1

Provenance: formalization of a published result. Source: arXiv:2611.14573 Section 2

The optimal 1-means cost OPT₁(X) of a finite set of points X is the infimum over all centers c of the 1-means cost of X with center c.
-/

/-- The optimal 1-means cost (variance) of a finite point set X. -/
noncomputable def kmeans_opt_one {E : Type*} [NormedAddCommGroup E] (X : Finset E) : ℝ := ⨅ c : E, kmeans_cost_one X c
