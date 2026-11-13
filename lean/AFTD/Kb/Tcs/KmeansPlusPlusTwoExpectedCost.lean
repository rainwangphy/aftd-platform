import AFTD.Prelude
import AFTD.Kb.Tcs.KmeansCostOne
import AFTD.Kb.Tcs.KmeansCostTwo

/-!
# kmeans_plus_plus_two_expected_cost

Topic: algorithms   Node: a4d24c2fc5b9

Provenance: formalization of a published result. Source: arXiv:2611.14573 Section 2, Algorithm 1

The expected cost E[Phi₂] of two centers chosen by k-means++ on a finite set X is the average over uniformly chosen first center c₁ in X of the expectation of the 2-means cost when the second center c₂ in X is sampled with probability proportional to ||c₂ - c₁||².
-/

/-- The expected 2-means cost of the two centers chosen by k-means++ on a finite set X. -/
noncomputable def kmeans_plus_plus_two_expected_cost {E : Type*} [NormedAddCommGroup E] (X : Finset E) : ℝ := (X.card : ℝ)⁻¹ * ∑ c₁ ∈ X, ((kmeans_cost_one X c₁)⁻¹ * ∑ c₂ ∈ X, ‖c₂ - c₁‖^2 * kmeans_cost_two X c₁ c₂)
