import AFTD.Prelude
import AFTD.Kb.Tcs.KmeansTwoCompetitiveRatios

/-!
# kmeans_two_worst_case_ratio

Topic: algorithms   Node: 7698d56f377b

Provenance: formalization of a published result. Source: arXiv:2611.14573 Section 1.1

The worst-case competitive ratio R₂ of k-means++ for two centers is the supremum of E[Phi₂]/OPT₂(X) over all finite sets X in Euclidean spaces with OPT₂(X) > 0.
-/

/-- The worst-case competitive ratio R₂ of k-means++ for two centers. -/
noncomputable def kmeans_two_worst_case_ratio : ℝ := sSup kmeans_two_competitive_ratios
