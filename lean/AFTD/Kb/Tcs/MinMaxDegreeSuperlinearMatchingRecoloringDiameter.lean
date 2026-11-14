import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphReconfigurationDiamGtMatching

/-!
# min_max_degree_superlinear_matching_recoloring_diameter

Topic: graphs   Node: a0447b80a9a3

Provenance: formalization of a published result. Source: arXiv:2611.17022 Sec. 8, Question 3

The minimal maximum degree for super-linear matching recoloring diameter: the infimum sInf of the set of natural numbers Δ satisfying simple_graph_reconfiguration_diam_gt_matching Δ.
-/

/-- The smallest maximum degree Δ for which some graph has (Δ+2)-recoloring diameter > |V| + μ. -/
noncomputable def min_max_degree_superlinear_matching_recoloring_diameter : ℕ := sInf {Δ : ℕ | simple_graph_reconfiguration_diam_gt_matching Δ}
