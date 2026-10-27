import AFTD.Prelude
import AFTD.Kb.Tcs.GaleSigmaThree
import AFTD.Kb.Tcs.GaleDistanceGraph
import AFTD.Kb.Tcs.SphereThreePartitionRatioLtThreshold
import AFTD.Kb.Tcs.NonColorableImpPartitionDiamGt
import AFTD.Kb.Tcs.ThresholdGraphFourNotColorable101

/-!
# counterexample_partition_diameter_ratio_three_101

Topic: combinatorics   Node: 8f431d8b16b7

Provenance: formalization of a published result. Source: arXiv:2610.28828 -- A counterexample to Gale's conjecture in $\mathbb{R}^3$, Theorem 2

There exists a finite subset V of 3-dimensional Euclidean space of cardinality 101 and strictly positive diameter such that for every 4-partition of V (given by a map c : V → Fin 4), at least one part has diameter strictly greater than 0.88928 times the diameter of V, and this ratio 0.88928 strictly exceeds the 4-partition diameter ratio of the unit 2-sphere sqrt((3 + sqrt(3)) / 6).
-/

/-- There exists a 101-point subset in 3D Euclidean space whose 4-partition diameter ratio exceeds 0.88928, strictly greater than the unit sphere ratio. -/
theorem counterexample_partition_diameter_ratio_three_101 :
    ∃ V : Finset (EuclideanSpace ℝ (Fin 3)),
      V.card = 101 ∧
      0 < Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))) ∧
      (∀ c : V → Fin 4, ∃ i : Fin 4,
        (88928 / 100000 : ℝ) * Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))) <
          Metric.diam ((Subtype.val : V → EuclideanSpace ℝ (Fin 3)) '' (c ⁻¹' {i}))) ∧
      gale_sigma_three < (88928 / 100000 : ℝ) := by
  obtain ⟨V, hcard, hdiam, hnot⟩ := threshold_graph_four_not_colorable_101
  exact ⟨V, hcard, hdiam, fun c => non_colorable_imp_partition_diam_gt V _ hnot c, sphere_three_partition_ratio_lt_threshold⟩
