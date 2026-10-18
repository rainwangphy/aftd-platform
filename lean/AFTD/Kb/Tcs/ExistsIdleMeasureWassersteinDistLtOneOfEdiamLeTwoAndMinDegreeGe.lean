import AFTD.Prelude
import AFTD.Kb.Tcs.EdiamLeTwoOfMinDegreeGeTwoThirds
import AFTD.Kb.Tcs.GraphDistLeTwoOfEdiamLeTwo
import AFTD.Kb.Tcs.GraphEdgeVertexPartition
import AFTD.Kb.Tcs.GraphEdgePartitionCard
import AFTD.Kb.Tcs.GraphMinDegreeEdgePartitionBCardLe
import AFTD.Kb.Tcs.GraphIdleTransportPlanMain
import AFTD.Kb.Tcs.GraphIdleTransportPlanMainMarginals
import AFTD.Kb.Tcs.GraphIdleTransportPlanMainCost
import AFTD.Kb.Tcs.GraphIdlePlanCostLtOne
import AFTD.Kb.Tcs.GraphIdlePlanCostLtOneBoundary
import AFTD.Kb.Tcs.GraphIdlePlanCostLtOneOfBEqZero
import AFTD.Kb.Tcs.GraphEdgePartitionSpecialStructure
import AFTD.Kb.Tcs.GraphIdleTransportPlanSpecial
import AFTD.Kb.Tcs.GraphIdleSpecialCostLtOne
import AFTD.Kb.Tcs.GraphIdleWassersteinLtOneOfEdgePartition
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

Topic: graphs   Node: 330e935244db

Provenance: helper lemma. step towards lly_curvature_pos_of_edge_connectivity_ge

In a connected graph of diameter at most 2 with minimum degree at least 2n/3 − 1, for every edge xy there exists α ∈ (0, 1) such that the Wasserstein distance between idle measures μ_x^α and μ_y^α is strictly less than 1.
-/

/-- In a connected graph of diameter at most 2 with minimum degree at least 2n/3 - 1, for every edge xy there exists α ∈ (0, 1) with W(μ_x^α, μ_y^α) < 1. -/
theorem exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hdiam : G.ediam ≤ 2)
    (hδ : (2 * (Fintype.card V : ℝ)) / 3 - 1 ≤ (G.minDegree : ℝ))
    (x y : V) (hxy : G.Adj x y) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y) < 1 := by
  obtain ⟨A, B, C, P, hA, hB, hC, hP, hcover, -⟩ := graph_edge_vertex_partition G x y hxy
  obtain ⟨hdx, hdy, hn⟩ := graph_edge_partition_card G x y hxy A B C P hA hB hC hP hcover
  refine ⟨1/2, by norm_num, by norm_num, ?_⟩
  exact graph_idle_wasserstein_lt_one_of_edge_partition G x y hxy hdiam hδ A B C P hA hB hC hP hcover hdx hdy hn
