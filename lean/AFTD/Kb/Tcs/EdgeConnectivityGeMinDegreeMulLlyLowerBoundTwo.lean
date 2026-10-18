import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureLowerBound
import AFTD.Kb.Tcs.GraphEdgeConnectivity
import AFTD.Kb.Tcs.GraphLlyCurvatureLowerBoundTwoLeOne
import AFTD.Kb.Tcs.CrossingPairsCardEqCrossingEdgesCard
import AFTD.Kb.Tcs.CrossCutCardGeMinDegreeOfDiamTwo
import AFTD.Kb.Tcs.GraphEdgeConnectivityEqMinDegreeOfDiamTwo

/-!
# edge_connectivity_ge_min_degree_mul_lly_lower_bound_two

Topic: graphs   Node: 188ed01dbae9

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Theorem 1.1 (for finite graphs).

Every finite connected graph of diameter 2 has κ'(G) ≥ δ(G) · κ_LLY^(2)(G).
-/

theorem edge_connectivity_ge_min_degree_mul_lly_lower_bound_two
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hd : G.diam = 2) :
    (G.minDegree : ℝ) * graph_lly_curvature_lower_bound G 2 ≤ (graph_edge_connectivity G : ℝ) := by
  have h1 : graph_lly_curvature_lower_bound G 2 ≤ 1 :=
    graph_lly_curvature_lower_bound_two_le_one G hG
  have h2 : graph_edge_connectivity G = G.minDegree :=
    graph_edge_connectivity_eq_minDegree_of_diam_two G hG hd
  rw [h2]
  have h3 : (G.minDegree : ℝ) * graph_lly_curvature_lower_bound G 2 ≤ (G.minDegree : ℝ) * 1 := by
    apply mul_le_mul_of_nonneg_left h1
    exact Nat.cast_nonneg _
  linarith
