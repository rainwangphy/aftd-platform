import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphEdgeConnectivity
import AFTD.Kb.Tcs.GraphLlyCurvaturePosOfWassersteinLtOne
import AFTD.Kb.Tcs.EdiamLeTwoOfMinDegreeGeTwoThirds
import AFTD.Kb.Tcs.ExistsIdleMeasureWassersteinDistLtOneOfEdiamLeTwoAndMinDegreeGe
import AFTD.Kb.Tcs.GraphEdgeConnectivityLeMinDegree
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphWassersteinDist

/-!
# lly_curvature_pos_of_edge_connectivity_ge

Topic: graphs   Node: 261ff8f9122b

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Theorem 1.3. Gives c(n) ≤ ⌈2n/3 − 1⌉ in OP-165.

If a finite connected graph on n vertices has edge-connectivity κ'(G) ≥ 2n/3 − 1, then every edge xy has κ_LLY(x, y) > 0.
-/

theorem lly_curvature_pos_of_edge_connectivity_ge
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hk : (2 * (Fintype.card V : ℝ)) / 3 - 1 ≤ (graph_edge_connectivity G : ℝ))
    (x y : V) (hxy : G.Adj x y) : 0 < graph_lly_curvature G x y := by
  have : Nontrivial V := ⟨x, y, hxy.ne⟩
  have hδ : (2 * (Fintype.card V : ℝ)) / 3 - 1 ≤ (G.minDegree : ℝ) := by
    have h_le : (graph_edge_connectivity G : ℝ) ≤ (G.minDegree : ℝ) := by
      exact_mod_cast (graph_edge_connectivity_le_minDegree G)
    exact le_trans hk h_le
  have hdiam : G.ediam ≤ 2 := ediam_le_two_of_minDegree_ge_two_thirds G hG hδ
  obtain ⟨α, hα0, hα1, hW⟩ := exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge G hG hdiam hδ x y hxy
  exact graph_lly_curvature_pos_of_wasserstein_lt_one G hG x y hxy α hα0 hα1 hW
