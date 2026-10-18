import AFTD.Prelude
import AFTD.Kb.Tcs.FiveVertexTStar
import AFTD.Kb.Tcs.FiveVertexTStarAdjDecidable
import AFTD.Kb.Tcs.GraphEdgeConnectivity
import AFTD.Kb.Tcs.OneLeGraphEdgeConnectivityOfConnected
import AFTD.Kb.Tcs.GraphEdgeConnectivityLeMinDegree

/-!
# five_vertex_t_star_connected_edge_connectivity

Topic: graphs   Node: fea82b7e9975

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

The T-graph (edges 0–1, 0–3, 0–4, 1–2) is connected and has edge-connectivity κ' = 1 (it is a tree).
-/

/-- The T-graph is connected and its edge-connectivity is 1, so it is a legitimate test graph for both the hypotheses `0 ≤ κ'` and `1 ≤ κ'`. -/
theorem five_vertex_t_star_connected_edge_connectivity :
    five_vertex_t_star.Connected ∧ graph_edge_connectivity five_vertex_t_star = 1 := by
  have hconn : five_vertex_t_star.Connected := by decide
  refine ⟨hconn, ?_⟩
  have h1 : 1 ≤ graph_edge_connectivity five_vertex_t_star :=
    one_le_graph_edge_connectivity_of_connected five_vertex_t_star hconn
  have h2 : graph_edge_connectivity five_vertex_t_star ≤ 1 := by
    have hle := graph_edge_connectivity_le_minDegree five_vertex_t_star
    have hdeg : five_vertex_t_star.minDegree = 1 := by decide
    omega
  omega
