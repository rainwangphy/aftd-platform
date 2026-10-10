import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEdgeConnectivity

/-!
# graph_edge_connectivity_le_minDegree

Topic: graphs   Node: b20300730a31

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Sec. 1 (the classical bound κ(G) ≤ κ'(G) ≤ δ(G) quoted there).

Edge-connectivity is at most the minimum degree, κ'(G) ≤ δ(G) (for at least two vertices).
-/

theorem graph_edge_connectivity_le_minDegree {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    graph_edge_connectivity G ≤ G.minDegree := by
  dsimp [graph_edge_connectivity]
  apply csSup_le
  · exact ⟨0, SimpleGraph.IsEdgeConnected.zero⟩
  · intro k hk
    obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
    rw [hv]
    exact hk.le_degree
