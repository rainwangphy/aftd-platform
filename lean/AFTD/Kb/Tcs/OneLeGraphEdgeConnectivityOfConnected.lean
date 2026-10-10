import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEdgeConnectivity

/-!
# one_le_graph_edge_connectivity_of_connected

Topic: graphs   Node: 803f2216c9be

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Sec. 1.

A connected graph on at least two vertices has edge-connectivity at least 1.
-/

theorem one_le_graph_edge_connectivity_of_connected {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    1 ≤ graph_edge_connectivity G := by
  dsimp [graph_edge_connectivity]
  apply le_csSup
  · obtain ⟨v⟩ : Nonempty V := inferInstance
    exact ⟨G.degree v, fun k hk ↦ hk.le_degree⟩
  · exact G.isEdgeConnected_one.mpr hG.preconnected
