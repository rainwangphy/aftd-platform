import AFTD.Prelude
import AFTD.Kb.Tcs.CrossCutCardGeMinDegreeOfDiamTwo
import AFTD.Kb.Tcs.ExistsMinCutPartition
import AFTD.Kb.Tcs.GraphEdgeConnectivityLeMinDegree
import AFTD.Kb.Tcs.OneLeGraphEdgeConnectivityOfConnected
import AFTD.Kb.Tcs.GraphEdgeConnectivity

/-!
# graph_edge_connectivity_eq_minDegree_of_diam_two

Topic: graphs   Node: 69dd127819dd

Provenance: helper lemma. step towards edge_connectivity_ge_min_degree_mul_lly_lower_bound_two

Plesník's theorem: every finite connected graph of diameter 2 has edge-connectivity equal to its minimum degree, κ'(G) = δ(G).
-/

/-- Plesník's theorem: a finite connected diameter-2 graph has κ'(G) = δ(G). -/
theorem graph_edge_connectivity_eq_minDegree_of_diam_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hd : G.diam = 2) :
    graph_edge_connectivity G = G.minDegree := by
  have : Nontrivial V := SimpleGraph.nontrivial_of_diam_ne_zero (by rw [hd]; decide)
  apply le_antisymm
  · exact graph_edge_connectivity_le_minDegree G
  · obtain ⟨X, hX, hXc, hle⟩ := exists_min_cut_partition G hG
    have hge := cross_cut_card_ge_minDegree_of_diam_two G hG hd X hX hXc
    exact le_trans hge hle
