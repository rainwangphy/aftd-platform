import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphIsColorConnectingEdgeSet
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting

/-!
# simple_graph_wild_number_le_card_edge_finset

Topic: graphs   Node: 4da87464741a

Provenance: helper lemma. Sanity lemma for the wild number, arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Sec. 2.

The wild number of a finite connected edge-coloured graph is at most its number of edges.
-/

theorem simple_graph_wild_number_le_card_edge_finset {V α : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (γ : G.edgeSet → α) (hG : G.Connected) :
    simple_graph_wild_number G γ ≤ G.edgeFinset.card := by
  apply Nat.sInf_le
  exact ⟨G.edgeFinset, rfl, by
    rw [SimpleGraph.coe_edgeFinset]; exact simple_graph_is_color_connecting_edge_set G γ hG⟩
