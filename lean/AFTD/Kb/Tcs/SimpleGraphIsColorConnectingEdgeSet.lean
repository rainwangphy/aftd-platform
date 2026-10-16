import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting

/-!
# simple_graph_is_color_connecting_edge_set

Topic: graphs   Node: 4343ec27d691

Provenance: helper lemma. Sanity lemma for colour-connecting sets, arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Sec. 2 (the bound wld ≤ n − 1 starts from this).

In a connected edge-coloured graph, the whole edge set is colour-connecting.
-/

theorem simple_graph_is_color_connecting_edge_set {V α : Type*} (G : SimpleGraph V)
    (γ : G.edgeSet → α) (hG : G.Connected) : simple_graph_is_color_connecting G γ G.edgeSet := by
  refine ⟨subset_rfl, fun e => ?_⟩
  refine hG.mono ?_
  calc G = SimpleGraph.fromEdgeSet G.edgeSet := (SimpleGraph.fromEdgeSet_edgeSet G).symm
    _ ≤ _ := SimpleGraph.fromEdgeSet_mono Set.subset_union_right
