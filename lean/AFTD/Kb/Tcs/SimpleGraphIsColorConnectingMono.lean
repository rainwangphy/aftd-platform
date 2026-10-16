import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting

/-!
# simple_graph_is_color_connecting_mono

Topic: graphs   Node: 4c2c59d1d6a7

Provenance: helper lemma. Sanity lemma for colour-connecting sets, arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Sec. 2.

A set of edges containing a colour-connecting set is colour-connecting.
-/

theorem simple_graph_is_color_connecting_mono {V α : Type*} (G : SimpleGraph V)
    (γ : G.edgeSet → α) {W W' : Set (Sym2 V)} (hW : simple_graph_is_color_connecting G γ W)
    (hWW' : W ⊆ W') (hW' : W' ⊆ G.edgeSet) : simple_graph_is_color_connecting G γ W' :=
  ⟨hW', fun e => (hW.2 e).mono (SimpleGraph.fromEdgeSet_mono (Set.union_subset_union_right _ hWW'))⟩
