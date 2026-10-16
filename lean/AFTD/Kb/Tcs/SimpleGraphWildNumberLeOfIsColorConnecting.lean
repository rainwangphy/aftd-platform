import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting

/-!
# simple_graph_wild_number_le_of_is_color_connecting

Topic: graphs   Node: 06d919f462df

Provenance: helper lemma. Sanity lemma for the wild number, arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Sec. 2.

The wild number is at most the size of any colour-connecting set.
-/

theorem simple_graph_wild_number_le_of_is_color_connecting {V α : Type*}
    (G : SimpleGraph V) (γ : G.edgeSet → α) (W : Finset (Sym2 V))
    (hW : simple_graph_is_color_connecting G γ ↑W) :
    simple_graph_wild_number G γ ≤ W.card :=
  Nat.sInf_le ⟨W, rfl, hW⟩
