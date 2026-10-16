import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting

/-!
# simple_graph_wild_number

Topic: graphs   Node: f33af4faf661

Provenance: formalization of a published result. Source: arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Sec. 2 (definition of the wild number wld_γ(G)).

The wild number wld_γ(G) of an edge-coloured graph is the minimum size of a colour-connecting set of edges.
-/

/-- The wild number `wld_γ(G)`: the least size of a finite colour-connecting set (0 if there is none, which cannot happen for a finite connected graph). -/
noncomputable def simple_graph_wild_number {V α : Type*} (G : SimpleGraph V) (γ : G.edgeSet → α) : ℕ :=
  sInf {k | ∃ W : Finset (Sym2 V), W.card = k ∧ simple_graph_is_color_connecting G γ ↑W}
