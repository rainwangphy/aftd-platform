import AFTD.Prelude

/-!
# simple_graph_is_color_connecting

Topic: graphs   Node: 142895c4d97f

Provenance: formalization of a published result. Source: arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Sec. 2 (definition of a color-connecting set; every colouring is taken surjective, so the colours are the colours of edges).

Let γ be an edge colouring of a graph G. A set W of edges of G is colour-connecting if, for every colour c used by γ, the spanning subgraph whose edges are the edges of colour c together with W is connected.
-/

/-- `W` is a colour-connecting set of the edge colouring `γ` of `G`: `W ⊆ E(G)` and, for every colour class, the class together with `W` spans a connected graph (colours are those of edges, so the colouring is read as surjective onto its used colours). -/
def simple_graph_is_color_connecting {V α : Type*} (G : SimpleGraph V) (γ : G.edgeSet → α)
    (W : Set (Sym2 V)) : Prop :=
  W ⊆ G.edgeSet ∧ ∀ e : G.edgeSet,
    (SimpleGraph.fromEdgeSet ({f | ∃ hf : f ∈ G.edgeSet, γ ⟨f, hf⟩ = γ e} ∪ W)).Connected
