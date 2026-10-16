import AFTD.Prelude

/-!
# simple_graph_edge_is_rich

Topic: graphs   Node: 19c70f01ab49

Provenance: formalization of a published result. Source: arXiv:2610.21868 (Rich-neighbor 5-edge-colorings of subcubic graphs whose 3-vertices induce a matching), Sec. 1 (definition of a rich edge).

In an edge colouring c, an edge e is rich if all edges adjacent to e receive pairwise distinct colours.
-/

/-- `e` is rich for `c`: the edges adjacent to `e` have pairwise distinct colours. -/
def simple_graph_edge_is_rich {V α : Type*} (G : SimpleGraph V) (c : G.edgeSet → α)
    (e : G.edgeSet) : Prop :=
  ∀ f g : G.edgeSet, G.lineGraph.Adj e f → G.lineGraph.Adj e g → f ≠ g → c f ≠ c g
