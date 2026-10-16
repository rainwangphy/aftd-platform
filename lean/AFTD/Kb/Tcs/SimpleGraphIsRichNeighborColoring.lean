import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# simple_graph_is_rich_neighbor_coloring

Topic: graphs   Node: 95ae9bbe237b

Provenance: formalization of a published result. Source: arXiv:2610.21868 (Rich-neighbor 5-edge-colorings of subcubic graphs whose 3-vertices induce a matching), Sec. 1 (definition of a rich-neighbor edge-coloring).

A proper edge colouring is a rich-neighbor edge colouring if every non-isolated edge (one with at least one adjacent edge) is adjacent to a rich edge.
-/

/-- A proper edge colouring (a colouring of the line graph) in which every non-isolated edge is adjacent to a rich edge. -/
def simple_graph_is_rich_neighbor_coloring {V α : Type*} (G : SimpleGraph V)
    (c : G.lineGraph.Coloring α) : Prop :=
  ∀ e : G.edgeSet, (∃ f, G.lineGraph.Adj e f) →
    ∃ f, G.lineGraph.Adj e f ∧ simple_graph_edge_is_rich G c f
