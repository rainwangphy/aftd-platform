import AFTD.Prelude

/-!
# simple_graph_underlying_color_graph

Topic: graphs   Node: 376fc10e641a

Provenance: formalization of a published result. Source: arXiv:2611.18391, Section 2

The underlying simple graph of the color graph of a simple graph G equipped with coloring c : V → α is defined on vertex type Set.range c by SimpleGraph.map (Set.rangeFactorization c) G.
-/

/-- The underlying simple graph of the color graph of a vertex-colored graph (G, c), on vertex set Set.range c. -/
def simple_graph_underlying_color_graph {V α : Type*} (G : SimpleGraph V) (c : V → α) :
    SimpleGraph (Set.range c) := G.map (Set.rangeFactorization c)
