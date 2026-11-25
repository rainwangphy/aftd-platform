import AFTD.Prelude

/-!
# simple_graph_chromatic_index

Topic: graphs   Node: 995304bb4d26

Provenance: formalization of a published result. Source: arXiv:2611.29111 Section 1

The chromatic index chi'(G) of a simple graph G is the minimum number of colors in a proper edge-coloring of G, defined as the infimum of all k such that the line graph of G is k-colorable.
-/

/-- The chromatic index chi'(G) of a simple graph G is the minimum number of colors in a proper edge-coloring of G, defined as the chromatic number of its line graph. -/
noncomputable def simple_graph_chromatic_index {V : Type*} (G : SimpleGraph V) : ℕ := sInf {k : ℕ | G.lineGraph.Colorable k}
