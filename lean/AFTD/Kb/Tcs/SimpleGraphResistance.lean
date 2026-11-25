import AFTD.Prelude

/-!
# simple_graph_resistance

Topic: graphs   Node: abd406e8409f

Provenance: formalization of a published result. Source: arXiv:2611.32276, Section 1

The resistance of a finite graph G is the minimum cardinality of an edge set whose removal leaves a 3-edge-colourable graph.
-/

/-- The resistance of a graph is the minimum number of edges to delete to obtain a 3-edge-colourable graph. -/
noncomputable def simple_graph_resistance {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := sInf {n : ℕ | ∃ s : Finset (Sym2 V), (↑s : Set (Sym2 V)) ⊆ G.edgeSet ∧
    (G.deleteEdges (↑s)).lineGraph.Colorable 3 ∧ s.card = n}
