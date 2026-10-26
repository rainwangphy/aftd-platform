import AFTD.Prelude

/-!
# IsPkFree

Topic: graphs   Node: ef3849aa4959

Provenance: formalization of a published result. Source: arXiv:2610.20129 Sec. 1.1

A simple graph G is P_k-free if it contains no induced subgraph isomorphic to the path on k vertices.
-/

/-- A simple graph is P_k-free if it does not contain the path graph on k vertices as an induced subgraph. -/
def IsPkFree {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop := ¬ SimpleGraph.IsIndContained (SimpleGraph.pathGraph k) G
