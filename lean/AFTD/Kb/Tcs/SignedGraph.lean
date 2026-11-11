import AFTD.Prelude

/-!
# SignedGraph

Topic: combinatorics   Node: 5b04d1c80a95

Provenance: formalization of a published result. Source: arXiv:2611.13901, Sec. 2.1

A signed graph on vertex type V consists of an underlying simple graph and a signature assigning to each edge a value in {1, -1}.
-/

/-- A signed graph consists of a simple graph and an edge signature with values in {-1, 1}. -/
structure SignedGraph (V : Type*) where
  graph : SimpleGraph V
  sgn : graph.edgeSet → Int
  sgn_mem : ∀ e, sgn e = 1 ∨ sgn e = -1
