import AFTD.Prelude

/-!
# is_path_graph

Topic: graphs   Node: b3094a2509aa

Provenance: formalization of a published result. Source: arXiv:2611.09627:332

A simple graph is a path graph if it is isomorphic to a standard path graph on n vertices for some n.
-/

/-- A simple graph is a path graph if it is isomorphic to SimpleGraph.pathGraph n for some natural number n. -/
def is_path_graph {V : Type*} (G : SimpleGraph V) : Prop := ∃ n : ℕ, Nonempty (G ≃g SimpleGraph.pathGraph n)
