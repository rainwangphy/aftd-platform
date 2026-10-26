import AFTD.Prelude

/-!
# digraph_is_connected

Topic: graphs   Node: bdb3aeea06bd

Provenance: formalization of a published result. Source: arXiv:2610.18600 Section 1

For a directed graph G : Digraph V on an implicit type {V : Type*}, digraph_is_connected G asserts that the underlying undirected simple graph G.toSimpleGraphInclusive is connected (SimpleGraph.Connected), meaning V is nonempty and any two vertices are reachable by a walk.
-/

/-- A directed graph G : Digraph V is connected if G.toSimpleGraphInclusive is Connected. -/
def digraph_is_connected {V : Type*} (G : Digraph V) : Prop := G.toSimpleGraphInclusive.Connected
