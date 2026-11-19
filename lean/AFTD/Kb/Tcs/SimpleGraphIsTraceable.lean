import AFTD.Prelude

/-!
# SimpleGraph.IsTraceable

Topic: graphs   Node: b8466edf09cd

Provenance: formalization of a published result. Source: scout/2611-23018-an-infinite-family-of-bipartite-hypotraceable-graphs.md:90

A simple graph G on a vertex type V is traceable if it contains a Hamiltonian path, that is, a walk in G that visits every vertex of V exactly once.
-/

/-- A simple graph is traceable if it admits a Hamiltonian path (a walk visiting each vertex once). -/
def SimpleGraph.IsTraceable {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop := ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian
