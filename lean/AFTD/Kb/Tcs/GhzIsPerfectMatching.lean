import AFTD.Prelude

/-!
# ghz_is_perfect_matching

Topic: quantum   Node: 9ee3be803a61

Provenance: formalization of a published result. Source: scout/2610-22190-connectivity-bounds-for-ghz-graphs.md:149

A set of edges M : Finset (Sym2 V) is a perfect matching in a simple graph G on a finite type V if every edge in M belongs to the edge set of G and every vertex v : V is incident to a unique edge in M (there exists a unique e in M such that v ∈ e).
-/

/-- A set of edges is a perfect matching in G if every edge in M is an edge of G and every vertex in V is incident to a unique edge in M. -/
def ghz_is_perfect_matching {V : Type*} [Fintype V] (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop := (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ v : V, ∃! e ∈ M, v ∈ e
