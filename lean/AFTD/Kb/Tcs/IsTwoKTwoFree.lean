import AFTD.Prelude

/-!
# IsTwoKTwoFree

Topic: graphs   Node: 5136fe1c1400

Provenance: formalization of a published result. Source: arXiv:2611.17183, Section 3

A simple graph G is 2K₂-free if for every pair of edges (a, b) and (c, d) in G, at least one of (a, c), (a, d), (b, c), or (b, d) is an edge of G (that is, G contains no induced 2K₂, the disjoint union of two edges).
-/

/-- A simple graph is 2K₂-free if it contains no induced subgraph isomorphic to 2K₂ (two disjoint edges). -/
def IsTwoKTwoFree {V : Type*} (G : SimpleGraph V) : Prop := ∀ a b c d : V, G.Adj a b → G.Adj c d →
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d
