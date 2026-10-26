import AFTD.Prelude

/-!
# simple_graph_is_minor

Topic: graphs   Node: 89c63149531d

Provenance: formalization of a published result. Source: Diestel, Graph Theory (5th ed.), Section 1.7

A graph H is a minor of a graph G if there exists a family of pairwise disjoint, non-empty, connected subsets B_u of V(G) indexed by u in V(H) such that whenever u and v are adjacent in H, there is an edge in G between B_u and B_v.
-/

/-- H is a graph minor of G if there exist pairwise disjoint connected branch sets in G adjacent whenever H is. -/
def simple_graph_is_minor {U V : Type*} (H : SimpleGraph U) (G : SimpleGraph V) : Prop := ∃ B : U → Set V,
    (∀ u, (G.induce (B u)).Connected) ∧
    (∀ u v, u ≠ v → Disjoint (B u) (B v)) ∧
    (∀ u v, H.Adj u v → ∃ x ∈ B u, ∃ y ∈ B v, G.Adj x y)
