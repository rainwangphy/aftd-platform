import AFTD.Prelude

/-!
# is_induced_minor

Topic: graphs   Node: ca9e0536e418

Provenance: formalization of a published result. Source: arXiv:2611.09627:348

A graph H is an induced minor of G if there exists an induced minor model of H in G, which maps each vertex of H to a connected vertex set in G such that branch sets are pairwise disjoint and adjacency between distinct branch sets matches adjacency in H.
-/

/-- A graph H is an induced minor of G if there exist pairwise disjoint connected branch sets in G whose adjacencies in G reflect the adjacency of H. -/
def is_induced_minor {V_H V_G : Type*} (H : SimpleGraph V_H) (G : SimpleGraph V_G) : Prop := ∃ X : V_H → Set V_G,
    (∀ v, (G.induce (X v)).Connected) ∧
    (∀ u v, u ≠ v → Disjoint (X u) (X v)) ∧
    (∀ u v, u ≠ v → (H.Adj u v ↔ ∃ x ∈ X u, ∃ y ∈ X v, G.Adj x y))
