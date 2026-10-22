import AFTD.Prelude

/-!
# bipartite_poset_le

Topic: combinatorics   Node: e9684084f4b8

Provenance: formalization of a published result. Source: arXiv:2610.24774, Section 4.1; Trotter, Combinatorics and Partially Ordered Sets (1992)

For a graph H on α and subsets A, B of α, the height-2 order relation associated to H with bipartition (A, B) has x ≤ y if and only if x = y or (x ∈ A, y ∈ B, and x and y are adjacent in H).
-/

/-- The partial order relation of the height-2 poset associated to a bipartite graph. -/
def bipartite_poset_le {α : Type*} (H : SimpleGraph α) (A B : Set α) (x y : α) : Prop :=
  x = y ∨ (x ∈ A ∧ y ∈ B ∧ H.Adj x y)
