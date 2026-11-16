import AFTD.Prelude

/-!
# IsExpandable

Topic: combinatorics   Node: d7f270a82666

Provenance: formalization of a published result. Source: arXiv:2611.16957, Definition 3.2

A nonempty set X of vertices is expandable in a hypergraph H with edge size bound r if every edge of H has size at most r, and for every set Y disjoint from X with |Y| ≤ 2r, there is an edge of H containing X and disjoint from Y.
-/

/-- A nonempty set X is expandable in hypergraph H with bound r if every edge in H has size at most r and every disjoint set Y of size at most 2r can be avoided by an edge containing X. -/
def IsExpandable {V : Type*} (H : Finset (Finset V)) (r : ℕ) (X : Finset V) : Prop := X.Nonempty ∧ (∀ e ∈ H, e.card ≤ r) ∧ ∀ Y : Finset V, Disjoint Y X → Y.card ≤ 2 * r → ∃ e ∈ H, X ⊆ e ∧ Disjoint e Y
