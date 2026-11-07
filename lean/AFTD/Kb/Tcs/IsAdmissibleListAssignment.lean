import AFTD.Prelude

/-!
# is_admissible_list_assignment

Topic: graphs   Node: c9bfc020a573

Provenance: formalization of a published result. Source: arXiv:2611.07924, Section 1

A list assignment L assigning to each vertex of a graph G a finite set of natural numbers is admissible for list size m if every list has cardinality m and the lists assigned to distinct nonadjacent vertices are disjoint.
-/

/-- A list assignment L of m-element subsets of ℕ on a simple graph G is admissible if L(u) and L(v) are disjoint whenever u and v are distinct nonadjacent vertices. -/
def is_admissible_list_assignment {V : Type*}
    (G : SimpleGraph V) (m : ℕ) (L : V → Finset ℕ) : Prop :=
  (∀ v : V, (L v).card = m) ∧ (∀ u v : V, Gᶜ.Adj u v → Disjoint (L u) (L v))
