import AFTD.Prelude

/-!
# disjoint_copies_graph

Topic: combinatorics   Node: 9e6483bed36b

Provenance: formalization of a published result. Source: arXiv:2611.14160 Section 1

For any natural number m and simple graph G on vertex type V, the graph of m disjoint copies of G has vertex set Fin m × V, with vertices adjacent if and only if they belong to the same copy and are adjacent in G.
-/

/-- Disjoint union of m copies of a simple graph G. -/
def disjoint_copies_graph (m : ℕ) {V : Type*} (G : SimpleGraph V) : SimpleGraph (Fin m × V) := {
  Adj := fun ⟨i, u⟩ ⟨j, v⟩ => i = j ∧ G.Adj u v
  symm := ⟨fun ⟨_, _⟩ ⟨_, _⟩ ⟨h1, h2⟩ => ⟨h1.symm, G.adj_symm h2⟩⟩
  loopless := ⟨fun ⟨_, u⟩ ⟨_, h2⟩ => G.loopless.irrefl u h2⟩
}
