import AFTD.Prelude
import AFTD.Kb.Tcs.IsThreeUniform
import AFTD.Kb.Tcs.IsHypergraphFree

/-!
# extremal_number

Topic: combinatorics   Node: 3c19c95285f4

Provenance: formalization of a published result. Source: arXiv:2611.16654:94

For a natural number n and a hypergraph F on vertex type W, the extremal number extremal_number n F is the maximum cardinality of an F-free 3-uniform hypergraph on Fin n (the supremum over all hypergraphs H on Fin n satisfying is_three_uniform H and is_hypergraph_free H F of H.card).
-/

/-- The Turán extremal number ex(n, F) for 3-uniform hypergraphs: the maximum number of edges in an F-free 3-uniform hypergraph on n vertices. -/
noncomputable def extremal_number (n : ℕ) {W : Type*} (F : Finset (Finset W)) : ℕ := open scoped Classical in
  Finset.sup (Finset.univ.filter fun H : Finset (Finset (Fin n)) => is_three_uniform H ∧ is_hypergraph_free H F)
    Finset.card
