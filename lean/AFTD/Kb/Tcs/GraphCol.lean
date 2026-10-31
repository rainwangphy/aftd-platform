import AFTD.Prelude

/-!
# graph_col

Topic: graphs   Node: 7d8015d50f94

Provenance: formalization of a published result. Source: arXiv:2610.39966 Section 2

The collinear count col(G) of a finite graph G is the number of 3-element subsets {x, y, z} of vertices such that one of the three vertices lies between the other two, i.e., satisfies d(x, y) + d(y, z) = d(x, z).
-/

open scoped Classical in
/-- The number of collinear triples col(G) in a finite graph G. -/
noncomputable def graph_col {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := ((Finset.univ : Finset (Finset V)).filter (fun s =>
    s.card = 3 ∧ ∃ y ∈ s, ∃ x ∈ s, ∃ z ∈ s, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ G.dist x y + G.dist y z = G.dist x z)).card
