import AFTD.Prelude

/-!
# subcubic_partition_component_le_three_of_card_le_three

Topic: graphs   Node: 1d5d78c3cac2

Provenance: helper lemma. arXiv:2611.05178 Question 5.4 -- Weighted Max Cut in Subcubic Graphs

Every finite simple graph on at most 3 vertices admits a partition of its vertex set into an independent set L and a complement R = Lᶜ such that every connected component of the induced subgraph G[R] has order at most 3.
-/

/-- Every graph on at most 3 vertices admits an independent set whose complement has all connected components of order at most 3. -/
theorem subcubic_partition_component_le_three_of_card_le_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 3) :
    ∃ L : Finset V, G.induce (L : Set V) = ⊥ ∧
      ∀ C : (G.induce (Lᶜ : Set V)).ConnectedComponent,
        open scoped Classical in Fintype.card C ≤ 3 := by
  use ∅
  constructor
  · ext ⟨x, hx⟩
    simp at hx
  · intro C
    classical
    exact (Fintype.card_subtype_le (· ∈ C)).trans hcard
