import AFTD.Prelude

/-!
# subcubic_odd_girth_seven_partition_of_card_le_five

Topic: graphs   Node: e881a69867fa

Provenance: helper lemma. folklore

Every finite simple graph G on at most 5 vertices admits a partition into an independent set L and a subset R = Lᶜ such that every connected component of the induced subgraph G[R] has at most 5 vertices.
-/

open SimpleGraph in
open scoped Classical in
/-- Every finite simple graph with at most 5 vertices trivially admits a partition with component order at most 5. -/
theorem subcubic_odd_girth_seven_partition_of_card_le_five {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 5) :
    ∃ L : Finset V, G.induce (L : Set V) = ⊥ ∧
      ∀ C : (G.induce (Lᶜ : Set V)).ConnectedComponent, Fintype.card C ≤ 5 := by
  use ∅
  constructor
  · ext ⟨x, hx⟩
    simp only [Finset.coe_empty, Set.mem_empty_iff_false] at hx
  · intro C
    have : Fintype.card C ≤ Fintype.card V := Fintype.card_subtype_le _
    omega
