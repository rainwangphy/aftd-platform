import AFTD.Prelude

/-!
# simple_graph_common_neighbors_card_le_degree_sub_one

Topic: graphs   Node: ac1511b4555d

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number_of_max_degree_le_eleven

The number of common neighbors of two adjacent vertices u and v is at most deg(u) - 1.
-/

/-- The number of common neighbors of two adjacent vertices u and v is at most deg(u) - 1. -/
theorem simple_graph_common_neighbors_card_le_degree_sub_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (h : G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ G.degree u - 1 := by
  have hsub : G.neighborFinset u ∩ G.neighborFinset v ⊆ (G.neighborFinset u).erase v := by
    intro w hw
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hw
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    refine ⟨?_, hw.1⟩
    rintro rfl
    exact G.irrefl hw.2
  calc
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ ((G.neighborFinset u).erase v).card :=
      Finset.card_le_card hsub
    _ = (G.neighborFinset u).card - 1 := by
      rw [Finset.card_erase_of_mem (by simpa using h)]
    _ = G.degree u - 1 := by rw [G.card_neighborFinset_eq_degree]
