import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_outside_maximum_packing_card_le_one

Topic: graphs   Node: 3abf0634a17c

Provenance: helper lemma. step towards simple_graph_pair_stable_no_good_finite_kernel

Every triangle in G shares an edge with any maximum packing, so it has at most one vertex outside the packing support.
-/

/-- Every triangle in G shares an edge with any maximum packing, so it has at most one vertex outside the packing support. -/
theorem simple_graph_triangle_outside_maximum_packing_card_le_one
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  (T : Finset (Finset V)) (hT : ∀ t ∈ T, G.IsNClique 3 t)
  (hTp : (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1))
  (hTc : T.card = simple_graph_triangle_packing_number G)
  (t : Finset V) (ht : G.IsNClique 3 t) :
  (t \ T.biUnion id).card ≤ 1 := by
  classical
  obtain ⟨q,hq,hqmeet⟩ := simple_graph_maximum_triangle_packing_edge_meets G T hT hTp hTc t ht
  have hsub : q ∩ t ⊆ t ∩ T.biUnion id := by
    intro x hx
    obtain ⟨hxq,hxt⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨hxt, Finset.mem_biUnion.mpr ⟨q,hq,hxq⟩⟩
  have hcard := Finset.card_le_card hsub
  have hsum := Finset.card_sdiff_add_card_inter t (T.biUnion id)
  rw [ht.card_eq] at hsum
  omega
