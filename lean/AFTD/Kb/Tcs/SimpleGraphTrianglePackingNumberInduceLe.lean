import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_packing_number_induce_le

Topic: graphs   Node: 0ec442a8759a

Provenance: helper lemma. Induced-kernel transport prerequisite for the triangle packing campaign.

The triangle packing number of an induced subgraph is at most that of the whole graph.
-/

theorem simple_graph_triangle_packing_number_induce_le
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    simple_graph_triangle_packing_number (G.induce (S : Set V)) ≤
      simple_graph_triangle_packing_number G := by
  classical
  let f : S ↪ V := Function.Embedding.subtype (fun x => x ∈ S)
  let e : Finset S ↪ Finset V := ⟨fun t => t.map f, Finset.map_injective f⟩
  unfold simple_graph_triangle_packing_number
  apply csSup_le_csSup
  · refine ⟨Fintype.card (Finset V), ?_⟩
    rintro n ⟨T, _, _, rfl⟩
    exact Finset.card_le_univ T
  · exact ⟨0, ∅, by simp, by simp, rfl⟩
  · rintro n ⟨T, hT, hpw, rfl⟩
    refine ⟨T.map e, ?_, ?_, Finset.card_map _⟩
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
      exact (G.isNClique_induce_iff (S : Set V) s 3).mp (hT s hs)
    · intro s hs t ht hne
      obtain ⟨s', hs', rfl⟩ := Finset.mem_map.mp hs
      obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
      have hne' : s' ≠ t' := by intro h; exact hne (congrArg e h)
      have h := hpw hs' ht' hne'
      change ((s'.map f) ∩ (t'.map f)).card ≤ 1
      rw [← Finset.map_inter, Finset.card_map]
      exact h
