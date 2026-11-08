import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsDegenerate

/-!
# simple_graph_is_degenerate_of_induce_compl_singleton

Topic: graphs   Node: 0cb22988a19d

Provenance: helper lemma. step towards tree_edge_disjoint_embedding_two_degenerate_union

If a simple graph G has a vertex v with degree at most k, and the induced subgraph on {v}ᶜ is k-degenerate, then G is k-degenerate.
-/

/-- If removing a vertex v of degree at most k from a simple graph G leaves a k-degenerate induced subgraph on {v}ᶜ, then G is k-degenerate. -/
theorem simple_graph_is_degenerate_of_induce_compl_singleton {V : Type*}
    (G : SimpleGraph V) (v : V) {k : ℕ} (hdeg : (G.neighborSet v).encard ≤ k)
    (hind : simple_graph_is_degenerate (G.induce ({v}ᶜ : Set V)) k) :
    simple_graph_is_degenerate G k := by
  intro s hs
  by_cases hvs : v ∈ s
  · refine ⟨v, hvs, le_trans (Set.encard_le_encard Set.inter_subset_right) hdeg⟩
  · have hs' : (Subtype.val ⁻¹' s : Set ({v}ᶜ : Set V)).Nonempty := by
      obtain ⟨x, hx⟩ := hs
      have hxv : x ≠ v := fun h => hvs (h ▸ hx)
      exact ⟨⟨x, hxv⟩, hx⟩
    obtain ⟨w', hw's, hw'deg⟩ := hind (Subtype.val ⁻¹' s) hs'
    refine ⟨w'.val, hw's, ?_⟩
    have hsub : s ∩ G.neighborSet w'.val ⊆
        Subtype.val '' ((Subtype.val ⁻¹' s) ∩ (G.induce ({v}ᶜ : Set V)).neighborSet w') := by
      intro x hx
      simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet] at hx
      have hxv : x ≠ v := fun h => hvs (h ▸ hx.1)
      refine ⟨⟨x, hxv⟩, ?_, rfl⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, SimpleGraph.mem_neighborSet]
      exact ⟨hx.1, hx.2⟩
    have himg : (Subtype.val '' ((Subtype.val ⁻¹' s) ∩ (G.induce ({v}ᶜ : Set V)).neighborSet w')).encard =
        ((Subtype.val ⁻¹' s) ∩ (G.induce ({v}ᶜ : Set V)).neighborSet w').encard :=
      Subtype.val_injective.encard_image _
    exact le_trans (Set.encard_le_encard hsub) (himg.le.trans hw'deg)
