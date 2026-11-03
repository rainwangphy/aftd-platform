import AFTD.Prelude

/-!
# simple_graph_delete_vertex_preserves_smaller_edge_cliques

Topic: graphs   Node: aa9fed91bf0a

Provenance: helper lemma. Induced-subgraph step in the overlap-to-regularity route for OP-110.

If every edge of a finite simple graph lies in a clique of size k+1, then after deleting any vertex every remaining edge lies in a clique of size k, provided k is at least two.
-/

theorem simple_graph_delete_vertex_preserves_smaller_edge_cliques
    (α : Type) [Fintype α] [DecidableEq α] (G : SimpleGraph α) (k : ℕ) (hk : 2 ≤ k)
    (hclique : ∀ u v, G.Adj u v → ∃ S : Finset α,
      S.card = k + 1 ∧ u ∈ S ∧ v ∈ S ∧ G.IsClique (S : Set α))
    (x : α) :
    ∀ u v : {a : α // a ≠ x}, (G.induce {a | a ≠ x}).Adj u v →
      ∃ S : Finset {a : α // a ≠ x}, S.card = k ∧ u ∈ S ∧ v ∈ S ∧
        (G.induce {a | a ≠ x}).IsClique (S : Set {a : α // a ≠ x}) := by
  intro u v huv
  have hG : G.Adj u.1 v.1 := (SimpleGraph.induce_adj).mp huv
  obtain ⟨S, hScard, huS, hvS, hSclique⟩ := hclique u.1 v.1 hG
  have key : ∃ T : Finset α, T.card = k ∧ u.1 ∈ T ∧ v.1 ∈ T ∧
      (∀ a ∈ T, a ≠ x) ∧ G.IsClique (T : Set α) := by
    by_cases hxS : x ∈ S
    · refine ⟨S.erase x, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_erase_of_mem hxS, hScard]; omega
      · exact Finset.mem_erase.mpr ⟨u.2, huS⟩
      · exact Finset.mem_erase.mpr ⟨v.2, hvS⟩
      · intro a ha; exact (Finset.mem_erase.mp ha).1
      · exact hSclique.subset (by intro a ha; exact (Finset.mem_erase.mp ha).2)
    · have hvA : v.1 ∈ S.erase u.1 := Finset.mem_erase.mpr ⟨hG.ne.symm, hvS⟩
      have hA : (S.erase u.1).card = k := by
        rw [Finset.card_erase_of_mem huS, hScard]; omega
      have hEv : ((S.erase u.1).erase v.1).card = k - 1 := by
        rw [Finset.card_erase_of_mem hvA, hA]
      have hpos : 0 < ((S.erase u.1).erase v.1).card := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      have hw_ne_v : w ≠ v.1 := (Finset.mem_erase.mp hw).1
      have hw_in_A : w ∈ S.erase u.1 := (Finset.mem_erase.mp hw).2
      have hw_ne_u : w ≠ u.1 := (Finset.mem_erase.mp hw_in_A).1
      have hwS : w ∈ S := (Finset.mem_erase.mp hw_in_A).2
      refine ⟨S.erase w, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_erase_of_mem hwS, hScard]; omega
      · exact Finset.mem_erase.mpr ⟨hw_ne_u.symm, huS⟩
      · exact Finset.mem_erase.mpr ⟨hw_ne_v.symm, hvS⟩
      · intro a ha h
        exact hxS (h ▸ (Finset.mem_erase.mp ha).2)
      · exact hSclique.subset (by intro a ha; exact (Finset.mem_erase.mp ha).2)
  obtain ⟨T, hTcard, huT, hvT, hTsub, hTclique⟩ := key
  refine ⟨Finset.subtype (fun a : α => a ≠ x) T, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_subtype, Finset.filter_true_of_mem hTsub, hTcard]
  · exact Finset.mem_subtype.mpr huT
  · exact Finset.mem_subtype.mpr hvT
  · intro a ha b hb hab
    rw [SimpleGraph.induce_adj]
    exact hTclique (Finset.mem_subtype.mp ha) (Finset.mem_subtype.mp hb)
      (fun h => hab (Subtype.ext h))
