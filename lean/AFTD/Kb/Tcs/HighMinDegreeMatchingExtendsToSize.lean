import AFTD.Prelude
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# high_min_degree_matching_extends_to_size

Topic: graphs   Node: ba1ceb4703a2

Provenance: helper lemma. Exposed-barrier reduction for OP-1957; https://arxiv.org/abs/2611.22690.

A matching with at most k edges extends to size k in a sufficiently large graph of minimum degree at least 2k.
-/

theorem high_min_degree_matching_extends_to_size
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hsize : 2*k+2 ≤ Fintype.card V)
    (hdegree : ∀ v, 2*k ≤ (G.neighborFinset v).card)
    (M : G.Subgraph) (hM : M.IsMatching) (hm : M.edgeSet.ncard ≤ k) :
    ∃ N : G.Subgraph, N.IsMatching ∧ M ≤ N ∧ N.edgeSet.ncard = k := by
  set_option maxHeartbeats 4000000 in
    classical
    have aux : ∀ t : ℕ, ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard+t=k →
        ∃ N : G.Subgraph, N.IsMatching ∧ M ≤ N ∧ N.edgeSet.ncard=k := by
      intro t
      induction t with
      | zero =>
        intro M hM ht
        exact ⟨M,hM,le_rfl,by omega⟩
      | succ t ih =>
        intro M hM ht
        let D := M.verts.toFinset
        have hD : D.card = 2*M.edgeSet.ncard := by
          rw [← Set.ncard_eq_toFinset_card']
          exact (in1076_matching_twice_card hM).symm
        have hnot : ¬ (Finset.univ : Finset V) ⊆ D := by
          intro hh
          have hc := Finset.card_le_card hh
          simp only [Finset.card_univ] at hc
          omega
        obtain ⟨u,_,huD⟩ := Finset.not_subset.mp hnot
        have hnotN : ¬ G.neighborFinset u ⊆ D := by
          intro hh
          have hc := Finset.card_le_card hh
          have hd := hdegree u
          omega
        obtain ⟨v,hvN,hvD⟩ := Finset.not_subset.mp hnotN
        have huv : G.Adj u v := by simpa using hvN
        let f : Fin 1 → V := fun _ => u
        let g : Fin 1 → V := fun _ => v
        have hf : Function.Injective f := by intro a b h; exact Subsingleton.elim a b
        have hg : Function.Injective g := by intro a b h; exact Subsingleton.elim a b
        have hfg : ∀ a b, f a ≠ g b := by intro a b; exact G.ne_of_adj huv
        obtain ⟨E,hE,hEcard,hEverts⟩ := indexed_disjoint_cross_edges_form_matching G 1 f g hf hg hfg (by intro a; exact huv)
        have hdis : Disjoint M.verts E.verts := by
          apply Set.disjoint_left.mpr
          intro x hxM hxE
          rw [hEverts] at hxE
          rcases hxE with ⟨i,hi⟩ | ⟨i,hi⟩
          · apply huD
            simpa [D,f,hi] using hxM
          · apply hvD
            simpa [D,g,hi] using hxM
        have hsup := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard M E hM hE hdis
        have hn : (M ⊔ E).edgeSet.ncard+t=k := by rw [hsup.2,hEcard]; omega
        obtain ⟨N,hN,hMN,hNk⟩ := ih (M ⊔ E) hsup.1 hn
        exact ⟨N,hN,le_trans le_sup_left hMN,hNk⟩
    exact aux (k-M.edgeSet.ncard) M hM (by omega)
