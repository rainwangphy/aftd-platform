import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.PerfectMatchingBalancedCutInternalEdgeCountsEqual
import AFTD.Kb.Tcs.FiniteMatchingHasSubmatchingOfEachSmallerSize
import AFTD.Kb.Tcs.PerfectMatchingInducedEdgesFormMatching
import AFTD.Kb.Tcs.MatchingEdgesInsideInduced
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# extendible_balanced_cut_maximum_matching_sizes_equal

Topic: graphs   Node: e9eb314e9ede

Provenance: helper lemma. Balanced-cut structural reduction for OP-1957; https://arxiv.org/abs/2611.22690.

For a k-extendible graph of order 4k, maximum matchings on the two halves of a balanced cut have equal sizes if their sizes sum to at least k.
-/

theorem extendible_balanced_cut_maximum_matching_sizes_equal
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) (hext : is_k_extendable G k)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hNC : N.verts ⊆ ((C : Set (Fin (4*k)))ᶜ))
    (hmaxM : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k))) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ ((C : Set (Fin (4*k)))ᶜ) → T.edgeSet.ncard ≤ N.edgeSet.ncard)
    (hsum : k ≤ M.edgeSet.ncard + N.edgeSet.ncard) :
    M.edgeSet.ncard = N.edgeSet.ncard := by
  set_option maxHeartbeats 4000000 in
    classical
    have hCcomp : ((Cᶜ : Finset (Fin (4*k))) : Set (Fin (4*k))) = (C : Set (Fin (4*k)))ᶜ := by ext v; simp
    have hCcompcard : (Cᶜ : Finset (Fin (4*k))).card = 2*k := by
      have h := Finset.card_compl C
      simp only [Fintype.card_fin] at h
      omega
    have hmle : M.edgeSet.ncard ≤ k := by
      have hverts := in1076_matching_twice_card hM
      have hsub := Set.ncard_le_ncard hMC (Set.toFinite _)
      rw [Set.ncard_coe_finset,hcard] at hsub
      omega
    have hnle : N.edgeSet.ncard ≤ k := by
      have hverts := in1076_matching_twice_card hN
      have hsub := Set.ncard_le_ncard hNC (Set.toFinite _)
      rw [← hCcomp,Set.ncard_coe_finset,hCcompcard] at hsub
      omega
    have hMN : Disjoint M.verts N.verts := by
      apply Set.disjoint_left.mpr
      intro v hvM hvN
      exact (hNC hvN) (hMC hvM)
    have hnleM : N.edgeSet.ncard ≤ M.edgeSet.ncard := by
      obtain ⟨M',hM',hM'M,hM'card⟩ :=
        finite_matching_has_submatching_of_each_smaller_size G M hM (k-N.edgeSet.ncard) (by omega)
      have hM'N : Disjoint M'.verts N.verts := hMN.mono_left hM'M.1
      have hT := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard M' N hM' hN hM'N
      have hTk : (M' ⊔ N).edgeSet.ncard = k := by rw [hT.2,hM'card]; omega
      obtain ⟨P,hP,hTP⟩ := hext.2.2 (M' ⊔ N) hT.1 hTk
      have hNP : N ≤ P := le_trans le_sup_right hTP
      obtain ⟨Q,hQ,hQC,hQP,hQE⟩ := perfect_matching_induced_edges_form_matching G P hP C
      have hNsub : N.edgeSet ⊆ (P.induce ((C : Set (Fin (4*k)))ᶜ)).edgeSet := by
        rw [← hCcomp]
        exact matching_edges_inside_induced G N P hNP (Cᶜ : Finset (Fin (4*k))) (by simpa [hCcomp] using hNC)
      have hNbound := Set.ncard_le_ncard hNsub (Set.toFinite _)
      have heq := perfect_matching_balanced_cut_internal_edge_counts_equal G P hP C (by simp only [Fintype.card_fin,hcard]; omega)
      have hQbound := hmaxM Q hQ hQC
      rw [← heq,← hQE] at hNbound
      omega
    have hmleN : M.edgeSet.ncard ≤ N.edgeSet.ncard := by
      obtain ⟨N',hN',hN'N,hN'card⟩ :=
        finite_matching_has_submatching_of_each_smaller_size G N hN (k-M.edgeSet.ncard) (by omega)
      have hMN' : Disjoint M.verts N'.verts := hMN.mono_right hN'N.1
      have hT := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard M N' hM hN' hMN'
      have hTk : (M ⊔ N').edgeSet.ncard = k := by rw [hT.2,hN'card]; omega
      obtain ⟨P,hP,hTP⟩ := hext.2.2 (M ⊔ N') hT.1 hTk
      have hMP : M ≤ P := le_trans le_sup_left hTP
      obtain ⟨Q,hQ,hQC,hQP,hQE⟩ := perfect_matching_induced_edges_form_matching G P hP (Cᶜ : Finset (Fin (4*k)))
      have hMsub := matching_edges_inside_induced G M P hMP C hMC
      have hMbound := Set.ncard_le_ncard hMsub (Set.toFinite _)
      have heq := perfect_matching_balanced_cut_internal_edge_counts_equal G P hP C (by simp only [Fintype.card_fin,hcard]; omega)
      have hQbound := hmaxN Q hQ (by simpa [hCcomp] using hQC)
      rw [← hCcomp,← hQE] at heq
      rw [heq] at hMbound
      omega
    omega
