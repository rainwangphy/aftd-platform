import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingSymmetryOfIndependence
import AFTD.Kb.Tcs.ExtendibleEqualCutMaximumMatchingDeficiencyAtMostOne
import AFTD.Kb.Tcs.InducedOddComponentsLeUnmatchedMatchingVertices
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.IsKExtendable

/-!
# extendible_high_degree_balanced_cut_odd_bound_no_separator

Topic: graphs   Node: 4c3631a6854f

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/1011.3384.

In the displayed high-degree extendible graph with independence bound k, every balanced half has at most two odd components, with no separate separator assumption.
-/

theorem extendible_high_degree_balanced_cut_odd_bound_no_separator
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ 2 := by
  set_option maxHeartbeats 4000000 in
    classical
    let R : Finset (Fin (4*k)) := Cᶜ
    have hRcard : R.card = 2*k := by
      have hh := Finset.card_compl C
      simp only [Fintype.card_fin] at hh
      dsimp [R]
      omega
    have hRset : (R : Set (Fin (4*k))) = (C : Set (Fin (4*k)))ᶜ := by ext x; simp [R]
    obtain ⟨M,hM,hMC,hmaxM⟩ := finite_subset_has_maximum_matching G C
    obtain ⟨N,hN,hNR,hmaxNR⟩ := finite_subset_has_maximum_matching G R
    have hNC : N.verts ⊆ (C : Set (Fin (4*k)))ᶜ := by simpa [hRset] using hNR
    have hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k)))ᶜ → T.edgeSet.ncard ≤ N.edgeSet.ncard := by
      simpa [hRset] using hmaxNR
    have heq := extendible_balanced_cut_matching_symmetry_of_independence k G hext hind C hcard M N hM hN hMC hNC hmaxM hmaxN
    have hnear := extendible_equal_cut_maximum_matching_deficiency_at_most_one k G hext hdegree C hcard M N hM hN hMC hNC hmaxM hmaxN heq hind
    let D : Finset (Fin (4*k)) := N.verts.toFinset
    have hDR : D ⊆ R := by intro x hx; exact hNR (by simpa [D] using hx)
    have hDcard : D.card=2*N.edgeSet.ncard := by
      dsimp [D]
      rw [← Set.ncard_eq_toFinset_card']
      exact (in1076_matching_twice_card hN).symm
    have hmiss : (R \ D).card ≤ 2 := by
      have hh := Finset.card_sdiff_add_card_eq_card hDR
      omega
    have hodd := induced_odd_components_le_unmatched_matching_vertices G R N hN hNR
    have hRcomp : {v : Fin (4*k) | v ∈ R} = {v | v ∉ C} := by ext x; simp [R]
    rw [hRcomp] at hodd
    change (G.induce {v | v ∉ C}).oddComponents.ncard ≤ (R \ D).card at hodd
    omega
