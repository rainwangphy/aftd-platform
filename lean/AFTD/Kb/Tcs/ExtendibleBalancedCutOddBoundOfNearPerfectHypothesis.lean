import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingSymmetryOfIndependence
import AFTD.Kb.Tcs.FiniteMatchingHasSubmatchingOfEachSmallerSize
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingDeficiencyOddBound
import AFTD.Kb.Tcs.IsKExtendable

/-!
# extendible_balanced_cut_odd_bound_of_near_perfect_hypothesis

Topic: graphs   Node: 7ec7f0869bc9

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/1011.3384.

Under the displayed assumptions and the explicitly assumed near-perfect maximum-matching property, the opposite side of a balanced cut has at most two odd components.
-/

theorem extendible_balanced_cut_odd_bound_of_near_perfect_hypothesis
    (k : ℕ) (hk : 1 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (hcore : ∀ (M N : G.Subgraph), M.IsMatching → N.IsMatching →
      M.verts ⊆ (C : Set (Fin (4*k))) → N.verts ⊆ ((C : Set (Fin (4*k)))ᶜ) →
      (∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k))) → T.edgeSet.ncard ≤ M.edgeSet.ncard) →
      (∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ ((C : Set (Fin (4*k)))ᶜ) → T.edgeSet.ncard ≤ N.edgeSet.ncard) →
      M.edgeSet.ncard = N.edgeSet.ncard → k ≤ M.edgeSet.ncard + 1) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ 2 := by
  set_option maxHeartbeats 4000000 in
    classical
    let R : Finset (Fin (4*k)) := Cᶜ
    have hRcomp : (R : Set (Fin (4*k))) = (C : Set (Fin (4*k)))ᶜ := by ext v; simp [R]
    obtain ⟨M,hM,hMC,hmaxM⟩ := finite_subset_has_maximum_matching G C
    obtain ⟨N,hN,hNR,hmaxNR⟩ := finite_subset_has_maximum_matching G R
    have hNC : N.verts ⊆ (C : Set (Fin (4*k)))ᶜ := by simpa [hRcomp] using hNR
    have hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k)))ᶜ → T.edgeSet.ncard ≤ N.edgeSet.ncard := by
      simpa [hRcomp] using hmaxNR
    have heq := extendible_balanced_cut_matching_symmetry_of_independence k G hext hind C hcard M N hM hN hMC hNC hmaxM hmaxN
    have hm := hcore M N hM hN hMC hNC hmaxM hmaxN heq
    obtain ⟨T,hT,hTM,hTcard⟩ := finite_matching_has_submatching_of_each_smaller_size G M hM (k-1) (by omega)
    have hTC : T.verts ⊆ (C : Set (Fin (4*k))) := Set.Subset.trans hTM.1 hMC
    have hodd := extendible_balanced_cut_matching_deficiency_odd_bound k 1 (by omega) G hext hsep hdegree C hcard T hT hTC (by omega)
    simpa using hodd
