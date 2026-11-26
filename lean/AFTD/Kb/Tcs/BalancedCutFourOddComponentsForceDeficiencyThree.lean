import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingSymmetryOfIndependence
import AFTD.Kb.Tcs.FiniteMatchingHasSubmatchingOfEachSmallerSize
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingDeficiencyTwoOddBound
import AFTD.Kb.Tcs.IsKExtendable

/-!
# balanced_cut_four_odd_components_force_deficiency_three

Topic: graphs   Node: acae0bd64b34

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

With the stated extendibility, separator, degree and independence conditions, four odd components force maximum matching deficiency at least three on each side.
-/

theorem balanced_cut_four_odd_components_force_deficiency_three
    (k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (hind : ∀ U : Finset (Fin (4*k)),
      (∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v) → U.card ≤ k)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k)
    (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (hMC : M.verts ⊆ (C : Set (Fin (4*k))))
    (hNC : N.verts ⊆ ((C : Set (Fin (4*k)))ᶜ))
    (hmaxM : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k))) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ ((C : Set (Fin (4*k)))ᶜ) → T.edgeSet.ncard ≤ N.edgeSet.ncard)
    (hodd : 4 ≤ (G.induce {v | v ∉ C}).oddComponents.ncard) :
    M.edgeSet.ncard + 3 ≤ k ∧ N.edgeSet.ncard + 3 ≤ k := by
  set_option maxHeartbeats 4000000 in
    classical
    have heq := extendible_balanced_cut_matching_symmetry_of_independence k G hext hind C hcard M N hM hN hMC hNC hmaxM hmaxN
    have hm : M.edgeSet.ncard + 3 ≤ k := by
      by_contra hn
      have hle : k-2 ≤ M.edgeSet.ncard := by omega
      obtain ⟨T,hT,hTM,hTcard⟩ := finite_matching_has_submatching_of_each_smaller_size G M hM (k-2) hle
      have hTC : T.verts ⊆ (C : Set (Fin (4*k))) := hTM.1.trans hMC
      have hb := extendible_balanced_cut_matching_deficiency_two_odd_bound k G hext hsep hdegree C hcard T hT hTC (by omega)
      omega
    constructor
    · exact hm
    · omega
