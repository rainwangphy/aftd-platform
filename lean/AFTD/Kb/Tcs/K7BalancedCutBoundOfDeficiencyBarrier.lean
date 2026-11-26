import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.BalancedCutFourOddComponentsForceDeficiencyThree
import AFTD.Kb.Tcs.MaximumMatchingSizeFromIndependence
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingSymmetryOfIndependence
import AFTD.Kb.Tcs.InducedOddComponentsLeIndependence
import AFTD.Kb.Tcs.K7AtMostFourOddComponents
import AFTD.Kb.Tcs.K7FourOddGroupsInternalDegreeBound
import AFTD.Kb.Tcs.ExtendibleBalancedCutExposedBarrierOddBound
import AFTD.Kb.Tcs.MatchingVerticesCardAtMostTwiceEdges

/-!
# k7_balanced_cut_bound_of_deficiency_barrier

Topic: graphs   Node: 7453af364bd7

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

Under the displayed extendibility, separator, degree and independence conditions, the matching-deficiency barrier hypothesis implies at most two odd components on a balanced half.
-/

theorem k7_balanced_cut_bound_of_deficiency_barrier
    (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (hext : is_k_extendable G 7)
    (hsep : ∀ S P Q : Finset (Fin 28), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 14 ≤ S.card)
    (hdegree : ∀ v, 15 ≤ (G.neighborFinset v).card)
    (hind : ∀ U : Finset (Fin 28),
      (∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v) → U.card ≤ 7)
    (hbar : ∀ R : Finset (Fin 28), R.card=14 →
      (¬ ∃ N : G.Subgraph, N.IsMatching ∧ N.verts ⊆ (R : Set (Fin 28)) ∧ 5 ≤ N.edgeSet.ncard) →
      ∃ X : Finset (Fin 28), X ⊆ R ∧
        6+X.card ≤ (G.induce {v | v ∈ R ∧ v ∉ X}).oddComponents.ncard)
    (C : Finset (Fin 28)) (hcard : C.card = 14) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ 2 := by
  by_contra hnot
  have h4 : (G.induce {v | v ∉ C}).oddComponents.ncard ≤ 4 :=
    k7_at_most_four_odd_components G hdegree C hcard
  have hodd : 4 ≤ (G.induce {v | v ∉ C}).oddComponents.ncard := by
    let U : Finset (Fin 28) := Cᶜ
    have hUcard : U.card = 14 := by
      have hh := Finset.card_compl C
      simp only [Fintype.card_fin] at hh
      dsimp [U]; omega
    have hs : {v : Fin 28 | v ∈ U} = {v : Fin 28 | v ∉ C} := by ext v; simp [U]
    let H := G.induce {v : Fin 28 | v ∈ U}
    have hHcard : Nat.card {v : Fin 28 | v ∈ U} = 14 := by
      rw [Nat.card_coe_set_eq]
      change (U : Set (Fin 28)).ncard = 14
      rw [Set.ncard_coe_finset, hUcard]
    have hpar := SimpleGraph.odd_ncard_oddComponents H
    rw [hHcard, Nat.odd_iff, Nat.odd_iff] at hpar
    change (G.induce {v | v ∈ U}).oddComponents.ncard % 2 = 1 ↔ 14 % 2 = 1 at hpar
    rw [hs] at hpar
    omega
  let R : Finset (Fin 28) := Cᶜ
  have hRcard : R.card = 14 := by
    have hh := Finset.card_compl C
    simp only [Fintype.card_fin] at hh
    dsimp [R]; omega
  have hR_compl : ((R : Finset (Fin 28)) : Set (Fin 28)) = ((C : Set (Fin 28))ᶜ) := by
    ext x; simp [R]
  obtain ⟨M, hM, hMC, hmaxM⟩ := finite_subset_has_maximum_matching G C
  obtain ⟨N, hN, hNR, hmaxNR⟩ := finite_subset_has_maximum_matching G R
  have hNC : N.verts ⊆ ((C : Set (Fin 28))ᶜ) := by
    rw [← hR_compl]; exact hNR
  have hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ ((C : Set (Fin 28))ᶜ) → T.edgeSet.ncard ≤ N.edgeSet.ncard := by
    intro T hT hTNC
    have hTR : T.verts ⊆ (R : Set (Fin 28)) := by
      rw [hR_compl]; exact hTNC
    exact hmaxNR T hT hTR
  have hk : 2 ≤ 7 := by omega
  have hdef := balanced_cut_four_odd_components_force_deficiency_three 7 hk G hext hsep hdegree hind C hcard M N hM hN hMC hNC hmaxM hmaxN hodd
  have hMsize := maximum_matching_size_from_independence G C M hM hMC hmaxM 7 hind
  have hMcard : M.edgeSet.ncard = 4 := by omega
  have hno5 : ¬ ∃ N' : G.Subgraph, N'.IsMatching ∧ N'.verts ⊆ (R : Set (Fin 28)) ∧ 5 ≤ N'.edgeSet.ncard := by
    intro ⟨N', hN', hN'R, hN'card⟩
    have hle := hmaxNR N' hN' hN'R
    omega
  obtain ⟨X, hXR, hXodd⟩ := hbar R hRcard hno5
  have hXle7 := induced_odd_components_le_independence G {v | v ∈ R ∧ v ∉ X} 7 hind
  have hXcard : X.card = 1 := by
    have hcard_le : X.card ≤ 1 := by omega
    by_cases h0 : X.card = 0
    · rw [Finset.card_eq_zero] at h0
      have hset0 : {v : Fin 28 | v ∈ R ∧ v ∉ X} = {v : Fin 28 | v ∉ C} := by
        ext v; simp [h0, R]
      rw [hset0] at hXodd
      omega
    · omega
  obtain ⟨x0, hx0⟩ := Finset.card_eq_one.mp hXcard
  have hx0_not_C : x0 ∉ C := by
    have hx0R : x0 ∈ R := by
      rw [hx0] at hXR
      exact Finset.singleton_subset_iff.mp hXR
    simp [R] at hx0R
    exact hx0R
  have hhint := k7_four_odd_groups_internal_degree_bound G hdegree C hcard hodd x0 hx0_not_C
  have hsplit := Finset.card_filter_add_card_filter_not (s := G.neighborFinset x0) (· ∈ C)
  have hdeg := hdegree x0
  have hKcard : 11 ≤ ((G.neighborFinset x0).filter (· ∈ C)).card := by omega
  obtain ⟨SM, hSM_sub, hSM_card⟩ := matching_vertices_card_at_most_twice_edges M hM hMcard
  have hexist_u : ∃ u : Fin 28, u ∈ C ∧ u ∉ M.verts ∧ G.Adj u x0 := by
    by_contra! hcontra
    have hsub : (G.neighborFinset x0).filter (· ∈ C) ⊆ SM := by
      intro u hu
      simp only [Finset.mem_filter] at hu
      have hu_not_not : ¬ u ∉ M.verts := by
        intro hunot
        exact hcontra u hu.2 hunot (G.adj_symm ((G.mem_neighborFinset x0 u).mp hu.1))
      have hverts : u ∈ M.verts := by
        by_contra hnv
        exact hu_not_not hnv
      exact hSM_sub u hverts
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨u, huC, huM, huAdj⟩ := hexist_u
  have hexpose : ∃ f : X → Fin 28, Function.Injective f ∧
      ∀ x : X, f x ∈ C ∧ f x ∉ M.verts ∧ G.Adj (f x) x.val := by
    use fun _ => u
    refine ⟨?_, ?_⟩
    · intro ⟨a, ha⟩ ⟨b, hb⟩ _
      rw [hx0, Finset.mem_singleton] at ha hb
      subst ha hb
      rfl
    · intro ⟨a, ha⟩
      rw [hx0, Finset.mem_singleton] at ha
      subst ha
      exact ⟨huC, huM, huAdj⟩
  have hCX : Disjoint C X := by
    rw [hx0, Finset.disjoint_singleton_right]
    exact hx0_not_C
  have hm : M.edgeSet.ncard + 3 = 7 := by omega
  have hXle : X.card ≤ 3 := by omega
  have hbound := extendible_balanced_cut_exposed_barrier_odd_bound 7 3 G hext hsep C X hcard hCX M hM hMC hm hXle hexpose
  have hset_eq : {v : Fin 28 | v ∈ R ∧ v ∉ X} = {v : Fin 28 | v ∉ C ∧ v ∉ X} := by
    ext v; simp [R]
  rw [hset_eq] at hXodd
  have heq : (G.induce {v : Fin (4 * 7) | v ∉ C ∧ v ∉ X}).oddComponents.ncard =
             (G.induce {v : Fin 28 | v ∉ C ∧ v ∉ X}).oddComponents.ncard := rfl
  omega
