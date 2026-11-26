import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingDeficiencyTwoOddBound
import AFTD.Kb.Tcs.BalancedCutAnticompleteSideHasCrossMatching
import AFTD.Kb.Tcs.ExtendibleBalancedCutEvenComponentOddBound
import AFTD.Kb.Tcs.ExtendibleBalancedCutMaximumMatchingSizesEqual
import AFTD.Kb.Tcs.ExtendibleBalancedCutExposedBarrierOddBound
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.BalancedCutFourOddComponentsForceDeficiencyThree
import AFTD.Kb.Tcs.MaximumMatchingSizeFromIndependence
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingSymmetryOfIndependence
import AFTD.Kb.Tcs.K7FourOddGroupsInternalDegreeBound
import AFTD.Kb.Tcs.FourGroupsWithDoubleEdgeHaveFiveMatching
import AFTD.Kb.Tcs.PairwiseIntersectingEdgesHaveCenter
import AFTD.Kb.Tcs.ForceOneCrossEdgeExtendPerfect
import AFTD.Kb.Tcs.FourOddGroupsStarForcedMatchingObstruction
import AFTD.Kb.Tcs.Op1957OddComponentsAmbientPartition
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# extendible_k7_balanced_cut_odd_component_bound

Topic: graphs   Node: 8664ce5a82a6

Provenance: helper lemma. Boundary test for OP-1957; https://arxiv.org/abs/2611.22690.

In the stated 28-vertex, 7-extendible, high-degree setting with the separator and independence assumptions, any balanced cut has at most two odd components on its opposite side.
-/

theorem extendible_k7_balanced_cut_odd_component_bound
    (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (hext : is_k_extendable G 7)
    (hsep : ∀ S P Q : Finset (Fin 28), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 14 ≤ S.card)
    (hdegree : ∀ v, 15 ≤ (G.neighborFinset v).card)
    (hind : ∀ U : Finset (Fin 28),
      (∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ G.Adj u v) → U.card ≤ 7)
    (C : Finset (Fin 28)) (hcard : C.card = 14) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ 2 := by
  set_option maxHeartbeats 4000000 in
    classical
    by_contra hnot
    let R : Finset (Fin 28) := Cᶜ
    have hRcard : R.card=14 := by
      have hh := Finset.card_compl C
      simp only [Fintype.card_fin] at hh
      dsimp [R]
      omega
    have hRset : (R : Set (Fin 28)) = {v | v ∉ C} := by ext v; simp [R]
    have hRcomp : (R : Set (Fin 28)) = (C : Set (Fin 28))ᶜ := by ext v; simp [R]
    have hRcardtype : Nat.card {v : Fin 28 | v ∉ C} = 14 := by
      rw [Nat.card_coe_set_eq]
      change ((C : Set (Fin 28))ᶜ).ncard = 14
      rw [← hRcomp,Set.ncard_coe_finset,hRcard]
    have hpar := SimpleGraph.odd_ncard_oddComponents (G.induce {v | v ∉ C})
    rw [hRcardtype,Nat.odd_iff,Nat.odd_iff] at hpar
    have hq : 4 ≤ (G.induce {v | v ∉ C}).oddComponents.ncard := by omega
    obtain ⟨M,hM,hMC,hmaxM⟩ := finite_subset_has_maximum_matching G C
    obtain ⟨N,hN,hNR,hmaxNR⟩ := finite_subset_has_maximum_matching G R
    have hNC : N.verts ⊆ (C : Set (Fin 28))ᶜ := by simpa [hRcomp] using hNR
    have hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin 28))ᶜ → T.edgeSet.ncard ≤ N.edgeSet.ncard := by
      simpa [hRcomp] using hmaxNR
    have hdef := balanced_cut_four_odd_components_force_deficiency_three 7 (by omega) G hext hsep hdegree hind C hcard M N hM hN hMC hNC hmaxM hmaxN hq
    have hm_lower := maximum_matching_size_from_independence G C M hM hMC hmaxM 7 hind
    have hm : M.edgeSet.ncard=4 := by omega
    have hn : N.edgeSet.ncard=4 := by
      have heq := extendible_balanced_cut_matching_symmetry_of_independence 7 G hext hind C hcard M N hM hN hMC hNC hmaxM hmaxN
      omega
    let U : Finset (Fin 28) := Cᶜ
    have hUcard : U.card=14 := by
      have hh := Finset.card_compl C
      simp only [Fintype.card_fin] at hh
      dsimp [U]
      omega
    have hodd' : 4 ≤ (G.induce {v | v ∈ U}).oddComponents.ncard := by
      have hs : {v : Fin 28 | v ∈ U} = {v : Fin 28 | v ∉ C} := by ext v; simp [U]
      rw [hs]
      exact hq
    obtain ⟨F,hF,hdis,hcover⟩ := op1957_odd_components_ambient_partition G U 4 (by omega) hodd' (by omega)
    have hmin : ∀ i : Fin 4, 3 ≤ (F i).card := by
      intro i
      have hi := (hF i).2
      have hpos : 0 < (F i).card := hi.pos
      obtain ⟨u,hu⟩ := Finset.card_pos.mp hpos
      have hnot : ¬ G.neighborFinset u ⊆ C := by
        intro h
        have hh := Finset.card_le_card h
        have hd := hdegree u
        omega
      obtain ⟨v,hvN,hvC⟩ := Finset.not_subset.mp hnot
      have huv : G.Adj u v := by simpa using hvN
      have hvU : v ∈ U := by simpa [U] using hvC
      have hvcover : v ∈ Finset.univ.biUnion F := by rw [hcover]; exact hvU
      obtain ⟨j,_,hvj⟩ := Finset.mem_biUnion.mp hvcover
      have hvF : v ∈ F i := by
        by_cases hij : i=j
        · simpa [hij] using hvj
        · exact False.elim ((hdis i j hij).2 u hu v hvj huv)
      have hne : u ≠ v := G.ne_of_adj huv
      have hpair : ({u,v} : Finset (Fin 28)) ⊆ F i := by
        intro x hx
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hh := Finset.card_le_card hpair
      rw [Finset.card_pair hne] at hh
      rw [Nat.odd_iff] at hi
      omega
    have hpairdis : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint F := by
      intro i hi j hj hij
      exact (hdis i j hij).1
    have hsum : ∑ i : Fin 4, (F i).card = 14 := by
      rw [← Finset.card_biUnion hpairdis,hcover,hUcard]
    have hsum' : (F 0).card+(F 1).card+(F 2).card+(F 3).card=14 := by
      simpa [Fin.sum_univ_succ,add_assoc] using hsum
    have hmax : ∀ i : Fin 4, (F i).card ≤ 5 := by
      intro i
      have h0 := hmin 0
      have h1 := hmin 1
      have h2 := hmin 2
      have h3 := hmin 3
      have b0 : (F 0).card ≤ 5 := by omega
      have b1 : (F 1).card ≤ 5 := by omega
      have b2 : (F 2).card ≤ 5 := by omega
      have b3 : (F 3).card ≤ 5 := by omega
      fin_cases i <;> first | exact b0 | exact b1 | exact b2 | exact b3
    have hneigh : ∀ i : Fin 4, ∀ u ∈ F i, ∃ v ∈ F i, G.Adj u v := by
      intro i u hu
      have hnotN : ¬ G.neighborFinset u ⊆ C := by
        intro hh
        have hc := Finset.card_le_card hh
        have hd := hdegree u
        omega
      obtain ⟨v,hvN,hvC⟩ := Finset.not_subset.mp hnotN
      have huv : G.Adj u v := by simpa using hvN
      have hvU : v ∈ U := by simpa [U] using hvC
      have hvcover : v ∈ Finset.univ.biUnion F := by rw [hcover]; exact hvU
      obtain ⟨j,_,hvj⟩ := Finset.mem_biUnion.mp hvcover
      have hvF : v ∈ F i := by
        by_cases hij : i=j
        · simpa [hij] using hvj
        · exact False.elim ((hdis i j hij).2 u hu v hvj huv)
      exact ⟨v,hvF,huv⟩
    have hedge : ∀ i : Fin 4, ∃ a ∈ F i, ∃ b ∈ F i, G.Adj a b := by
      intro i
      have hp : 0 < (F i).card := (hF i).2.pos
      obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
      obtain ⟨b,hb,hab⟩ := hneigh i a ha
      exact ⟨a,ha,b,hb,hab⟩
    have hbig : ∃ z : Fin 4, (F z).card=5 := by
      by_contra hn
      push Not at hn
      have hsmall : ∀ i : Fin 4, (F i).card ≤ 3 := by
        intro i
        have hi := (hF i).2
        rw [Nat.odd_iff] at hi
        have hh := hmax i
        have hne := hn i
        omega
      have h0 := hsmall 0
      have h1 := hsmall 1
      have h2 := hsmall 2
      have h3 := hsmall 3
      omega
    obtain ⟨z,hzcard⟩ := hbig
    have hFR : ∀ i, F i ⊆ R := by
      intro i
      simpa [U,R] using (hF i).1
    have hpair : ∀ i j, i ≠ j → Disjoint (F i) (F j) := by
      intro i j hij
      exact (hdis i j hij).1
    have hnodis : ∀ a ∈ F z, ∀ b ∈ F z, ∀ c ∈ F z, ∀ d ∈ F z,
        G.Adj a b → G.Adj c d → a=c ∨ a=d ∨ b=c ∨ b=d := by
      intro a ha b hb c hc d hd hab hcd
      by_contra hn'
      push Not at hn'
      obtain ⟨P,hP,hPR,hPcard⟩ := four_groups_with_double_edge_have_five_matching G R F hFR hpair hedge z a b c d ha hb hc hd hab hcd hn'.1 hn'.2.1 hn'.2.2.1 hn'.2.2.2
      have hh := hmaxNR P hP hPR
      omega
    obtain ⟨x,hx,hstar⟩ := pairwise_intersecting_edges_have_center G (F z) (by omega) (hneigh z) hnodis
    have hxC : x ∉ C := by
      have hxU := (hF z).1 hx
      simpa [U] using hxU
    let D : Finset (Fin 28) := M.verts.toFinset
    let W : Finset (Fin 28) := (G.neighborFinset x).filter (fun v => v ∉ C)
    have hDcard : D.card=8 := by
      have hh := in1076_matching_twice_card hM
      have hD : D.card = M.verts.ncard := by
        dsimp [D]
        exact (Set.ncard_eq_toFinset_card' M.verts).symm
      rw [hD,← hh,hm]
    have hWcard : W.card ≤ 4 := k7_four_odd_groups_internal_degree_bound G hdegree C hcard hq x hxC
    have hneighbor : ∃ u : Fin 28, u ∈ C ∧ u ∉ M.verts ∧ G.Adj u x := by
      by_contra hn'
      push Not at hn'
      have hsub' : G.neighborFinset x ⊆ D ∪ W := by
        intro v hvN
        by_cases hvC : v ∈ C
        · have hvM : v ∈ M.verts := by
            by_contra hvM
            have hxv : G.Adj x v := by simpa using hvN
            exact hn' v hvC hvM hxv.symm
          exact Finset.mem_union_left W (by simpa [D] using hvM)
        · exact Finset.mem_union_right D (Finset.mem_filter.mpr ⟨hvN,hvC⟩)
      have hc := Finset.card_le_card hsub'
      have hu := Finset.card_union_le D W
      have hd := hdegree x
      omega
    obtain ⟨u,huC,huM,hux⟩ := hneighbor
    obtain ⟨P,T,hP,hT,hTP,hxT,hTsub,hremain⟩ :=
      force_one_cross_edge_extend_perfect 7 3 (by omega) G hext hsep C hcard M hM hMC (by omega) x u hxC huC huM hux
    exact four_odd_groups_star_forced_matching_obstruction G C F
      (by intro i; simpa [U] using (hF i).1) (fun i => (hF i).2)
      hpair (fun i j hij => (hdis i j hij).2) (by simpa [U] using hcover)
      z x hx hzcard hstar P T hP hT hTP hxT hTsub (by omega)
