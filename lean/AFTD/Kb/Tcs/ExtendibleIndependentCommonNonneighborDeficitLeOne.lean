import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleEqualCutMaximumMatchingDeficiencyAtMostOne
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingSymmetryOfIndependence
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.FiniteMatchingHasSubmatchingOfEachSmallerSize
import AFTD.Kb.Tcs.ExtendibleIndependentAnticompleteMatchingObstructionGeneral
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching
import AFTD.Kb.Tcs.ExtendibleGraphMatchableDeletionInheritsExtendibility
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# extendible_independent_common_nonneighbor_deficit_le_one

Topic: graphs   Node: ff4b632ccc8d

Provenance: helper lemma. Positive-separator transfer for OP-1957; https://arxiv.org/abs/2611.22690.

Under the stated high-degree extendibility and independence assumptions, a nonempty independent U and a disjoint anticomplete W satisfy 2|U|+|W|≤2k+1.
-/

private theorem in1214_match_verts_perfect
    {V : Type*} (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching) :
    ∃ P : (G.induce M.verts).Subgraph, P.IsPerfectMatching := by
  set_option maxHeartbeats 4000000 in
    classical
    let f : M.verts → M.verts := fun v =>
      ⟨Classical.choose (hM v.property), M.edge_vert (Classical.choose_spec (hM v.property)).1.symm⟩
    have hf : ∀ v : M.verts, M.Adj v.val (f v).val := by
      intro v
      exact (Classical.choose_spec (hM v.property)).1
    have hinv : Function.Involutive f := by
      intro v
      apply Subtype.ext
      exact (hM (f v).property).unique (hf (f v)) (hf v).symm
    have hadj : ∀ v : M.verts, (G.induce M.verts).Adj v (f v) := by
      intro v
      exact M.adj_sub (hf v)
    exact perfect_matching_of_adjacency_involution (G.induce M.verts) f hinv hadj

theorem extendible_independent_common_nonneighbor_deficit_le_one
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k)
    (U W : Finset (Fin (4*k))) (hdis : Disjoint U W) (hU : U.Nonempty)
    (hUind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (hanti : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w) :
    2*U.card+W.card ≤ 2*k+1 := by
  set_option maxHeartbeats 4000000 in
    classical
    by_contra hn
    have hUlarge : 3 ≤ U.card := by
      by_contra hs
      have hsmall : U.card ≤ 2 := by omega
      obtain ⟨u,hu⟩ := hU
      have hNbr : G.neighborFinset u ⊆ (U ∪ W)ᶜ := by
        intro v hv
        have huv : G.Adj u v := by simpa using hv
        simp only [Finset.mem_compl,Finset.mem_union]
        intro hvUW
        rcases hvUW with hvU | hvW
        · exact hUind u hu v hvU huv
        · exact hanti u hu v hvW huv
      have hc := Finset.card_le_card hNbr
      have hcomp := Finset.card_compl (U ∪ W)
      have hunion := Finset.card_union_of_disjoint hdis
      have hd := hdegree u
      simp only [Fintype.card_fin] at hcomp
      omega
    have hUk : U.card ≤ k := hind U (by intro x hx y hy hne; exact hUind x hx y hy)
    have hk : 3 ≤ k := by omega
    let q := 2*k+2-2*U.card
    have hq : q+2*U.card=2*k+2 := by dsimp [q]; omega
    have hqpos : 1 ≤ q := by omega
    have hqW : q ≤ W.card := by omega
    obtain ⟨W0,hW0W,hW0card⟩ := Finset.exists_subset_card_eq hqW
    have hW0ne : W0.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w,hw0⟩ := hW0ne
    have hdis0 : Disjoint U W0 := Finset.disjoint_of_subset_right hW0W hdis
    have hwW : w ∈ W := hW0W hw0
    have hnot : ¬ G.neighborFinset w ⊆ W0 := by
      intro hh
      have hc := Finset.card_le_card hh
      have hd := hdegree w
      omega
    obtain ⟨z,hzw,hzW0⟩ := Finset.not_subset.mp hnot
    have hwz : G.Adj w z := by simpa using hzw
    have hzU : z ∉ U := by
      intro hz
      exact hanti z hz w hwW hwz.symm
    have hzUW : z ∉ U ∪ W0 := by simp [hzU,hzW0]
    have hdisz : Disjoint (U ∪ W0) ({z} : Finset (Fin (4*k))) := by
      simp [Finset.disjoint_singleton_right,hzUW]
    let X : Finset (Fin (4*k)) := U ∪ W0 ∪ {z}
    have hXcard : X.card = U.card+W0.card+1 := by
      dsimp [X]
      rw [Finset.card_union_of_disjoint hdisz,Finset.card_union_of_disjoint hdis0]
      simp
    have hXle : X.card ≤ 2*k := by omega
    obtain ⟨R,hXR,hRuniv,hRcard⟩ := Finset.exists_subsuperset_card_eq
      (s:=X) (t:=Finset.univ) (n:=2*k) (Finset.subset_univ X) hXle (by simp; omega)
    let C : Finset (Fin (4*k)) := Rᶜ
    have hCcard : C.card=2*k := by
      have hh := Finset.card_compl R
      simp only [Fintype.card_fin] at hh
      dsimp [C]
      omega
    have hCset : (C : Set (Fin (4*k))) = (R : Set (Fin (4*k)))ᶜ := by ext x; simp [C]
    have hUinR : U ⊆ R := by
      intro x hx
      apply hXR
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    have hWinR : W0 ⊆ R := by
      intro x hx
      apply hXR
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    have hzinR : z ∈ R := by
      apply hXR
      exact Finset.mem_union_right _ (by simp)
    obtain ⟨M,hM,hMC,hmaxM⟩ := finite_subset_has_maximum_matching G C
    obtain ⟨N,hN,hNR,hmaxNR⟩ := finite_subset_has_maximum_matching G R
    have hNC : N.verts ⊆ (C : Set (Fin (4*k)))ᶜ := by simpa [hCset] using hNR
    have hmaxN : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set (Fin (4*k)))ᶜ → T.edgeSet.ncard ≤ N.edgeSet.ncard := by
      simpa [hCset] using hmaxNR
    have heq := extendible_balanced_cut_matching_symmetry_of_independence k G hext hind C hCcard M N hM hN hMC hNC hmaxM hmaxN
    have hnear := extendible_equal_cut_maximum_matching_deficiency_at_most_one k G hext hdegree C hCcard M N hM hN hMC hNC hmaxM hmaxN heq hind
    obtain ⟨T,hT,hTM,hTcard⟩ := finite_matching_has_submatching_of_each_smaller_size G M hM (k-1) (by omega)
    have hTC : T.verts ⊆ (C : Set (Fin (4*k))) := Set.Subset.trans hTM.1 hMC
    let f : Fin 1 → Fin (4*k) := fun _ => w
    let g : Fin 1 → Fin (4*k) := fun _ => z
    obtain ⟨E,hE,hEcard,hEverts⟩ := indexed_disjoint_cross_edges_form_matching G 1 f g
      (by intro i j h; exact Subsingleton.elim i j)
      (by intro i j h; exact Subsingleton.elim i j)
      (by intro i j; exact G.ne_of_adj hwz)
      (by intro i; exact hwz)
    have hTE : Disjoint T.verts E.verts := by
      apply Set.disjoint_left.mpr
      intro x hxT hxE
      have hxC := hTC hxT
      rw [hEverts] at hxE
      rcases hxE with ⟨i,hi⟩ | ⟨i,hi⟩
      · have hxR : x ∈ R := by simpa [f,hi] using hWinR hw0
        simpa [C,hxR] using hxC
      · have hxR : x ∈ R := by simpa [g,hi] using hzinR
        simpa [C,hxR] using hxC
    have hTE' := extendible_graph_matchable_deletion_inherits_extendibility_sup_ncard T E hT hE hTE
    have hTEcard : (T ⊔ E).edgeSet.ncard = k := by rw [hTE'.2,hTcard,hEcard]; omega
    let S : Finset (Fin (4*k)) := (T ⊔ E).verts.toFinset
    have hScard : S.card=2*k := by
      change ((T ⊔ E).verts.toFinset).card = 2*k
      rw [← Set.ncard_eq_toFinset_card']
      simpa only [hTEcard] using (in1076_matching_twice_card hTE'.1).symm
    have hSdis : Disjoint S (U ∪ W0.erase w) := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxUW
      have hxTE : x ∈ (T ⊔ E).verts := by simpa [S] using hxS
      change x ∈ T.verts ∪ E.verts at hxTE
      rcases hxTE with hxT | hxE
      · have hxC := hTC hxT
        have hxR : x ∈ R := by
          rcases Finset.mem_union.mp hxUW with hxU | hxW
          · exact hUinR hxU
          · exact hWinR (Finset.mem_of_mem_erase hxW)
        simpa [C,hxR] using hxC
      · rw [hEverts] at hxE
        rcases hxE with ⟨i,hi⟩ | ⟨i,hi⟩
        · have hxw : x=w := by simpa [f] using hi.symm
          have hwU : w ∉ U := fun hh => Finset.disjoint_left.mp hdis0 hh hw0
          rw [hxw] at hxUW
          simp [hwU] at hxUW
        · have hxz : x=z := by simpa [g] using hi.symm
          rw [hxz] at hxUW
          simp [hzU,hzW0] at hxUW
    have hSMatch : ∃ P : (G.induce {v | v ∈ S}).Subgraph, P.IsPerfectMatching := by
      have hSeq : {v | v ∈ S} = (T ⊔ E).verts := by
        ext v
        simp [S]
      rw [hSeq]
      exact in1214_match_verts_perfect G (T ⊔ E) hTE'.1
    have hW0erase : (W0.erase w).card+1=W0.card := Finset.card_erase_add_one hw0
    have hlarge : Fintype.card (Fin (4*k))-2*k < 2*U.card+(W0.erase w).card := by
      simp only [Fintype.card_fin]
      omega
    have hanti0 : ∀ u ∈ U, ∀ v ∈ W0.erase w, ¬ G.Adj u v := by
      intro u hu v hv
      exact hanti u hu v (hW0W (Finset.mem_of_mem_erase hv))
    have hUW0 : Disjoint U (W0.erase w) := Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hdis0
    exact extendible_independent_anticomplete_matching_obstruction_general G k hext U (W0.erase w) S
      hUW0 hUind hanti0 hSdis hScard hlarge hSMatch
