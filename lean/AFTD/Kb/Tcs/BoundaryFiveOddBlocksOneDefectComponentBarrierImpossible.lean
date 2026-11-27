import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.BoundaryFiveOddBlocksOneDefectUniformCountImpossible
import AFTD.Kb.Tcs.FourBlockAnticompleteShoresSeparatorBound
import AFTD.Kb.Tcs.FactorcriticalAnticompleteOddGroupsBound
import AFTD.Kb.Tcs.OddGroupsSingleNonBlockComponentCount
import AFTD.Kb.Tcs.PairwiseDisjointNonemptyGroupsCardBound
import AFTD.Kb.Tcs.Op1957OneDefectEndpointNumericBounds
import AFTD.Kb.Tcs.Op1957OneDefectPoolNumericBounds
import AFTD.Kb.Tcs.Op1957OneDefectSeparatorNumericBounds
import AFTD.Kb.Tcs.Op1957OneDefectFactorcriticalTwoNumericBounds
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter

/-!
# boundary_five_odd_blocks_one_defect_component_barrier_impossible

Topic: graphs   Node: 0a1e5d6c5996

Provenance: helper lemma. OP-1957: arbitrary-size odd barrier component transfer for the one-defect route.

For the stated 5, 2k−5, c, 2k−c block partition with c odd and at most k, minimum degree 2k+2, the separator property and factor-critical B, an endpoint with at most one C nonneighbor cannot lie in an odd residual component containing at most two A vertices when the indicated odd components and barrier form a forced cross-edge decomposition.
-/

theorem boundary_five_odd_blocks_one_defect_component_barrier_impossible
    {ι : Type*} [DecidableEq ι] (k c : ℕ) (hc : 5 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card = 5) (hC : C.card = c)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C) (hxy : G.Adj x y)
    (hdefect : (C.filter (fun w => ¬ G.Adj x w)).card ≤ 1)
    (X Y S : Finset (Fin (4*k))) (I : Finset ι) (T : ι → Finset (Fin (4*k)))
    (hxX : x ∈ X) (hyY : y ∈ Y) (hXY : Disjoint X Y)
    (hXS : Disjoint X S) (hYS : Disjoint Y S)
    (hXT : ∀ i ∈ I, Disjoint X (T i)) (hYT : ∀ i ∈ I, Disjoint Y (T i))
    (hST : ∀ i ∈ I, Disjoint S (T i))
    (hTT : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (T i) (T j))
    (hoddX : Odd X.card) (hoddY : Odd Y.card) (hoddT : ∀ i ∈ I, Odd (T i).card)
    (hS : S.card = I.card) (hres : (X ∪ Y ∪ I.biUnion T ∪ S).card = 2*k)
    (hcrossXY : ∀ u ∈ X, ∀ v ∈ Y, G.Adj u v → u = x ∧ v = y)
    (hcrossXT : ∀ i ∈ I, ∀ u ∈ X, ∀ v ∈ T i, ¬ G.Adj u v)
    (hcrossYT : ∀ i ∈ I, ∀ u ∈ Y, ∀ v ∈ T i, ¬ G.Adj u v)
    (hcrossTT : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, ¬ G.Adj u v)
    (hbad : (X ∩ A).card ≤ 2) : False := by
  classical
  let U := I.biUnion T
  have hB : B.card=2*k-5 := by omega
  have hD : D.card=2*k-c := by omega
  have hB' : B.card+5=2*k := by omega
  have hD' : D.card+c=2*k := by omega
  have hXU : Disjoint X U := (Finset.disjoint_biUnion_right X I T).mpr hXT
  have hYU : Disjoint Y U := (Finset.disjoint_biUnion_right Y I T).mpr hYT
  have hSU : Disjoint S U := (Finset.disjoint_biUnion_right S I T).mpr hST
  have hantiX : ∀ u ∈ X, ∀ v ∈ U, ¬ G.Adj u v := by
    intro u hu v hv
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
    exact hcrossXT i hi u hu v hvi
  have hantiY : ∀ u ∈ Y, ∀ v ∈ U, ¬ G.Adj u v := by
    intro u hu v hv
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
    exact hcrossYT i hi u hu v hvi
  have hantiXY : ∀ u ∈ X ∩ B, ∀ v ∈ Y ∩ B, ¬ G.Adj u v := by
    intro u hu v hv h
    obtain ⟨huX,huB⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvY,hvB⟩ := Finset.mem_inter.mp hv
    obtain ⟨hux,hvy⟩ := hcrossXY u huX v hvY h
    exact Finset.disjoint_left.mp hAB hx (hux ▸ huB)
  have hne : ∀ i ∈ I, (T i).Nonempty := by
    intro i hi
    apply Finset.card_pos.mp
    obtain ⟨a,ha⟩ := hoddT i hi
    omega
  have hR : I.card ≤ U.card := by
    by_cases hI : I.Nonempty
    · obtain ⟨i,hi⟩ := hI
      have hpool := pairwise_disjoint_nonempty_groups_card_bound I T i hi hTT hne
      have hTi := Finset.card_pos.mpr (hne i hi)
      change (T i).card+I.card ≤ U.card+1 at hpool
      omega
    · have hI0 : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      simp [hI0]
  have hXYU : Disjoint (X ∪ Y) U := Finset.disjoint_union_left.mpr ⟨hXU,hYU⟩
  have hXYUS : Disjoint (X ∪ Y ∪ U) S := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨hXS,hYS⟩,hSU.symm⟩
  have htotal : X.card+Y.card+U.card+S.card=2*k := by
    rw [Finset.card_union_of_disjoint hXYUS,Finset.card_union_of_disjoint hXYU,
      Finset.card_union_of_disjoint hXY] at hres
    omega
  have hparts (P : Finset (Fin (4*k))) := finset_card_eq_sum_four_block_inter A B C D P hAB hAC hAD hBC hBD hCD hcover
  have hXparts := hparts X
  have hYparts := hparts Y
  have hUparts := hparts U
  have htotal' : (X ∩ A).card+(X ∩ B).card+(X ∩ C).card+(X ∩ D).card+
      (Y ∩ A).card+(Y ∩ B).card+(Y ∩ C).card+(Y ∩ D).card+
      (U ∩ A).card+(U ∩ B).card+(U ∩ C).card+(U ∩ D).card+I.card=2*k := by omega
  have hend := op1957_one_defect_endpoint_numeric_bounds k c hc hkc G A B C D X Y U
    hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD hdegree
    x y hx hy hxX hyY hXY hXU hYU hcrossXY hantiX hantiY hdefect
  dsimp only at hend
  obtain ⟨ha0,hc1,hcsmall,hxcount,hycount,hqa0,hqc0,hqd0,hqa1,hqc1⟩ := hend
  have hpoolbounds := op1957_one_defect_pool_numeric_bounds k c hc hkc G A B C D X Y
    hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD hdegree
    I T hoddT hTT hXY hXT hYT hcrossXT hcrossYT hcrossTT
  dsimp only at hpoolbounds
  obtain ⟨hqa2,hqc2,hqd2⟩ := hpoolbounds
  have hcuts := op1957_one_defect_separator_numeric_bounds k c G A B C D X Y U
    hAB hAC hAD hBC hBD hCD hcover hsizeAB hD' hnoCD hsep x y hx hy hxX hyY
    hXY hXU hYU hcrossXY hantiX hantiY
  obtain ⟨hcut0,hcut1⟩ := hcuts
  have hcritnum : 1 ≤ (Y ∩ B).card →
      I.card+(if (X ∩ B).card%2=1 then 1 else 0)+(X ∩ B).card+(Y ∩ B).card+(U ∩ B).card+5 ≤
        2*k+(U ∩ A).card+(U ∩ C).card+(U ∩ D).card := by
    intro hYB
    have hYN : (Y ∩ B).Nonempty := Finset.card_pos.mp (by omega)
    exact (op1957_one_defect_factorcritical_two_numeric_bounds k G A B C D X Y
      hAB hAC hAD hBC hBD hCD hcover hA hsizeAB hnoAB hcritB hdegree
      I T hXY hXT hYT hTT hantiXY hcrossXT hcrossYT hcrossTT hYN hoddT x y hx hy hxX hyY).1
  have hcritgroup : 1 ≤ (Y ∩ B).card → 1 ≤ (U ∩ A).card →
      (X ∩ A).card+(X ∩ C).card+(X ∩ D).card+(Y ∩ A).card+(Y ∩ C).card+(Y ∩ D).card=2 →
      I.card+(if ((U ∩ A).card+(U ∩ C).card+(U ∩ D).card)%2=0 then 1 else 0)+
      (if (X ∩ B).card%2=1 then 1 else 0)+(X ∩ B).card+(Y ∩ B).card+(U ∩ B).card+4 ≤ 2*k := by
    intro hYB hUA _
    have hYN : (Y ∩ B).Nonempty := Finset.card_pos.mp (by omega)
    have hUAN : (U ∩ A).Nonempty := Finset.card_pos.mp (by omega)
    exact (op1957_one_defect_factorcritical_two_numeric_bounds k G A B C D X Y
      hAB hAC hAD hBC hBD hCD hcover hA hsizeAB hnoAB hcritB hdegree
      I T hXY hXT hYT hTT hantiXY hcrossXT hcrossYT hcrossTT hYN hoddT x y hx hy hxX hyY).2 hUAN
  apply boundary_five_odd_blocks_one_defect_uniform_count_impossible
    k c I.card (X ∩ A).card (X ∩ B).card (X ∩ C).card (X ∩ D).card
    (Y ∩ A).card (Y ∩ B).card (Y ∩ C).card (Y ∩ D).card
    (U ∩ A).card (U ∩ B).card (U ∩ C).card (U ∩ D).card
    hkc (by have hh := hUparts; omega) ha0 hbad hc1 hcsmall htotal' hxcount hycount
    hqa0 hqc0 hqd0 hcut0 hqa1 hqc1 hcut1
  · intro hh
    have hp : 0 < (U ∩ A).card := by omega
    exact hqa2 (Finset.card_pos.mp hp)
  · intro hh
    have hp : 0 < (U ∩ C).card := by omega
    exact hqc2 (Finset.card_pos.mp hp)
  · intro hh
    have hp : 0 < (U ∩ D).card := by omega
    exact hqd2 (Finset.card_pos.mp hp)
  · exact hcritnum
  · exact hcritgroup
