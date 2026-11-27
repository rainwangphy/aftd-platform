import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveOddLargeShoreBOnlyPositiveBarrierImpossible
import AFTD.Kb.Tcs.BoundaryFiveOddBlocksOneDefectUniformCountImpossible
import AFTD.Kb.Tcs.NontrivialFactorcriticalGraphConnected
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.FourBlockAnticompleteShoresSeparatorBound
import AFTD.Kb.Tcs.Op1957FourShoreAggregateTotals
import AFTD.Kb.Tcs.Op1957FourShoreAggregateRepresentativeBounds
import AFTD.Kb.Tcs.FourShoreSaturatedYRootCountBound
import AFTD.Kb.Tcs.FourShoreAggregateBlockCriticality
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_one_defect_empty_barrier_impossible

Topic: graphs   Node: 85693527d381

Provenance: helper lemma. OP-1957: one-defect empty-barrier case

In the displayed five-by-odd partition with degree, separator and factor-criticality hypotheses, two disjoint endpoint shores covering 2k vertices cannot have only the distinguished crossing edge when the first shore meets A in at most two vertices and its root has at most one C nonneighbor.
-/

set_option maxHeartbeats 3000000
open scoped BigOperators

theorem op1957_one_defect_empty_barrier_impossible
    (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D X Y : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (x y : Fin (4*k)) (hxA : x ∈ A) (hyC : y ∈ C) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hXY : Disjoint X Y) (hsize : X.card+Y.card=2*k)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hdefect : (C.filter (fun w => ¬ G.Adj x w)).card ≤ 1)
    (hsmallA : (X ∩ A).card ≤ 2) : False := by
  classical
  let F : Fin 4 → Finset (Fin (4*k)) := in1245_shores X Y
  let L : Fin 4 → Finset (Fin (4*k)) := in1245_blocks A B C D
  let forb : Fin 4 → Fin 4 := ![1,0,3,2]
  have hFdis : ∀ i j, i ≠ j → Disjoint (F i) (F j) := in1245_shores_disjoint X Y hXY
  have hEdis : ∀ i, Disjoint (F i) ∅ := by intro i; simp
  have hBdis : ∀ i j, i ≠ j → Disjoint (L i) (L j) := in1245_blocks_disjoint A B C D hAB hAC hAD hBC hBD hCD
  have hBcover : (Finset.univ : Finset (Fin 4)).biUnion L = Finset.univ := in1245_blocks_cover A B C D hcover
  have hcross4 : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, G.Adj a b →
      (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x) := in1245_shores_cross G X Y x y hcross
  have hEanti : ∀ i, ∀ a ∈ F i, ∀ u ∈ (∅ : Finset (Fin (4*k))), ¬ G.Adj a u := by simp
  have hforbid : ∀ b, ∀ a ∈ L b, ∀ w ∈ L (forb b), ¬ G.Adj a w := by
    intro i a ha v hv h
    fin_cases i <;> simp only [L,forb,in1245_blocks,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at ha hv
    · exact hnoAB a ha v hv h
    · exact hnoAB v hv a ha h.symm
    · exact hnoCD a ha v hv h
    · exact hnoCD v hv a ha h.symm
  have hbf : ∀ b, b ≠ forb b := by intro i; fin_cases i <;> decide
  have hblocks : ∀ b, (L b).card+(L (forb b)).card=2*k := by
    intro i; fin_cases i <;> simp [L,forb,in1245_blocks,hA,hB,hC,hD] <;> omega
  have hmin : ∀ b, 3 ≤ (L b).card := by
    intro i; fin_cases i <;> simp [L,in1245_blocks,hA,hB,hC,hD] <;> omega
  have hV : Fintype.card (Fin (4*k))=2*(2*k) := by simp; omega
  have hxL : x ∈ L 0 := by simpa [L,in1245_blocks] using hxA
  have hyL : y ∈ L 2 := by simpa [L,in1245_blocks] using hyC
  have hrep := op1957_four_shore_aggregate_representative_bounds G F L ∅ x y forb (2*k)
    hFdis hEdis hBdis hBcover (by simp) hxL hyL hcross4 hEanti hbf hforbid hblocks hmin hV hdegree
  have hroot := four_shore_saturated_y_root_count_bound k c hc hkc G A B C D ∅ F x y
    hAB hAC hAD hBC hBD hCD hcover hFdis hEdis (by simp)
    (by simp [F,in1245_shores]) (by simp [F,in1245_shores])
    (by simp [F,in1245_shores]) (by simp [F,in1245_shores])
    hxA (by simpa [F,in1245_shores] using hxX) hyC (by simpa [F,in1245_shores] using hyY)
    hD hcross4 hEanti hnoCD (hdegree y)
  simp [F,in1245_shores] at hroot
  have hB2 : 1 < B.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hB2
  have hconnB : (G.induce {v | v ∈ B}).Connected :=
    nontrivial_factorcritical_graph_connected (G.induce {v | v ∈ B}) hcritB
      ⟨a,ha⟩ ⟨b,hb⟩ (fun h => hab (congrArg Subtype.val h))
  have hcrit := four_shore_aggregate_block_criticality G F L ∅ x y (∅ : Finset (Fin 0)) (fun i => Fin.elim0 i)
    hFdis hEdis hBdis hBcover (by simp) hxL hyL hcross4 hEanti (by simp) (by simp) (by simp) (by simp) hcritB hconnB
  have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hAB hxA h
  have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
  have hxD : x ∉ D := fun h => Finset.disjoint_left.mp hAD hxA h
  have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hCD hyC h
  have hxY : x ∉ Y := fun h => Finset.disjoint_left.mp hXY hxX h
  have hbudget := anticomplete_neighbor_defect_bound G B x hxB (hnoAB x hxA) (2*k+4) 2
    (by simp [hB]; omega) (by have := hdegree x; omega)
  have hyQB : y ∈ Y \ B := Finset.mem_sdiff.mpr ⟨hyY,hyB⟩
  have hsub : ((Y \ B).erase y) ⊆ (((Finset.univ \ B).erase x) \ G.neighborFinset x) := by
    intro v hv
    have hv' := Finset.mem_erase.mp hv
    have hvY := (Finset.mem_sdiff.mp hv'.2).1
    have hvB := (Finset.mem_sdiff.mp hv'.2).2
    have hvx : v ≠ x := fun h => hxY (h ▸ hvY)
    have hnot : ¬ G.Adj x v := fun h => hv'.1 (hcross x hxX v hvY h).2
    simp only [Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hvx,hvB⟩,hnot⟩
  have hYother : (Y \ B).card ≤ 3 := by
    have hh := Finset.card_le_card hsub
    have he := Finset.card_erase_add_one hyQB
    omega
  have hYsum := finset_card_eq_sum_four_block_inter A B C D Y hAB hAC hAD hBC hBD hCD hcover
  have hYdiff := Finset.card_inter_add_card_sdiff Y B
  have hxcount : (Y ∩ A).card+(Y ∩ C).card+(Y ∩ D).card ≤ 3 := by omega
  let P := C.filter (fun w => ¬ G.Adj x w)
  have hYcsub : Y ∩ C ⊆ insert y P := by
    intro v hv
    have hvY := (Finset.mem_inter.mp hv).1
    have hvC := (Finset.mem_inter.mp hv).2
    by_cases hvy : v=y
    · simp [hvy]
    · have hnot : ¬ G.Adj x v := fun h => hvy (hcross x hxX v hvY h).2
      simp [P,hvC,hnot]
  have hcsmall : (Y ∩ C).card ≤ 2 := by
    have hh := Finset.card_le_card hYcsub
    have hi := Finset.card_insert_le y P
    dsimp [P] at hh hi
    omega
  have ha0 : 1 ≤ (X ∩ A).card := Finset.card_pos.mpr ⟨x,Finset.mem_inter.mpr ⟨hxX,hxA⟩⟩
  have hc1 : 1 ≤ (Y ∩ C).card := Finset.card_pos.mpr ⟨y,Finset.mem_inter.mpr ⟨hyY,hyC⟩⟩
  have hXsum := finset_card_eq_sum_four_block_inter A B C D X hAB hAC hAD hBC hBD hCD hcover
  have htotal : (X ∩ A).card+(X ∩ B).card+(X ∩ C).card+(X ∩ D).card+
      (Y ∩ A).card+(Y ∩ B).card+(Y ∩ C).card+(Y ∩ D).card=2*k := by omega
  have hE1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hE3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  have hE2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hrepA0 : 2 ≤ (X ∩ A).card → (Y ∩ A).card+(Y ∩ C).card+(Y ∩ D).card ≤ 2 := by
    intro hh
    have hr := hrep 0 0 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    dsimp at hr
    simp [hE1,F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hA] at hr
    omega
  have hrepC0 : 1 ≤ (X ∩ C).card → (Y ∩ A).card+(Y ∩ B).card+(Y ∩ C).card+3 ≤ c := by
    intro hh
    have hr := hrep 0 2 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    dsimp at hr
    simp [hE3,F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hC] at hr
    omega
  have hrepD0 : 1 ≤ (X ∩ D).card → (Y ∩ A).card+(Y ∩ B).card+(Y ∩ D).card+c+3 ≤ 2*k := by
    intro hh
    have hr := hrep 0 3 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    dsimp at hr
    simp [hE2,F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hD] at hr
    omega
  have hrepA1 : 1 ≤ (Y ∩ A).card → (X ∩ A).card+(X ∩ C).card+(X ∩ D).card ≤ 2 := by
    intro hh
    have hr := hrep 1 0 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    dsimp at hr
    simp [hE1,F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hA] at hr
    omega
  have hrepC1 : 2 ≤ (Y ∩ C).card → (X ∩ A).card+(X ∩ B).card+(X ∩ C).card+3 ≤ c := by
    intro hh
    have hr := hrep 1 2 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    dsimp at hr
    simp [hE3,F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hC] at hr
    omega
  have hcut0 : 1 ≤ (X ∩ D).card → (X ∩ D).card+(Y ∩ B).card+(Y ∩ D).card+c ≤ 2*k := by
    intro hh
    have hd : (D ∩ X).Nonempty := by
      apply Finset.card_pos.mp
      simpa [Finset.inter_comm] using hh
    have hdxy : Disjoint X (Y.erase y) := Finset.disjoint_of_subset_right (Finset.erase_subset y Y) hXY
    have hantixy : ∀ u ∈ X, ∀ v ∈ Y.erase y, ¬ G.Adj u v := by
      intro u hu v hv h
      have hv' := Finset.mem_erase.mp hv
      exact hv'.1 (hcross u hu v hv'.2 h).2
    have hWB : B ∩ Y.erase y = B ∩ Y := by
      ext v; simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hb,_,hy⟩; exact ⟨hb,hy⟩
      · rintro ⟨hb,hy⟩; exact ⟨hb,fun h => hyB (h ▸ hb),hy⟩
    have hWD : D ∩ Y.erase y = D ∩ Y := by
      ext v; simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hd,_,hy⟩; exact ⟨hd,hy⟩
      · rintro ⟨hd,hy⟩; exact ⟨hd,fun h => hyD (h ▸ hd),hy⟩
    have hh' := four_block_anticomplete_shores_separator_bound G A B C D
      hAB hAC hAD hBC hBD hCD hcover ⟨y,hyC⟩ (2*k) (by omega) hnoCD hsep X (Y.erase y) hdxy hantixy hd
    rw [hWB,hWD,hD] at hh'
    rw [Finset.inter_comm D X,Finset.inter_comm B Y,Finset.inter_comm D Y] at hh'
    omega
  have hcut1 : 1 ≤ (Y ∩ D).card → (Y ∩ D).card+(X ∩ B).card+(X ∩ D).card+c ≤ 2*k := by
    intro hh
    have hd : (D ∩ Y).Nonempty := by
      apply Finset.card_pos.mp
      simpa [Finset.inter_comm] using hh
    have hdyx : Disjoint Y (X.erase x) := Finset.disjoint_of_subset_right (Finset.erase_subset x X) hXY.symm
    have hantiyx : ∀ u ∈ Y, ∀ v ∈ X.erase x, ¬ G.Adj u v := by
      intro u hu v hv h
      have hv' := Finset.mem_erase.mp hv
      exact hv'.1 (hcross v hv'.2 u hu h.symm).1
    have hWB : B ∩ X.erase x = B ∩ X := by
      ext v; simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hb,_,hx⟩; exact ⟨hb,hx⟩
      · rintro ⟨hb,hx⟩; exact ⟨hb,fun h => hxB (h ▸ hb),hx⟩
    have hWD : D ∩ X.erase x = D ∩ X := by
      ext v; simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hd,_,hx⟩; exact ⟨hd,hx⟩
      · rintro ⟨hd,hx⟩; exact ⟨hd,fun h => hxD (h ▸ hd),hx⟩
    have hh' := four_block_anticomplete_shores_separator_bound G A B C D
      hAB hAC hAD hBC hBD hCD hcover ⟨y,hyC⟩ (2*k) (by omega) hnoCD hsep Y (X.erase x) hdyx hantiyx hd
    rw [hWB,hWD,hD] at hh'
    rw [Finset.inter_comm D Y,Finset.inter_comm B X,Finset.inter_comm D X] at hh'
    omega
  have hcrit' : ((X ∩ B).card+(Y ∩ B).card+5 < 2*k →
      (X ∩ B).card+(Y ∩ B).card+6 ≤ 2*k) ∧
    ((X ∩ B).card+(Y ∩ B).card+5 = 2*k →
      (if 1 ≤ (X ∩ B).card then 1 else 0)+(if 1 ≤ (Y ∩ B).card then 1 else 0) ≤ 1) := by
    dsimp at hcrit
    simp only [Fin.sum_univ_four] at hcrit
    simp [F,L,in1245_shores,in1245_blocks,hB] at hcrit
    have hz0 : (1 ≤ (X ∩ B).card) ↔ (X ∩ B).Nonempty := by rw [←Finset.card_pos]; omega
    have hz1 : (1 ≤ (Y ∩ B).card) ↔ (Y ∩ B).Nonempty := by rw [←Finset.card_pos]; omega
    simp only [hz0,hz1]
    omega
  have hcritpar : 1 ≤ (Y ∩ B).card →
      (if (X ∩ B).card%2=1 then 1 else 0)+(X ∩ B).card+(Y ∩ B).card+5 ≤ 2*k := by
    intro hb1
    by_cases hlt : (X ∩ B).card+(Y ∩ B).card+5 < 2*k
    · have hh := hcrit'.1 hlt
      split_ifs <;> omega
    · have htot := op1957_four_shore_aggregate_totals F L ∅ hFdis hEdis hBdis hBcover (by simp)
      have hh := htot.2.1 1
      simp [F,L,in1245_shores,in1245_blocks,Fin.sum_univ_four,hB] at hh
      have heq : (X ∩ B).card+(Y ∩ B).card+5=2*k := by omega
      have hc := hcrit'.2 heq
      have hx0 : (X ∩ B).card=0 := by split_ifs at hc <;> omega
      simp [hx0] at *
      omega
  apply boundary_five_odd_blocks_one_defect_uniform_count_impossible
    k c 0 (X ∩ A).card (X ∩ B).card (X ∩ C).card (X ∩ D).card
      (Y ∩ A).card (Y ∩ B).card (Y ∩ C).card (Y ∩ D).card 0 0 0 0
      hkc (by simp) ha0 hsmallA hc1 (by simpa using hcsmall) (by simpa using htotal)
      (by simpa using hxcount) (by simpa using hroot) (by simpa using hrepA0)
      (by simpa using hrepC0) (by simpa using hrepD0) (by simpa using hcut0)
      (by simpa using hrepA1) (by simpa using hrepC1) (by simpa using hcut1)
  · simp
  · simp
  · simp
  · simpa using hcritpar
  · simp
