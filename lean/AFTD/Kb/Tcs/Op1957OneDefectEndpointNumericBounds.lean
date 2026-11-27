import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveOddLargeShoreBOnlyPositiveBarrierImpossible
import AFTD.Kb.Tcs.AnticompleteVertexFourDisjointNonneighborSetsBound
import AFTD.Kb.Tcs.Op1957FourShoreRepresentativeBudget
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter

/-!
# op1957_one_defect_endpoint_numeric_bounds

Topic: graphs   Node: 939f1fcc6a95

Provenance: helper lemma. OP-1957: five-by-odd boundary reduction, arXiv:2611.22690

Under the displayed five-by-odd block partition, degree and one-defect shore hypotheses, the endpoint and nonendpoint representative intersection counts satisfy the listed inequalities.
-/

theorem op1957_one_defect_endpoint_numeric_bounds
    (k c : ℕ) (hc : 5 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D X Y U : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (x y : Fin (4*k)) (hxA : x ∈ A) (hyC : y ∈ C) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hantiY : ∀ a ∈ Y, ∀ u ∈ U, ¬ G.Adj a u)
    (hdefect : (C.filter (fun w => ¬ G.Adj x w)).card ≤ 1) :
    let a0 := (X ∩ A).card; let b0 := (X ∩ B).card; let c0 := (X ∩ C).card; let d0 := (X ∩ D).card
    let a1 := (Y ∩ A).card; let b1 := (Y ∩ B).card; let c1 := (Y ∩ C).card; let d1 := (Y ∩ D).card
    let a2 := (U ∩ A).card; let b2 := (U ∩ B).card; let c2 := (U ∩ C).card; let d2 := (U ∩ D).card
    1 ≤ a0 ∧ 1 ≤ c1 ∧ c1+c2 ≤ 2 ∧
    a1+c1+d1+a2+c2+d2 ≤ 3 ∧ a0+b0+c0+a2+b2+c2+2 ≤ c ∧
    (2 ≤ a0 → a1+c1+d1+a2+c2+d2 ≤ 2) ∧
    (1 ≤ c0 → a1+b1+c1+a2+b2+c2+3 ≤ c) ∧
    (1 ≤ d0 → a1+b1+d1+a2+b2+d2+c+3 ≤ 2*k) ∧
    (1 ≤ a1 → a0+c0+d0+a2+c2+d2 ≤ 2) ∧
    (2 ≤ c1 → a0+b0+c0+a2+b2+c2+3 ≤ c) := by
  classical
  dsimp only
  let F : Fin 4 → Finset (Fin (4*k)) := in1245_shores X Y
  let L : Fin 4 → Finset (Fin (4*k)) := in1245_blocks A B C D
  let forb : Fin 4 → Fin 4 := ![1,0,3,2]
  have hFdis : ∀ i j, i ≠ j → Disjoint (F i) (F j) := in1245_shores_disjoint X Y hXY
  have hEdis : ∀ i, Disjoint (F i) U := in1245_shores_pool_disjoint X Y U hXU hYU
  have hBdis : ∀ i j, i ≠ j → Disjoint (L i) (L j) := in1245_blocks_disjoint A B C D hAB hAC hAD hBC hBD hCD
  have hcross4 : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, G.Adj a b →
      (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x) := in1245_shores_cross G X Y x y hcross
  have hEanti : ∀ i, ∀ a ∈ F i, ∀ u ∈ U, ¬ G.Adj a u := in1245_shores_pool_anti G X Y U hantiX hantiY
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
  have hxL : x ∈ L 0 := by simpa [L,in1245_blocks] using hxA
  have hyL : y ∈ L 2 := by simpa [L,in1245_blocks] using hyC
  have hrep (j b : Fin 4)
      (hh : (if (j=0 ∧ b=0) ∨ (j=1 ∧ b=2) then 2 else 1) ≤ (F j ∩ L b).card) :=
    op1957_four_shore_representative_budget G F L U x y hFdis hEdis hBdis hxL hyL hcross4 hEanti
      j b (forb b) (hbf b) (hforbid b) (2*k) (hmin b)
      (by have hb := hblocks b; have hm := hmin b; simp only [Fintype.card_fin]; omega) hdegree hh
  have hparts (P : Finset (Fin (4*k))) := finset_card_eq_sum_four_block_inter A B C D P hAB hAC hAD hBC hBD hCD hcover
  have hdiffB (P : Finset (Fin (4*k))) : (P \ B).card = (P ∩ A).card+(P ∩ C).card+(P ∩ D).card := by
    have hs := hparts P; have hd := Finset.card_inter_add_card_sdiff P B; omega
  have hdiffC (P : Finset (Fin (4*k))) : (P \ C).card = (P ∩ A).card+(P ∩ B).card+(P ∩ D).card := by
    have hs := hparts P; have hd := Finset.card_inter_add_card_sdiff P C; omega
  have hdiffD (P : Finset (Fin (4*k))) : (P \ D).card = (P ∩ A).card+(P ∩ B).card+(P ∩ C).card := by
    have hs := hparts P; have hd := Finset.card_inter_add_card_sdiff P D; omega
  have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hAB hxA h
  have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
  have hxD : x ∉ D := fun h => Finset.disjoint_left.mp hAD hxA h
  have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hCD hyC h
  have hxY : x ∉ Y := fun h => Finset.disjoint_left.mp hXY hxX h
  have hyX : y ∉ X := fun h => Finset.disjoint_left.mp hXY h hyY
  have hxU : x ∉ U := fun h => Finset.disjoint_left.mp hXU hxX h
  have hyU : y ∉ U := fun h => Finset.disjoint_left.mp hYU hyY h
  have hyQB : y ∈ Y \ B := Finset.mem_sdiff.mpr ⟨hyY,hyB⟩
  have hxQD : x ∈ X \ D := Finset.mem_sdiff.mpr ⟨hxX,hxD⟩
  have hYerase : (Y.erase y) \ B = (Y \ B).erase y := by ext z; simp [and_assoc,and_left_comm,and_comm]
  have hXerase : (X.erase x) \ D = (X \ D).erase x := by ext z; simp [and_assoc,and_left_comm,and_comm]
  have hbudgetX : ((Y.erase y) \ B).card + (U \ B).card ≤ 2 := by
    have hs : ∀ z, (z ∈ Y.erase y ∨ z ∈ U ∨ z ∈ (∅ : Finset (Fin (4*k))) ∨ z ∈ (∅ : Finset (Fin (4*k)))) → z ≠ x ∧ ¬ G.Adj x z := by
      intro z hz
      rcases hz with hz | hz | hz | hz
      · have hz' := Finset.mem_erase.mp hz
        exact ⟨fun he => hxY (he ▸ hz'.2),fun h => hz'.1 (hcross x hxX z hz'.2 h).2⟩
      · exact ⟨fun he => hxU (he ▸ hz),hantiX x hxX z hz⟩
      · simp at hz
      · simp at hz
    have hh := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G B x hxB (hnoAB x hxA) (2*k+4) 2
      (by simp only [Fintype.card_fin]; omega) (by have := hdegree x; omega)
      (Y.erase y) U ∅ ∅ hs (Finset.disjoint_of_subset_left (Finset.erase_subset y Y) hYU) (by simp) (by simp) (by simp) (by simp) (by simp)
    simpa using hh
  have hbudgetY : ((X.erase x) \ D).card + (U \ D).card ≤ c-3 := by
    have hs : ∀ z, (z ∈ X.erase x ∨ z ∈ U ∨ z ∈ (∅ : Finset (Fin (4*k))) ∨ z ∈ (∅ : Finset (Fin (4*k)))) → z ≠ y ∧ ¬ G.Adj y z := by
      intro z hz
      rcases hz with hz | hz | hz | hz
      · have hz' := Finset.mem_erase.mp hz
        exact ⟨fun he => hyX (he ▸ hz'.2),fun h => hz'.1 (hcross z hz'.2 y hyY h.symm).1⟩
      · exact ⟨fun he => hyU (he ▸ hz),hantiY y hyY z hz⟩
      · simp at hz
      · simp at hz
    have hh := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G D y hyD (hnoCD y hyC) (2*k+c-1) (c-3)
      (by simp only [Fintype.card_fin]; omega) (by have := hdegree y; omega)
      (X.erase x) U ∅ ∅ hs (Finset.disjoint_of_subset_left (Finset.erase_subset x X) hXU) (by simp) (by simp) (by simp) (by simp) (by simp)
    simpa using hh
  have hxcount : (Y ∩ A).card+(Y ∩ C).card+(Y ∩ D).card+(U ∩ A).card+(U ∩ C).card+(U ∩ D).card ≤ 3 := by
    rw [hYerase,Finset.card_erase_of_mem hyQB,hdiffB Y,hdiffB U] at hbudgetX
    have hp := Finset.card_pos.mpr ⟨y,hyQB⟩
    rw [hdiffB Y] at hp
    omega
  have hycount : (X ∩ A).card+(X ∩ B).card+(X ∩ C).card+(U ∩ A).card+(U ∩ B).card+(U ∩ C).card+2 ≤ c := by
    rw [hXerase,Finset.card_erase_of_mem hxQD,hdiffD X,hdiffD U] at hbudgetY
    have hp := Finset.card_pos.mpr ⟨x,hxQD⟩
    rw [hdiffD X] at hp
    omega
  let P := C.filter (fun w => ¬ G.Adj x w)
  have hCsub : ((Y ∩ C).erase y) ∪ (U ∩ C) ⊆ P := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have he := Finset.mem_erase.mp hz
      have hyc := Finset.mem_inter.mp he.2
      have hn : ¬ G.Adj x z := fun h => he.1 (hcross x hxX z hyc.1 h).2
      exact Finset.mem_filter.mpr ⟨hyc.2,hn⟩
    · have hu := Finset.mem_inter.mp hz
      exact Finset.mem_filter.mpr ⟨hu.2,hantiX x hxX z hu.1⟩
  have hCdis : Disjoint ((Y ∩ C).erase y) (U ∩ C) :=
    Finset.disjoint_of_subset_left (Finset.Subset.trans (Finset.erase_subset y (Y ∩ C)) Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hYU)
  have hyYC : y ∈ Y ∩ C := Finset.mem_inter.mpr ⟨hyY,hyC⟩
  have hcsmall : (Y ∩ C).card+(U ∩ C).card ≤ 2 := by
    have hh := Finset.card_le_card hCsub
    rw [Finset.card_union_of_disjoint hCdis,Finset.card_erase_of_mem hyYC] at hh
    have hp := Finset.card_pos.mpr ⟨y,hyYC⟩
    dsimp [P] at hh
    omega
  have ha0 : 1 ≤ (X ∩ A).card := Finset.card_pos.mpr ⟨x,Finset.mem_inter.mpr ⟨hxX,hxA⟩⟩
  have hc1 : 1 ≤ (Y ∩ C).card := Finset.card_pos.mpr ⟨y,hyYC⟩
  have hE0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hE1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hrepA0 : 2 ≤ (X ∩ A).card → (Y ∩ A).card+(Y ∩ C).card+(Y ∩ D).card+(U ∩ A).card+(U ∩ C).card+(U ∩ D).card ≤ 2 := by
    intro hh
    have hr := hrep 0 0 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    simp [F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hE0,hE1,hA,hdiffB] at hr
    omega
  have hrepC0 : 1 ≤ (X ∩ C).card → (Y ∩ A).card+(Y ∩ B).card+(Y ∩ C).card+(U ∩ A).card+(U ∩ B).card+(U ∩ C).card+3 ≤ c := by
    intro hh
    have hr := hrep 0 2 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    simp [F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hE0,hE1,hC,hdiffD] at hr
    omega
  have hrepD0 : 1 ≤ (X ∩ D).card → (Y ∩ A).card+(Y ∩ B).card+(Y ∩ D).card+(U ∩ A).card+(U ∩ B).card+(U ∩ D).card+c+3 ≤ 2*k := by
    intro hh
    have hr := hrep 0 3 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    simp [F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hE0,hE1,hD,hdiffC] at hr
    omega
  have hrepA1 : 1 ≤ (Y ∩ A).card → (X ∩ A).card+(X ∩ C).card+(X ∩ D).card+(U ∩ A).card+(U ∩ C).card+(U ∩ D).card ≤ 2 := by
    intro hh
    have hr := hrep 1 0 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    simp [F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hE0,hE1,hA,hdiffB] at hr
    omega
  have hrepC1 : 2 ≤ (Y ∩ C).card → (X ∩ A).card+(X ∩ B).card+(X ∩ C).card+(U ∩ A).card+(U ∩ B).card+(U ∩ C).card+3 ≤ c := by
    intro hh
    have hr := hrep 1 2 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    simp [F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hE0,hE1,hC,hdiffD] at hr
    omega
  exact ⟨ha0,hc1,hcsmall,hxcount,hycount,hrepA0,hrepC0,hrepD0,hrepA1,hrepC1⟩
