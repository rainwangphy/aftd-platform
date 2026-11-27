import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.Op1957OddComponentsAmbientPartition
import AFTD.Kb.Tcs.Op1957FourShoreAggregateTotals
import AFTD.Kb.Tcs.FourShoreSaturatedYRootCountBound
import AFTD.Kb.Tcs.Op1957FourShoreAggregateRepresentativeBounds
import AFTD.Kb.Tcs.Op1957FourShoreFirstDSeparatorBound
import AFTD.Kb.Tcs.FourShoreAggregateBlockCriticality
import AFTD.Kb.Tcs.Op1957LargeShoreNonemptyBPoolContradiction
import AFTD.Kb.Tcs.PairwiseDisjointNonemptyGroupsCardBound
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter

/-!
# boundary_five_odd_large_shore_B_only_positive_barrier_impossible

Topic: graphs   Node: c1959b8bb6bd

Provenance: helper lemma. OP-1957: positive B-only barrier and A-rich shore

Under the displayed five-by-odd partition, degree, separator and connected factor-critical block conditions, a positive barrier supported in B and a second shore supported in B plus its C-root cannot coexist with an A-rich first shore of size three or four.
-/

set_option maxHeartbeats 2000000
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def in1245_shores (X Y : Finset V) : Fin 4 → Finset V := ![X,Y,∅,∅]
def in1245_blocks (A B C D : Finset V) : Fin 4 → Finset V := ![A,B,C,D]

theorem in1245_shores_disjoint (X Y : Finset V) (h : Disjoint X Y) :
    ∀ i j : Fin 4, i ≠ j → Disjoint (in1245_shores X Y i) (in1245_shores X Y j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [in1245_shores] <;> exact h.symm

theorem in1245_shores_pool_disjoint (X Y U : Finset V) (hX : Disjoint X U) (hY : Disjoint Y U) :
    ∀ i : Fin 4, Disjoint (in1245_shores X Y i) U := by
  intro i
  fin_cases i <;> simp_all [in1245_shores]

theorem in1245_blocks_disjoint (A B C D : Finset V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) :
    ∀ i j : Fin 4, i ≠ j → Disjoint (in1245_blocks A B C D i) (in1245_blocks A B C D j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [in1245_blocks] <;> first | exact hAB.symm | exact hAC.symm | exact hAD.symm | exact hBC.symm | exact hBD.symm | exact hCD.symm

theorem in1245_blocks_cover (A B C D : Finset V) (hcover : A ∪ B ∪ C ∪ D = Finset.univ) :
    (Finset.univ : Finset (Fin 4)).biUnion (in1245_blocks A B C D) = Finset.univ := by
  ext v
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · intro _; simp
  · intro _
    have hv : v ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; simp
    simp only [Finset.mem_union] at hv
    rcases hv with ((ha | hb) | hc) | hd
    · exact ⟨0,by simpa [in1245_blocks] using ha⟩
    · exact ⟨1,by simpa [in1245_blocks] using hb⟩
    · exact ⟨2,by simpa [in1245_blocks] using hc⟩
    · exact ⟨3,by simpa [in1245_blocks] using hd⟩

theorem in1245_shores_cross (G : SimpleGraph V) (X Y : Finset V) (x y : V)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y) :
    ∀ i j : Fin 4, i ≠ j → ∀ a ∈ in1245_shores X Y i, ∀ b ∈ in1245_shores X Y j,
      G.Adj a b → (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x) := by
  intro i j hij a ha b hb hab
  fin_cases i <;> fin_cases j <;> simp_all [in1245_shores]
  · exact hcross a ha b hb hab
  · obtain ⟨h1,h2⟩ := hcross b hb a ha hab.symm
    exact ⟨h2,h1⟩

theorem in1245_shores_pool_anti (G : SimpleGraph V) (X Y U : Finset V)
    (hX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hY : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u) :
    ∀ i : Fin 4, ∀ a ∈ in1245_shores X Y i, ∀ u ∈ U, ¬ G.Adj a u := by
  intro i a ha u hu
  fin_cases i <;> simp_all [in1245_shores]

theorem boundary_five_odd_large_shore_B_only_positive_barrier_impossible
    (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D X Y U : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hconnB : (G.induce {v | v ∈ B}).Connected)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (x y : Fin (4*k)) (hxA : x ∈ A) (hyC : y ∈ C) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hY : Y ⊆ B ∪ {y}) (hU : U ⊆ B)
    (s : ℕ) (hs : 1 ≤ s) (hsize : X.card+Y.card+U.card+s=2*k)
    (hUodd : s ≤ (G.induce {v | v ∈ U}).oddComponents.ncard)
    (hUparity : U.card % 2 = s % 2)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hantiY : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u)
    (hlarge : 3 ≤ (X ∩ A).card ∧ (X ∩ A).card ≤ 4) : False := by
  classical
  let F : Fin 4 → Finset (Fin (4*k)) := in1245_shores X Y
  let L : Fin 4 → Finset (Fin (4*k)) := in1245_blocks A B C D
  let forb : Fin 4 → Fin 4 := ![1,0,3,2]
  have hFdis : ∀ i j, i ≠ j → Disjoint (F i) (F j) := in1245_shores_disjoint X Y hXY
  have hEdis : ∀ i, Disjoint (F i) U := in1245_shores_pool_disjoint X Y U hXU hYU
  have hBdis : ∀ i j, i ≠ j → Disjoint (L i) (L j) := in1245_blocks_disjoint A B C D hAB hAC hAD hBC hBD hCD
  have hBcover : (Finset.univ : Finset (Fin 4)).biUnion L = Finset.univ := in1245_blocks_cover A B C D hcover
  have hcross4 : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, G.Adj a b →
      (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x) := in1245_shores_cross G X Y x y hcross
  have hEanti : ∀ i, ∀ a ∈ F i, ∀ u ∈ U, ¬ G.Adj a u := in1245_shores_pool_anti G X Y U hantiX hantiY
  have hforbid : ∀ b, ∀ a ∈ L b, ∀ w ∈ L (forb b), ¬ G.Adj a w := by
    intro i a ha v hv h
    fin_cases i <;> simp only [L,forb,in1245_blocks,Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at ha hv
    · exact hnoAB a ha v hv h
    · exact hnoAB v hv a ha h.symm
    · exact hnoCD a ha v hv h
    · exact hnoCD v hv a ha h.symm
  have hbf : ∀ b, b ≠ forb b := by intro i; fin_cases i <;> decide
  have hblocks : ∀ b, (L b).card+(L (forb b)).card=2*k := by
    intro i
    fin_cases i <;> simp [L,forb,in1245_blocks,hA,hB,hC,hD] <;> omega
  have hmin : ∀ b, 3 ≤ (L b).card := by
    intro i
    fin_cases i <;> simp [L,in1245_blocks,hA,hB,hC,hD] <;> omega
  have hV : Fintype.card (Fin (4*k))=2*(2*k) := by simp; omega
  obtain ⟨Q,hQodd,hQdis,hQcover⟩ := op1957_odd_components_ambient_partition G U s hs hUodd hUparity
  have hT : ∀ j ∈ (Finset.univ : Finset (Fin s)), Odd (Q j).card := by intro j _; exact (hQodd j).2
  have hQd : ∀ i ∈ (Finset.univ : Finset (Fin s)), ∀ j ∈ (Finset.univ : Finset (Fin s)), i ≠ j → Disjoint (Q i) (Q j) := by
    intro i _ j _ hij; exact (hQdis i j hij).1
  have hQa : ∀ i ∈ (Finset.univ : Finset (Fin s)), ∀ j ∈ (Finset.univ : Finset (Fin s)), i ≠ j → ∀ a ∈ Q i, ∀ b ∈ Q j, ¬ G.Adj a b := by
    intro i _ j _ hij; exact (hQdis i j hij).2
  have hEB : U ⊆ L 1 := by simpa [L,in1245_blocks] using hU
  have hxL : x ∈ L 0 := by simpa [L,in1245_blocks] using hxA
  have hyL : y ∈ L 2 := by simpa [L,in1245_blocks] using hyC
  have hrep := op1957_four_shore_aggregate_representative_bounds G F L U x y forb (2*k)
    hFdis hEdis hBdis hBcover hEB hxL hyL hcross4 hEanti hbf hforbid hblocks hmin hV hdegree
  have hcrit := four_shore_aggregate_block_criticality G F L U x y Finset.univ Q
    hFdis hEdis hBdis hBcover hEB hxL hyL hcross4 hEanti hT hQd hQa hQcover hcritB hconnB
  have hQne : ∀ j ∈ (Finset.univ : Finset (Fin s)), (Q j).Nonempty := by
    intro j _
    apply Finset.card_pos.mp
    have h := (hQodd j).2
    obtain ⟨t,ht⟩ := h
    omega
  have heb : s ≤ U.card := by
    let j : Fin s := ⟨0,hs⟩
    have hh := pairwise_disjoint_nonempty_groups_card_bound Finset.univ Q j (Finset.mem_univ _) hQd hQne
    rw [hQcover] at hh
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    have hj := Finset.card_pos.mpr (hQne j (Finset.mem_univ _))
    omega
  have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
  have hYeq : Y = (Y ∩ B) ∪ {y} := by
    ext z
    constructor
    · intro hz
      have hh := hY hz
      simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_singleton] at hh ⊢
      rcases hh with hb | heq
      · exact Or.inl ⟨hz,hb⟩
      · exact Or.inr heq
    · intro hz
      simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_singleton] at hz
      rcases hz with ⟨hz,_⟩ | rfl
      · exact hz
      · exact hyY
  have hYcard : Y.card = (Y ∩ B).card+1 := by
    calc
      Y.card = ((Y ∩ B) ∪ {y}).card := congrArg Finset.card hYeq
      _ = (Y ∩ B).card+1 := by
        rw [Finset.card_union_of_disjoint]
        · simp
        · simp [Finset.disjoint_singleton_right,hyB]
  have hYA : Y ∩ A = ∅ := by
    apply Finset.disjoint_iff_inter_eq_empty.mp
    apply Finset.disjoint_left.mpr
    intro z hzY hzA
    have hh := hY hzY
    simp only [Finset.mem_union,Finset.mem_singleton] at hh
    rcases hh with hzB | rfl
    · exact Finset.disjoint_left.mp hAB hzA hzB
    · exact Finset.disjoint_left.mp hAC hzA hyC
  have hYD : Y ∩ D = ∅ := by
    apply Finset.disjoint_iff_inter_eq_empty.mp
    apply Finset.disjoint_left.mpr
    intro z hzY hzD
    have hh := hY hzY
    simp only [Finset.mem_union,Finset.mem_singleton] at hh
    rcases hh with hzB | rfl
    · exact Finset.disjoint_left.mp hBD hzB hzD
    · exact Finset.disjoint_left.mp hCD hyC hzD
  have hYC : Y ∩ C = {y} := by
    ext z
    simp only [Finset.mem_inter,Finset.mem_singleton]
    constructor
    · rintro ⟨hzY,hzC⟩
      have hh := hY hzY
      simp only [Finset.mem_union,Finset.mem_singleton] at hh
      rcases hh with hzB | heq
      · exact False.elim (Finset.disjoint_left.mp hBC hzB hzC)
      · exact heq
    · intro h; subst z; exact ⟨hyY,hyC⟩
  have hXsum := finset_card_eq_sum_four_block_inter A B C D X hAB hAC hAD hBC hBD hCD hcover
  have htot := op1957_four_shore_aggregate_totals F L U hFdis hEdis hBdis hBcover hEB
  have hb := htot.2.1 1
  simp [F,L,in1245_shores,in1245_blocks,Fin.sum_univ_four,hB] at hb
  have hroot := four_shore_saturated_y_root_count_bound k c hc hkc G A B C D U F x y
    hAB hAC hAD hBC hBD hCD hcover hFdis hEdis hU
    (by simp [F,in1245_shores]) (by simp [F,in1245_shores])
    (by simp [F,in1245_shores]) (by simp [F,in1245_shores])
    hxA (by simpa [F,in1245_shores] using hxX) hyC (by simpa [F,in1245_shores] using hyY)
    hD hcross4 hEanti hnoCD (hdegree y)
  simp [F,in1245_shores] at hroot
  have hrepC : 1 ≤ (X ∩ C).card → (Y ∩ B).card+U.card+4 ≤ c := by
    intro hh
    have hr := hrep 0 2 (by simpa [F,L,in1245_shores,in1245_blocks] using hh)
    dsimp at hr
    have hE3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
    simp [hE3,F,L,forb,in1245_shores,in1245_blocks,Fin.sum_univ_four,hC,hYA,hYD,hYC] at hr
    omega
  have hcutD : 1 ≤ (X ∩ D).card → (X ∩ D).card+(Y ∩ B).card+U.card+c ≤ 2*k := by
    intro hh
    have hDX : (D ∩ F 0).Nonempty := by
      apply Finset.card_pos.mp
      simpa [F,in1245_shores,Finset.inter_comm] using hh
    have hr := op1957_four_shore_first_D_separator_bound G F U A B C D x y (2*k)
      hFdis hEdis hcross4 hEanti hU hyC hAB hAC hAD hBC hBD hCD hcover (by omega) hnoCD hsep hDX
    simp [F,in1245_shores] at hr
    omega
  have hcrit' : ((X ∩ B).card+(Y ∩ B).card+U.card+5 < 2*k →
      s+(X ∩ B).card+(Y ∩ B).card+U.card+6 ≤ 2*k) ∧
    ((X ∩ B).card+(Y ∩ B).card+U.card+5 = 2*k → s ≤ 1 ∧
      (if 1 ≤ (X ∩ B).card then 1 else 0) + (if 1 ≤ (Y ∩ B).card then 1 else 0) + s ≤ 1) := by
    dsimp at hcrit
    simp only [Fin.sum_univ_four,Finset.card_univ,Fintype.card_fin] at hcrit
    simp [F,L,in1245_shores,in1245_blocks,hB] at hcrit
    have hz0 : (1 ≤ (X ∩ B).card) ↔ (X ∩ B).Nonempty := by
      rw [← Finset.card_pos]
      omega
    have hz1 : (1 ≤ (Y ∩ B).card) ↔ (Y ∩ B).Nonempty := by
      rw [← Finset.card_pos]
      omega
    simp only [hz0,hz1]
    omega
  exact op1957_large_shore_nonempty_B_pool_contradiction k c s U.card
    (X ∩ A).card (X ∩ B).card (Y ∩ B).card (X ∩ C).card (X ∩ D).card
    hc hkc heb hs hlarge (by omega) (by omega) (by omega) hrepC hcutD hcrit'
