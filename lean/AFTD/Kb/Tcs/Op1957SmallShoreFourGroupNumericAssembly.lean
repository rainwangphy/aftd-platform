import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.Op1957FourShoreAggregateTotals
import AFTD.Kb.Tcs.FourShoreSaturatedYRootCountBound
import AFTD.Kb.Tcs.Op1957FourShoreAggregateRepresentativeBounds
import AFTD.Kb.Tcs.Op1957FourShoreFirstDSeparatorBound
import AFTD.Kb.Tcs.FourShoreAggregateBlockCriticality
import AFTD.Kb.Tcs.SaturatedOtherShoresOppositeBlockCardLeThree
import AFTD.Kb.Tcs.FiveOddSaturatedSmallShoreArithmeticNoConnectedness
import AFTD.Kb.Tcs.SaturatedPositiveSmallShoreForcesTwoSingletonGroups
import AFTD.Kb.Tcs.SaturatedSmallShoreSingletonPoolEmpty
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter

/-!
# op1957_small_shore_four_group_numeric_assembly

Topic: graphs   Node: ad8f332d5c5e

Provenance: helper lemma. OP-1957 positive-barrier small-shore count transfer

For four anticomplete shores and a B-only pool under the displayed saturated five-by-odd, degree, separator, extendibility, independence and group-count hypotheses, each exceptional shore meets C.
-/

set_option maxHeartbeats 3000000
open scoped BigOperators

def in1245_small_blocks {V : Type*} (A B C D : Finset V) : Fin 4 → Finset V := ![A,B,C,D]

theorem op1957_small_shore_four_group_numeric_assembly
    {I : Type*} [DecidableEq I]
    (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D E : Finset (Fin (4*k))) (F : Fin 4 → Finset (Fin (4*k)))
    (J : Finset I) (R : I → Finset (Fin (4*k))) (x y p q : Fin (4*k))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hconnB : (G.induce {v | v ∈ B}).Connected)
    (hext : is_k_extendable G k)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) → I.card ≤ k)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (hFdis : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hEdis : ∀ i, Disjoint (F i) E) (hEB : E ⊆ B)
    (hFA : ∀ i : Fin 4, i ≠ 0 → Disjoint (F i) A)
    (hFD : ∀ i : Fin 4, i ≠ 0 → Disjoint (F i) D)
    (hxA : x ∈ A) (hyC : y ∈ C) (hxF : x ∈ F 0) (hyF : y ∈ F 1)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z)
    (hcross : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, G.Adj a b →
      (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x))
    (hEanti : ∀ i, ∀ a ∈ F i, ∀ b ∈ E, ¬ G.Adj a b)
    (hRodd : ∀ i ∈ J, Odd (R i).card)
    (hRdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (R i) (R j))
    (hRanti : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ u ∈ R i, ∀ v ∈ R j, ¬ G.Adj u v)
    (hRcover : J.biUnion R = E)
    (hodd0 : Odd (F 0).card) (hodd1 : Odd (F 1).card)
    (hsmallA : (F 0 ∩ A).card ≤ 2)
    (he2 : ((F 2 ∩ C).card = 0 ∧ (F 2 ∩ B).card = 0) ∨ 1 ≤ (F 2 ∩ C).card)
    (he3 : ((F 3 ∩ C).card = 0 ∧ (F 3 ∩ B).card = 0) ∨ 1 ≤ (F 3 ∩ C).card)
    (heb : J.card ≤ E.card)
    (hsize : (∑ i : Fin 4, (F i).card)+E.card+J.card+
      (if 1 ≤ (F 2 ∩ C).card then 1 else 0)+
      (if 1 ≤ (F 3 ∩ C).card then 1 else 0)=2*k)
    (hspos : 1 ≤ J.card+(if 1 ≤ (F 2 ∩ C).card then 1 else 0)+
      (if 1 ≤ (F 3 ∩ C).card then 1 else 0)) :
    (F 2 ∩ C).Nonempty ∧ (F 3 ∩ C).Nonempty := by
  classical
  let L : Fin 4 → Finset (Fin (4*k)) := in1245_small_blocks A B C D
  let forb : Fin 4 → Fin 4 := ![1,0,3,2]
  have hBdis : ∀ i j, i ≠ j → Disjoint (L i) (L j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [L,in1245_small_blocks] <;>
      first | exact hAB | exact hAB.symm | exact hAC | exact hAC.symm | exact hAD | exact hAD.symm |
        exact hBC | exact hBC.symm | exact hBD | exact hBD.symm | exact hCD | exact hCD.symm
  have hBcover : (Finset.univ : Finset (Fin 4)).biUnion L = Finset.univ := by
    rw [←hcover]
    ext z
    simp [L,in1245_small_blocks,Finset.mem_biUnion,Fin.exists_fin_succ]
  have hforbid : ∀ b, ∀ a ∈ L b, ∀ w ∈ L (forb b), ¬ G.Adj a w := by
    intro i a ha v hv h
    fin_cases i <;> simp only [L,forb,in1245_small_blocks,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at ha hv
    · exact hnoAB a ha v hv h
    · exact hnoAB v hv a ha h.symm
    · exact hnoCD a ha v hv h
    · exact hnoCD v hv a ha h.symm
  have hbf : ∀ b, b ≠ forb b := by intro i; fin_cases i <;> decide
  have hblocks : ∀ b, (L b).card+(L (forb b)).card=2*k := by
    intro i
    fin_cases i <;> simp [L,forb,in1245_small_blocks,hA,hB,hC,hD] <;> omega
  have hmin : ∀ b, 3 ≤ (L b).card := by
    intro i
    fin_cases i <;> simp [L,in1245_small_blocks,hA,hB,hC,hD] <;> omega
  have hV : Fintype.card (Fin (4*k))=2*(2*k) := by simp; omega
  have hEL : E ⊆ L 1 := by simpa [L,in1245_small_blocks] using hEB
  have hxL : x ∈ L 0 := by simpa [L,in1245_small_blocks] using hxA
  have hyL : y ∈ L 2 := by simpa [L,in1245_small_blocks] using hyC
  have hrep := op1957_four_shore_aggregate_representative_bounds G F L E x y forb (2*k)
    hFdis hEdis hBdis hBcover hEL hxL hyL hcross hEanti hbf hforbid hblocks hmin hV hdegree
  have hcrit := four_shore_aggregate_block_criticality G F L E x y J R
    hFdis hEdis hBdis hBcover hEL hxL hyL hcross hEanti hRodd hRdis hRanti hRcover hcritB hconnB
  have htot := op1957_four_shore_aggregate_totals F L E hFdis hEdis hBdis hBcover hEL
  have hroot := four_shore_saturated_y_root_count_bound k c hc hkc G A B C D E F x y
    hAB hAC hAD hBC hBD hCD hcover hFdis hEdis hEB
    (hFA 2 (by decide)) (hFD 2 (by decide)) (hFA 3 (by decide)) (hFD 3 (by decide))
    hxA hxF hyC hyF hD hcross hEanti hnoCD (hdegree y)
  have hsmall := saturated_other_shores_opposite_block_card_le_three G F C x y p q hFdis hxF hcross hfull
  have hRne : ∀ i ∈ J, (R i).Nonempty := by
    intro i hi
    apply Finset.card_pos.mp
    obtain ⟨t,ht⟩ := hRodd i hi
    omega
  have hRsub : ∀ i ∈ J, R i ⊆ E := by
    intro i hi v hv
    rw [←hRcover]
    exact Finset.mem_biUnion.mpr ⟨i,hi,hv⟩
  have hFAzero : ∀ i : Fin 4, i ≠ 0 → F i ∩ A = ∅ := by
    intro i hi; exact Finset.disjoint_iff_inter_eq_empty.mp (hFA i hi)
  have hFDzero : ∀ i : Fin 4, i ≠ 0 → F i ∩ D = ∅ := by
    intro i hi; exact Finset.disjoint_iff_inter_eq_empty.mp (hFD i hi)
  have hcard0 := finset_card_eq_sum_four_block_inter A B C D (F 0) hAB hAC hAD hBC hBD hCD hcover
  have hcard1 := finset_card_eq_sum_four_block_inter A B C D (F 1) hAB hAC hAD hBC hBD hCD hcover
  have hcard2 := finset_card_eq_sum_four_block_inter A B C D (F 2) hAB hAC hAD hBC hBD hCD hcover
  have hcard3 := finset_card_eq_sum_four_block_inter A B C D (F 3) hAB hAC hAD hBC hBD hCD hcover
  have h1A := hFAzero 1 (by decide)
  have h2A := hFAzero 2 (by decide)
  have h3A := hFAzero 3 (by decide)
  have h1D := hFDzero 1 (by decide)
  have h2D := hFDzero 2 (by decide)
  have h3D := hFDzero 3 (by decide)
  simp [h1A,h2A,h3A,h1D,h2D,h3D] at hcard1 hcard2 hcard3
  have ha : 1 ≤ (F 0 ∩ A).card ∧ (F 0 ∩ A).card ≤ 2 := by
    constructor
    · exact Finset.card_pos.mpr ⟨x,Finset.mem_inter.mpr ⟨hxF,hxA⟩⟩
    · exact hsmallA
  have hc1 : 1 ≤ (F 1 ∩ C).card := Finset.card_pos.mpr ⟨y,Finset.mem_inter.mpr ⟨hyF,hyC⟩⟩
  have ho0 : Odd ((F 0 ∩ A).card+(F 0 ∩ B).card+(F 0 ∩ C).card+(F 0 ∩ D).card) := by
    rw [←hcard0]; exact hodd0
  have ho1 : Odd ((F 1 ∩ B).card+(F 1 ∩ C).card) := by
    rw [←hcard1]; exact hodd1
  have hs : J.card+(if 1 ≤ (F 2 ∩ C).card then 1 else 0)+
      (if 1 ≤ (F 3 ∩ C).card then 1 else 0)+1 ≤ c := by
    have hh2 : (if 1 ≤ (F 2 ∩ C).card then 1 else 0) ≤ (F 2 ∩ C).card := by split_ifs <;> omega
    have hh3 : (if 1 ≤ (F 3 ∩ C).card then 1 else 0) ≤ (F 3 ∩ C).card := by split_ifs <;> omega
    omega
  have hb : (F 0 ∩ B).card+(F 1 ∩ B).card+(F 2 ∩ B).card+(F 3 ∩ B).card+E.card+5 ≤ 2*k := by
    have hh := htot.2.1 1
    simp [L,in1245_small_blocks,Fin.sum_univ_four,hB] at hh
    omega
  have htotal : (F 0 ∩ A).card+(F 0 ∩ B).card+(F 1 ∩ B).card+(F 2 ∩ B).card+(F 3 ∩ B).card+E.card+
      (F 0 ∩ C).card+(F 1 ∩ C).card+(F 2 ∩ C).card+(F 3 ∩ C).card+(F 0 ∩ D).card+J.card+
      (if 1 ≤ (F 2 ∩ C).card then 1 else 0)+(if 1 ≤ (F 3 ∩ C).card then 1 else 0)=2*k := by
    simp only [Fin.sum_univ_four] at hsize
    omega
  have hE1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hE3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  have hrepA : 2 ≤ (F 0 ∩ A).card → (F 1 ∩ C).card+(F 2 ∩ C).card+(F 3 ∩ C).card ≤ 2 := by
    intro hh
    have hr := hrep 0 0 (by simpa [L,in1245_small_blocks] using hh)
    dsimp at hr
    simp [hE1,L,forb,in1245_small_blocks,Fin.sum_univ_four,hA,h1A,h2A,h3A,h1D,h2D,h3D] at hr
    omega
  have hrep0C : 1 ≤ (F 0 ∩ C).card →
      (F 1 ∩ B).card+(F 2 ∩ B).card+(F 3 ∩ B).card+E.card+
      (F 1 ∩ C).card+(F 2 ∩ C).card+(F 3 ∩ C).card+3 ≤ c := by
    intro hh
    have hr := hrep 0 2 (by simpa [L,in1245_small_blocks] using hh)
    dsimp at hr
    simp [hE3,L,forb,in1245_small_blocks,Fin.sum_univ_four,hC,h1A,h2A,h3A,h1D,h2D,h3D] at hr
    omega
  have hcutD : 1 ≤ (F 0 ∩ D).card → (F 0 ∩ D).card+(F 1 ∩ B).card+(F 2 ∩ B).card+
      (F 3 ∩ B).card+E.card+c ≤ 2*k := by
    intro hh
    have hd : (D ∩ F 0).Nonempty := by
      apply Finset.card_pos.mp
      simpa [Finset.inter_comm] using hh
    have hr := op1957_four_shore_first_D_separator_bound G F E A B C D x y (2*k)
      hFdis hEdis hcross hEanti hEB hyC hAB hAC hAD hBC hBD hCD hcover (by omega) hnoCD hsep hd
    omega
  have hrep1C : 2 ≤ (F 1 ∩ C).card →
      (F 0 ∩ A).card+(F 0 ∩ B).card+(F 2 ∩ B).card+(F 3 ∩ B).card+E.card+
      (F 0 ∩ C).card+(F 2 ∩ C).card+(F 3 ∩ C).card+3 ≤ c := by
    intro hh
    have hr := hrep 1 2 (by simpa [L,in1245_small_blocks] using hh)
    dsimp at hr
    simp [hE3,L,forb,in1245_small_blocks,Fin.sum_univ_four,hC,h1A,h2A,h3A,h1D,h2D,h3D] at hr
    omega
  have hrep2C : 1 ≤ (F 2 ∩ C).card →
      (F 0 ∩ A).card+(F 0 ∩ B).card+(F 1 ∩ B).card+(F 3 ∩ B).card+E.card+
      (F 0 ∩ C).card+(F 1 ∩ C).card+(F 3 ∩ C).card+3 ≤ c := by
    intro hh
    have hr := hrep 2 2 (by simpa [L,in1245_small_blocks] using hh)
    dsimp at hr
    simp [hE3,L,forb,in1245_small_blocks,Fin.sum_univ_four,hC,h1A,h2A,h3A,h1D,h2D,h3D] at hr
    omega
  have hrep3C : 1 ≤ (F 3 ∩ C).card →
      (F 0 ∩ A).card+(F 0 ∩ B).card+(F 1 ∩ B).card+(F 2 ∩ B).card+E.card+
      (F 0 ∩ C).card+(F 1 ∩ C).card+(F 2 ∩ C).card+3 ≤ c := by
    intro hh
    have hr := hrep 3 2 (by simpa [L,in1245_small_blocks] using hh)
    dsimp at hr
    simp [hE3,L,forb,in1245_small_blocks,Fin.sum_univ_four,hC,h1A,h2A,h3A,h1D,h2D,h3D] at hr
    omega
  have hcrit' : ((F 0 ∩ B).card+(F 1 ∩ B).card+(F 2 ∩ B).card+(F 3 ∩ B).card+E.card+5 < 2*k →
      J.card+(F 0 ∩ B).card+(F 1 ∩ B).card+(F 2 ∩ B).card+(F 3 ∩ B).card+E.card+6 ≤ 2*k) ∧
    ((F 0 ∩ B).card+(F 1 ∩ B).card+(F 2 ∩ B).card+(F 3 ∩ B).card+E.card+5 = 2*k → J.card ≤ 1 ∧
      (if 1 ≤ (F 0 ∩ B).card then 1 else 0)+(if 1 ≤ (F 1 ∩ B).card then 1 else 0)+
      (if 1 ≤ (F 2 ∩ B).card then 1 else 0)+(if 1 ≤ (F 3 ∩ B).card then 1 else 0)+J.card ≤ 1) := by
    dsimp at hcrit
    simp only [Fin.sum_univ_four] at hcrit
    simp [L,in1245_small_blocks,hB] at hcrit
    have hz (i : Fin 4) : (1 ≤ (F i ∩ B).card) ↔ (F i ∩ B).Nonempty := by
      rw [← Finset.card_pos]
      omega
    simp only [hz]
    omega
  have hsplit := five_odd_saturated_small_shore_arithmetic_no_connectedness
    k c J.card E.card (F 0 ∩ A).card (F 0 ∩ B).card (F 1 ∩ B).card (F 2 ∩ B).card (F 3 ∩ B).card
    (F 0 ∩ C).card (F 1 ∩ C).card (F 2 ∩ C).card (F 3 ∩ C).card (F 0 ∩ D).card
    hc hkc heb ha hc1 he2 he3 ho0 ho1 hs hb htotal hsmall hroot hrepA hrep0C hcutD hrep1C hrep2C hrep3C hcrit'
  have hpool : E.card=J.card → J.card=0 := by
    intro heq
    have hm : J.card ≤ k := by omega
    have he : ((if 1 ≤ (F 2 ∩ C).card then 1 else 0) +
      (if 1 ≤ (F 3 ∩ C).card then 1 else 0)) ≤ 2 := by split_ifs <;> omega
    exact saturated_small_shore_singleton_pool_empty k
      ((if 1 ≤ (F 2 ∩ C).card then 1 else 0) + (if 1 ≤ (F 3 ∩ C).card then 1 else 0)) G
      hext (fun v => by have := hdegree v; omega) hind hsep A B E F J R hA hAB hEB hnoAB
      hFdis hFA hEdis hEanti hRsub hRne hRdis hRanti (by omega) hm heq hsplit.1 he
  have hout := saturated_positive_small_shore_forces_two_singleton_groups
    k c J.card E.card (F 0 ∩ A).card (F 0 ∩ B).card (F 1 ∩ B).card (F 2 ∩ B).card (F 3 ∩ B).card
    (F 0 ∩ C).card (F 1 ∩ C).card (F 2 ∩ C).card (F 3 ∩ C).card (F 0 ∩ D).card
    hc hkc heb ha hc1 he2 he3 ho0 ho1 hs hspos hb htotal hsmall hroot hrepA hrep0C hcutD hrep1C hrep2C hrep3C hcrit' hpool
  exact ⟨Finset.card_pos.mp (by omega),Finset.card_pos.mp (by omega)⟩
