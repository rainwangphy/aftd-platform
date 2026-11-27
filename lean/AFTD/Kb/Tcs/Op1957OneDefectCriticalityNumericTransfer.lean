import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957FactorcriticalSingleExceptionParityBound
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_one_defect_criticality_numeric_transfer

Topic: graphs   Node: da228b939198

Provenance: helper lemma. OP-1957: one-defect boundary graph-to-count transfer, arXiv:2611.22690

The displayed factor-critical, four-block and single-exception hypotheses imply the sharp parity inequality in the one-defect scalar contradiction.
-/

theorem op1957_one_defect_criticality_numeric_transfer
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B C D X Y : Finset V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (k : ℕ) (hB : B.card + 5 = 2*k)
    (K : Finset I) (T : I → Finset V)
    (hcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hXY : Disjoint X Y)
    (hXT : ∀ i ∈ K, Disjoint X (T i)) (hYT : ∀ i ∈ K, Disjoint Y (T i))
    (hTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (T i) (T j))
    (hantiXY : ∀ u ∈ X ∩ B, ∀ v ∈ Y ∩ B, ¬ G.Adj u v)
    (hantiXT : ∀ i ∈ K, ∀ u ∈ X, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiYT : ∀ i ∈ K, ∀ u ∈ Y, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, ¬ G.Adj u v)
    (hYB : (Y ∩ B).Nonempty) (hoddT : ∀ i ∈ K, Odd (T i).card)
    (j : I) (hj : j ∈ K) (hother : ∀ i ∈ K, i ≠ j → T i ⊆ B) :
    let U := K.biUnion T
    K.card + (if ((U ∩ A).card+(U ∩ C).card+(U ∩ D).card)%2=0 then 1 else 0) +
      (if (X ∩ B).card%2=1 then 1 else 0) +
      (X ∩ B).card+(Y ∩ B).card+(U ∩ B).card+4 ≤ 2*k := by
  classical
  let U := K.biUnion T
  let R := X ∪ Y ∪ U
  have hbound := op1957_factorcritical_single_exception_parity_bound G B X Y K T
    hcrit hXY hXT hYT hTT hantiXY hantiXT hantiYT hantiTT hYB hoddT j hj hother
  change K.card + (if Even (U \ B).card then 1 else 0) +
      (if Odd ((X ∩ B).card) then 1 else 0) + (B ∩ R).card ≤ B.card + 1 at hbound
  have hXU : Disjoint X U := (Finset.disjoint_biUnion_right X K T).mpr hXT
  have hYU : Disjoint Y U := (Finset.disjoint_biUnion_right Y K T).mpr hYT
  have hXYU : Disjoint (X ∪ Y) U := Finset.disjoint_union_left.mpr ⟨hXU,hYU⟩
  have hXB_YB : Disjoint (X ∩ B) (Y ∩ B) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left (Finset.disjoint_of_subset_right Finset.inter_subset_left hXY)
  have hXYB_UB : Disjoint ((X ∪ Y) ∩ B) (U ∩ B) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left (Finset.disjoint_of_subset_right Finset.inter_subset_left hXYU)
  have hinter : (B ∩ R).card = (X ∩ B).card+(Y ∩ B).card+(U ∩ B).card := by
    rw [Finset.inter_comm B R]
    dsimp only [R]
    rw [Finset.union_inter_distrib_right,Finset.card_union_of_disjoint hXYB_UB,
      Finset.union_inter_distrib_right,Finset.card_union_of_disjoint hXB_YB]
  have hsplit := finset_card_eq_sum_four_block_inter A B C D U hAB hAC hAD hBC hBD hCD hcover
  have hdiff := Finset.card_inter_add_card_sdiff U B
  have hout : (U \ B).card = (U ∩ A).card+(U ∩ C).card+(U ∩ D).card := by omega
  rw [hinter,hout] at hbound
  simp only [Nat.even_iff,Nat.odd_iff] at hbound
  change K.card + (if ((U ∩ A).card+(U ∩ C).card+(U ∩ D).card)%2=0 then 1 else 0) +
      (if (X ∩ B).card%2=1 then 1 else 0) +
      (X ∩ B).card+(Y ∩ B).card+(U ∩ B).card+4 ≤ 2*k
  omega
