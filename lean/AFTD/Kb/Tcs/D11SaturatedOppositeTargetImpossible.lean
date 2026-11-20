import AFTD.Prelude

/-!
# d11_saturated_opposite_target_impossible

Topic: graphs   Node: e60106ccc69f

Provenance: helper lemma. OP-1957 d=11 factor-critical bridge-family analysis; scratch Lean axiom audit completed.

A degree-saturated four-shore family obeys the displayed opposite-target neighborhood restriction.
-/

theorem d11_saturated_opposite_target_impossible
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S C A B : Finset V) (Q W : V → Finset V)
    (hSC : Disjoint S C) (hS : S.card=10) (hA : A ⊆ S) (hAcard : A.card=4)
    (hB : B ⊆ S ∪ C) (hBcard : B.card=8) (hBS : (B ∩ S).card ≤ 2)
    (hE : 6 ≤ (B ∩ C).card) (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (hQ4 : ∀ z ∈ C, 4 ≤ (Q z).card)
    (havoid : ∀ z ∈ C, Disjoint A (Q z))
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hnest : ∀ z ∈ C, (A ∩ W z).Nonempty → A ⊆ W z ∧ Q z ⊆ B)
    (hEsat : ∀ q ∈ B ∩ C, ∀ w ∈ S \ A, ¬ H.Adj q w) :
    ∀ t ∈ C, (∀ w ∈ S \ A, H.Adj t w) → False := by
  classical
  intro t ht htD
  let D := S \ A
  have hDsize : D.card=6 := by
    have hc := Finset.card_sdiff_add_card_eq_card hA
    dsimp [D]
    omega
  have hDC : Disjoint D C := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_sdiff.mp ha).1 hc
  have hDsub : D ⊆ H.neighborFinset t := by
    intro w hw
    exact (H.mem_neighborFinset t w).mpr (htD w hw)
  have hNbound : ((H.neighborFinset t) ∩ C).card ≤ 5 := by
    have hd : Disjoint D ((H.neighborFinset t) ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hDC) ha (Finset.mem_inter.mp hb).2
    have hs : D ∪ ((H.neighborFinset t) ∩ C) ⊆ H.neighborFinset t := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hDsub ha
      · exact (Finset.mem_inter.mp ha).1
    have hc := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint hd,hDsize] at hc
    have hm := hmax t
    omega
  have hQCS : (Q t ∩ S).card + (Q t ∩ C).card = (Q t).card := by
    have hd : Disjoint (Q t ∩ S) (Q t ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (Q t ∩ S) ∪ (Q t ∩ C) = Q t := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hQ t ht ha) with hs | hc
        · exact Or.inl ⟨ha,hs⟩
        · exact Or.inr ⟨ha,hc⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    exact hc
  have hQtC : (Q t ∩ C).card ≤ 5 := by
    have hs : Q t ∩ C ⊆ (H.neighborFinset t) ∩ C := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨by simpa using hzQ t ht a (Finset.mem_inter.mp ha).1,
        (Finset.mem_inter.mp ha).2⟩
    exact le_trans (Finset.card_le_card hs) hNbound
  by_cases hAW : (A ∩ W t).Nonempty
  · obtain ⟨hAWsub,hQB⟩ := hnest t ht hAW
    have hQinE : (Q t ∩ (B ∩ C)).Nonempty := by
      by_contra hn
      have hQno : ∀ q ∈ Q t, q ∉ C := by
        intro q hq hqc
        apply hn
        exact ⟨q,Finset.mem_inter.mpr ⟨hq,Finset.mem_inter.mpr ⟨hQB hq,hqc⟩⟩⟩
      have hs : Q t ⊆ B ∩ S := by
        intro q hq
        refine Finset.mem_inter.mpr ⟨hQB hq,?_⟩
        rcases Finset.mem_union.mp (hQ t ht hq) with hs | hc
        · exact hs
        · exact ((hQno q hq) hc).elim
      have hc := Finset.card_le_card hs
      have hq4 := hQ4 t ht
      omega
    obtain ⟨q,hq⟩ := hQinE
    have hqQ : q ∈ Q t := (Finset.mem_inter.mp hq).1
    have hqE : q ∈ B ∩ C := (Finset.mem_inter.mp hq).2
    have hWsub : W t ⊆ A := by
      intro w hw
      by_contra hn
      have hwD : w ∈ S \ A := Finset.mem_sdiff.mpr ⟨hW t ht hw,hn⟩
      exact hEsat q hqE w hwD (hcross t ht q hqQ w hw)
    have hWeq : W t = A := Finset.Subset.antisymm hWsub hAWsub
    have hQsize : (Q t).card = 8 := by
      have hs := hsize t ht
      rw [hWeq,hAcard] at hs
      omega
    have hQeq : Q t = B := Finset.eq_of_subset_of_card_le hQB (by omega)
    have hEsub : B ∩ C ⊆ H.neighborFinset t := by
      intro q hq
      have hqQ : q ∈ Q t := hQeq.symm ▸ (Finset.mem_inter.mp hq).1
      exact (H.mem_neighborFinset t q).mpr (hzQ t ht q hqQ)
    have hde : Disjoint D (B ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro w hw he
      exact (Finset.disjoint_left.mp hDC) hw (Finset.mem_inter.mp he).2
    have hsub : D ∪ (B ∩ C) ⊆ H.neighborFinset t := Finset.union_subset hDsub hEsub
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hde,hDsize] at hc
    have hm := hmax t
    omega
  · have hdisAW : Disjoint A (W t) := by
      apply Finset.disjoint_left.mpr
      intro a ha hw
      exact hAW ⟨a,Finset.mem_inter.mpr ⟨ha,hw⟩⟩
    have hdisQW : Disjoint (Q t ∩ S) (W t) := by
      apply Finset.disjoint_left.mpr
      intro a ha hw
      exact (Finset.disjoint_left.mp (hdis t ht)) (Finset.mem_inter.mp ha).1 hw
    have hsub : (Q t ∩ S) ∪ W t ⊆ D := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp ha).2,?_⟩
        intro haA
        exact (Finset.disjoint_left.mp (havoid t ht)) haA (Finset.mem_inter.mp ha).1
      · refine Finset.mem_sdiff.mpr ⟨hW t ht ha,?_⟩
        intro haA
        exact (Finset.disjoint_left.mp hdisAW) haA ha
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisQW,hDsize] at hc
    have hs := hsize t ht
    omega
