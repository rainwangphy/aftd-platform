import AFTD.Prelude

/-!
# repeated_four_shore_endpoint_and_opposite_count

Topic: graphs   Node: 723224a4562b

Provenance: helper lemma. OP-1957 four-shore crossing and repeated-shore analysis; scratch Lean axiom audit completed.

The number of repeated first-four-shore endpoints plus an external opposite shore has size at most seven.
-/

theorem repeated_four_shore_endpoint_and_opposite_count
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S C A B R : Finset V) (Q W : V → Finset V)
    (hSC : Disjoint S C) (hA : A ⊆ S) (hR : R ⊆ C)
    (hAcard : A.card=4) (hBcard : B.card=8) (hBS : (B ∩ S).card ≤ 2)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, H.Adj b a)
    (hQR : ∀ r ∈ R, Q r = B) (hrQ : ∀ r ∈ R, ∀ q ∈ Q r, H.Adj r q)
    (hW : ∀ e ∈ B ∩ C, W e ⊆ S)
    (hW6 : ∀ e ∈ B ∩ C, 6 ≤ (W e).card)
    (havoid : ∀ e ∈ B ∩ C, Disjoint A (Q e))
    (heQ : ∀ e ∈ B ∩ C, ∀ q ∈ Q e, H.Adj e q)
    (hcross : ∀ e ∈ B ∩ C, ∀ q ∈ Q e, ∀ w ∈ W e, H.Adj q w) :
    ∀ e ∈ B ∩ C, R.card + (Q e).card ≤ 7 := by
  classical
  intro e he
  have hRinternal : ∀ r ∈ R, ((H.neighborFinset r) ∩ S).card ≤ 5 := by
    intro r hr
    let N := H.neighborFinset r
    have hBN : B ⊆ N := by
      intro b hb
      apply (H.mem_neighborFinset r b).mpr
      exact hrQ r hr b ((hQR r hr).symm ▸ hb)
    have hsub : B ∪ (N ∩ S) ⊆ N := by
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact hBN hb
      · exact (Finset.mem_inter.mp hb).1
    have hint : B ∩ (N ∩ S) = B ∩ S := by
      ext b
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hb,_,hs⟩
        exact ⟨hb,hs⟩
      · rintro ⟨hb,hs⟩
        exact ⟨hb,hBN hb,hs⟩
    have hsum := Finset.card_union_add_card_inter B (N ∩ S)
    rw [hint] at hsum
    have hc := Finset.card_le_card hsub
    have hm := hmax r
    dsimp [N] at *
    omega
  have heB : e ∈ B := (Finset.mem_inter.mp he).1
  have hRQ : Disjoint R (Q e) := by
    apply Finset.disjoint_left.mpr
    intro r hr hrQ
    have hwsub : W e ⊆ (H.neighborFinset r) ∩ S := by
      intro w hw
      exact Finset.mem_inter.mpr ⟨by simpa using hcross e he r hrQ w hw,hW e he hw⟩
    have hc := Finset.card_le_card hwsub
    have hsmall := hRinternal r hr
    have hlarge := hW6 e he
    omega
  have hAR : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro a ha hr
    exact (Finset.disjoint_left.mp hSC) (hA ha) (hR hr)
  have hAQ := havoid e he
  have hAQR : Disjoint (A ∪ Q e) R := Finset.disjoint_union_left.mpr ⟨hAR,hRQ.symm⟩
  have hsub : (A ∪ Q e) ∪ R ⊆ H.neighborFinset e := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · exact (H.mem_neighborFinset e a).mpr (hBA e heB a ha)
      · exact (H.mem_neighborFinset e a).mpr (heQ e he a ha)
    · have h := hrQ a ha e ((hQR a ha).symm ▸ heB)
      exact (H.mem_neighborFinset e a).mpr h.symm
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hAQR,Finset.card_union_of_disjoint hAQ,hAcard] at hc
  have hm := hmax e
  omega
