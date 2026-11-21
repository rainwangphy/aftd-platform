import AFTD.Prelude
import AFTD.Kb.Tcs.FourShoreEvenCrossingIsContained
import AFTD.Kb.Tcs.D11EightSelectedSixShoreMeetsFirst

/-!
# d11_eight_selected_six_shore_unique

Topic: graphs   Node: 96fbb6256210

Provenance: helper lemma. OP-1957; structural subcase for the saturated-twin k=8 branch.

In the displayed degree-eleven crossing-shore relaxation with eight selected roots, a distinguished four-shore, and three or four internal opposite-shore vertices: Any two selected six-shores are equal.
-/

theorem d11_eight_selected_six_shore_unique
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C F : Finset V) (hC : C.card = 18) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card = 10) (hF : F ⊆ C) (hFcard : F.card = 8)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ F, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ F, Q z ⊆ S ∪ C) (hW : ∀ z ∈ F, W z ⊆ S)
    (hxQ : ∀ z ∈ F, x ∉ Q z) (hyQ : ∀ z ∈ F, y ∉ Q z)
    (hsize : ∀ z ∈ F, (Q z).card + (W z).card = 12)
    (hzQ : ∀ z ∈ F, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ F, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ F, 4 ≤ (W z).card) (hWeven : ∀ z ∈ F, Even (W z).card)
    (hcutrule : ∀ z ∈ F, ∀ z' ∈ F, (W z ∩ W z').Nonempty →
      (W z ∪ W z').card + (Q z ∩ Q z').card = 12 ∧ Even (W z ∩ W z').card)
    (z₀ : V) (hz₀ : z₀ ∈ F) (hz₀four : (W z₀).card = 4)
    (hinner : 3 ≤ (Q z₀ ∩ S).card ∧ (Q z₀ ∩ S).card ≤ 4) : ∀ z ∈ F, ∀ z' ∈ F, (W z).card = 6 → (W z').card = 6 → W z = W z' := by
  have hW0_sub : ∀ z ∈ F, (W z).card = 6 → W z₀ ⊆ W z := by
    intro z hz hWz6
    have hW0z_ne : (W z₀ ∩ W z).Nonempty :=
      d11_eight_selected_six_shore_meets_first H x y hxy S C F hC hSC hxC hyC hS hF hFcard
        hmax hSxy Q W hdis hQ hW hxQ hyQ hsize hzQ hcross hWmin hWeven hcutrule z₀ hz₀ hz₀four hinner z hz hWz6
    have hcr := hcutrule z₀ hz₀ z hz hW0z_ne
    have hQ0card : (Q z₀).card = 8 := by
      have := hsize z₀ hz₀; omega
    have hWQ : (W z).card + (Q z).card = 12 := by
      have := hsize z hz; omega
    exact four_shore_even_crossing_is_contained H x y hxy S (W z₀) (Q z₀) (W z) (Q z)
      (hW z₀ hz₀) hz₀four hQ0card hWQ hcr.1 hW0z_ne hcr.2
      (hxQ z₀ hz₀) (hyQ z₀ hz₀) (hxQ z hz) (hyQ z hz)
      hmax hSxy (fun b hb a ha => hcross z₀ hz₀ b hb a ha)
      (fun q hq w hw => hcross z hz q hq w hw)
  have hxS : x ∉ S := fun h => H.irrefl (hSxy x h).1
  have hyS : y ∉ S := fun h => H.irrefl (hSxy y h).2
  have hWQ_disj_Q0 : ∀ z ∈ F, (W z).card = 6 → W z ∩ Q z₀ = ∅ := by
    intro z hz hWz6
    have hW0z_sub := hW0_sub z hz hWz6
    have hQzcard : (Q z).card = 6 := by
      have := hsize z hz; omega
    by_contra h_ne
    have h_nonempty : (W z ∩ Q z₀).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_ne
    rcases h_nonempty with ⟨d, hd⟩
    have hdW : d ∈ W z := (Finset.mem_inter.mp hd).1
    have hdQ0 : d ∈ Q z₀ := (Finset.mem_inter.mp hd).2
    have hdS : d ∈ S := hW z hz hdW
    have hxy_sub : {x, y} ⊆ H.neighborFinset d := by
      intro v hv
      rcases Finset.mem_insert.mp hv with hvx | hvy
      · rw [hvx]
        exact (H.mem_neighborFinset d x).mpr (hSxy d hdS).1
      · rw [Finset.mem_singleton.mp hvy]
        exact (H.mem_neighborFinset d y).mpr (hSxy d hdS).2
    have hW0_sub_d : W z₀ ⊆ H.neighborFinset d := by
      intro w hw
      exact (H.mem_neighborFinset d w).mpr (hcross z₀ hz₀ d hdQ0 w hw)
    have hQz_sub_d : Q z ⊆ H.neighborFinset d := by
      intro q hq
      exact (H.mem_neighborFinset d q).mpr (hcross z hz q hq d hdW).symm
    have hWQ_sub : W z₀ ∪ Q z ⊆ H.neighborFinset d := Finset.union_subset hW0_sub_d hQz_sub_d
    have hWQ_disj : Disjoint (W z₀) (Q z) := by
      apply Finset.disjoint_left.mpr
      intro w hw hwQ
      have hwW : w ∈ W z := hW0z_sub hw
      exact (Finset.disjoint_left.mp (hdis z hz)) hwQ hwW
    have hxy_disj : Disjoint {x, y} (W z₀ ∪ Q z) := by
      apply Finset.disjoint_left.mpr
      intro v hv
      rcases Finset.mem_insert.mp hv with hvx | hvy
      · rw [hvx]
        intro hxWQ
        rcases Finset.mem_union.mp hxWQ with hxW0 | hxQz
        · exact hxS (hW z₀ hz₀ hxW0)
        · exact hxQ z hz hxQz
      · rw [Finset.mem_singleton.mp hvy]
        intro hyWQ
        rcases Finset.mem_union.mp hyWQ with hyW0 | hyQz
        · exact hyS (hW z₀ hz₀ hyW0)
        · exact hyQ z hz hyQz
    have htot_sub : {x, y} ∪ (W z₀ ∪ Q z) ⊆ H.neighborFinset d :=
      Finset.union_subset hxy_sub hWQ_sub
    have htot_card : ({x, y} ∪ (W z₀ ∪ Q z)).card = 12 := by
      rw [Finset.card_union_of_disjoint hxy_disj, Finset.card_pair hxy]
      rw [Finset.card_union_of_disjoint hWQ_disj, hz₀four, hQzcard]
    have hdeg : 12 ≤ (H.neighborFinset d).card := by
      have := Finset.card_le_card htot_sub
      omega
    have := hmax d
    omega
  intro z hz z' hz' hWz6 hWz'6
  have hW0z_sub := hW0_sub z hz hWz6
  have hW0z'_sub := hW0_sub z' hz' hWz'6
  have hW0_ne : (W z₀).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at hz₀four
    omega
  rcases hW0_ne with ⟨w₀, hw₀⟩
  have h_inter_ne : (W z ∩ W z').Nonempty :=
    ⟨w₀, Finset.mem_inter.mpr ⟨hW0z_sub hw₀, hW0z'_sub hw₀⟩⟩
  have hcr := hcutrule z hz z' hz' h_inter_ne
  have heven := hcr.2
  have hAQ0 := hWQ_disj_Q0 z hz hWz6
  have hBQ0 := hWQ_disj_Q0 z' hz' hWz'6
  have hA_sub : W z ⊆ S \ (Q z₀ ∩ S) := by
    intro a ha
    rw [Finset.mem_sdiff, Finset.mem_inter]
    refine ⟨hW z hz ha, ?_⟩
    intro ⟨hq, _⟩
    have : a ∈ W z ∩ Q z₀ := Finset.mem_inter.mpr ⟨ha, hq⟩
    rw [hAQ0] at this
    exact Finset.notMem_empty a this
  have hB_sub : W z' ⊆ S \ (Q z₀ ∩ S) := by
    intro b hb
    rw [Finset.mem_sdiff, Finset.mem_inter]
    refine ⟨hW z' hz' hb, ?_⟩
    intro ⟨hq, _⟩
    have : b ∈ W z' ∩ Q z₀ := Finset.mem_inter.mpr ⟨hb, hq⟩
    rw [hBQ0] at this
    exact Finset.notMem_empty b this
  have hU_sub : W z ∪ W z' ⊆ S \ (Q z₀ ∩ S) := Finset.union_subset hA_sub hB_sub
  have hcard_sdiff : (S \ (Q z₀ ∩ S)).card = S.card - (Q z₀ ∩ S).card :=
    Finset.card_sdiff_of_subset Finset.inter_subset_right
  have hU_card : (W z ∪ W z').card ≤ 7 := by
    have h1 := Finset.card_le_card hU_sub
    omega
  have hsum := Finset.card_union_add_card_inter (W z) (W z')
  have hI_ge : 5 ≤ (W z ∩ W z').card := by omega
  have hI_le : (W z ∩ W z').card ≤ 6 := by
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := W z) (s₂ := W z'))
    omega
  have hI_card : (W z ∩ W z').card = 6 := by
    rcases heven with ⟨k, hk⟩
    omega
  have hI_eq : W z ∩ W z' = W z :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hI_card, hWz6])
  have hI_eq' : W z ∩ W z' = W z' :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hI_card, hWz'6])
  rw [← hI_eq, hI_eq']
