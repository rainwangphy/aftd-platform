import AFTD.Prelude
import AFTD.Kb.Tcs.FourShoreEvenCrossingIsContained

/-!
# d11_eight_selected_six_shore_meets_first

Topic: graphs   Node: c5328c199b76

Provenance: helper lemma. OP-1957; structural subcase for the saturated-twin k=8 branch.

In the displayed degree-eleven crossing-shore relaxation with eight selected roots, a distinguished four-shore, and three or four internal opposite-shore vertices: Every selected six-shore meets the distinguished four-shore.
-/

theorem d11_eight_selected_six_shore_meets_first
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
    (hinner : 3 ≤ (Q z₀ ∩ S).card ∧ (Q z₀ ∩ S).card ≤ 4) : ∀ z ∈ F, (W z).card = 6 → (W z₀ ∩ W z).Nonempty := by
  intro z hz hWz6
  by_contra h_empty_ne
  have h_empty : W z₀ ∩ W z = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty_ne
  have hxS : x ∉ S := by
    intro hxS
    exact H.irrefl (hSxy x hxS).1
  have hyS : y ∉ S := by
    intro hyS
    exact H.irrefl (hSxy y hyS).2
  have hQ₀card : (Q z₀).card = 8 := by
    have hs := hsize z₀ hz₀; omega
  have hQzcard : (Q z).card = 6 := by
    have hs := hsize z hz; omega
  have hW₀Qz : W z₀ ∩ Q z = ∅ := by
    by_contra h_inter
    have h_ne : (W z₀ ∩ Q z).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_inter
    rcases h_ne with ⟨a, ha⟩
    have haW₀ : a ∈ W z₀ := (Finset.mem_inter.mp ha).1
    have haQz : a ∈ Q z := (Finset.mem_inter.mp ha).2
    have haS : a ∈ S := hW z₀ hz₀ haW₀
    have hQ₀_sub : Q z₀ ⊆ H.neighborFinset a := by
      intro q hq
      exact (H.mem_neighborFinset a q).mpr (hcross z₀ hz₀ q hq a haW₀).symm
    have hWz_sub : W z ⊆ H.neighborFinset a := by
      intro w hw
      exact (H.mem_neighborFinset a w).mpr (hcross z hz a haQz w hw)
    have hQW_sub : Q z₀ ∪ W z ⊆ H.neighborFinset a := Finset.union_subset hQ₀_sub hWz_sub
    have hQW_inter_sub : Q z₀ ∩ W z ⊆ Q z₀ ∩ S := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hW z hz (Finset.mem_inter.mp hv).2⟩
    have hQW_inter_le : (Q z₀ ∩ W z).card ≤ 4 := by
      have h1 := Finset.card_le_card hQW_inter_sub
      omega
    have hQW_card_ge : 10 ≤ (Q z₀ ∪ W z).card := by
      have hsum := Finset.card_union_add_card_inter (Q z₀) (W z)
      omega
    have hxy_sub : {x, y} ⊆ H.neighborFinset a := by
      intro v hv
      rcases Finset.mem_insert.mp hv with hvx | hvy
      · rw [hvx]
        exact (H.mem_neighborFinset a x).mpr (hSxy a haS).1
      · rw [Finset.mem_singleton.mp hvy]
        exact (H.mem_neighborFinset a y).mpr (hSxy a haS).2
    have hxy_disj : Disjoint {x, y} (Q z₀ ∪ W z) := by
      apply Finset.disjoint_left.mpr
      intro v hv
      rcases Finset.mem_insert.mp hv with hvx | hvy
      · rw [hvx]
        intro hxQW
        rcases Finset.mem_union.mp hxQW with hxQ₀ | hxW
        · exact hxQ z₀ hz₀ hxQ₀
        · exact hxS (hW z hz hxW)
      · rw [Finset.mem_singleton.mp hvy]
        intro hyQW
        rcases Finset.mem_union.mp hyQW with hyQ₀ | hyW
        · exact hyQ z₀ hz₀ hyQ₀
        · exact hyS (hW z hz hyW)
    have htot_sub : {x, y} ∪ (Q z₀ ∪ W z) ⊆ H.neighborFinset a :=
      Finset.union_subset hxy_sub hQW_sub
    have htot_card : ({x, y} ∪ (Q z₀ ∪ W z)).card = 2 + (Q z₀ ∪ W z).card := by
      rw [Finset.card_union_of_disjoint hxy_disj, Finset.card_pair hxy]
    have hdeg : 12 ≤ (H.neighborFinset a).card := by
      have hle := Finset.card_le_card htot_sub
      omega
    have hmaxa := hmax a
    omega
  have hWdisj : Disjoint (W z₀) (W z) := Finset.disjoint_iff_inter_eq_empty.mpr h_empty
  have hWunion_sub : W z₀ ∪ W z ⊆ S := Finset.union_subset (hW z₀ hz₀) (hW z hz)
  have hWunion_card : (W z₀ ∪ W z).card = 10 := by
    rw [Finset.card_union_of_disjoint hWdisj, hz₀four, hWz6]
  have hWunion_eq : W z₀ ∪ W z = S := Finset.eq_of_subset_of_card_le hWunion_sub (by rw [hWunion_card, hS])
  have hb_nonempty : (Q z₀ ∩ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at hinner
    omega
  rcases hb_nonempty with ⟨b, hb⟩
  have hbQ₀ : b ∈ Q z₀ := (Finset.mem_inter.mp hb).1
  have hbS : b ∈ S := (Finset.mem_inter.mp hb).2
  have hbWz : b ∈ W z := by
    have hbU : b ∈ W z₀ ∪ W z := by rwa [hWunion_eq]
    rcases Finset.mem_union.mp hbU with hbW₀ | hbWz
    · have := (Finset.disjoint_left.mp (hdis z₀ hz₀)) hbQ₀ hbW₀
      contradiction
    · exact hbWz
  have hxy_sub_b : {x, y} ⊆ H.neighborFinset b := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hvx | hvy
    · rw [hvx]
      exact (H.mem_neighborFinset b x).mpr (hSxy b hbS).1
    · rw [Finset.mem_singleton.mp hvy]
      exact (H.mem_neighborFinset b y).mpr (hSxy b hbS).2
  have hW₀_sub_b : W z₀ ⊆ H.neighborFinset b := by
    intro w hw
    exact (H.mem_neighborFinset b w).mpr (hcross z₀ hz₀ b hbQ₀ w hw)
  have hQz_sub_b : Q z ⊆ H.neighborFinset b := by
    intro q hq
    exact (H.mem_neighborFinset b q).mpr (hcross z hz q hq b hbWz).symm
  have hWQ_disj : Disjoint (W z₀) (Q z) := Finset.disjoint_iff_inter_eq_empty.mpr hW₀Qz
  have hWQ_sub_b : W z₀ ∪ Q z ⊆ H.neighborFinset b := Finset.union_subset hW₀_sub_b hQz_sub_b
  have hxy_disj_b : Disjoint {x, y} (W z₀ ∪ Q z) := by
    apply Finset.disjoint_left.mpr
    intro v hv
    rcases Finset.mem_insert.mp hv with hvx | hvy
    · rw [hvx]
      intro hxWQ
      rcases Finset.mem_union.mp hxWQ with hxW₀ | hxQz
      · exact hxS (hW z₀ hz₀ hxW₀)
      · exact hxQ z hz hxQz
    · rw [Finset.mem_singleton.mp hvy]
      intro hyWQ
      rcases Finset.mem_union.mp hyWQ with hyW₀ | hyQz
      · exact hyS (hW z₀ hz₀ hyW₀)
      · exact hyQ z hz hyQz
  have htot_sub_b : {x, y} ∪ (W z₀ ∪ Q z) ⊆ H.neighborFinset b :=
    Finset.union_subset hxy_sub_b hWQ_sub_b
  have htot_card_b : ({x, y} ∪ (W z₀ ∪ Q z)).card = 12 := by
    rw [Finset.card_union_of_disjoint hxy_disj_b, Finset.card_pair hxy]
    rw [Finset.card_union_of_disjoint hWQ_disj, hz₀four, hQzcard]
  have hdeg_b : 12 ≤ (H.neighborFinset b).card := by
    have hle := Finset.card_le_card htot_sub_b
    omega
  have hmaxb := hmax b
  omega
