import AFTD.Prelude

/-!
# finite_three_set_private_packing_conflict_degree_le_two

Topic: graphs   Node: 243f3d265572

Provenance: helper lemma. Elementary incidence counting in the triangle packing-cover campaign, related to arXiv:2610.15539, Section 1.

For two disjoint-within-family collections of triples P and W, if C meets each P-triple and each W-triple meets C in one point outside the union of P, then each triple in either family intersects at most two triples of the other family.
-/

private lemma finite_three_set_private_packing_conflict_degree_le_two_sdiff_card_le_two
    {α : Type*} [DecidableEq α] {s C : Finset α}
    (hs : s.card = 3) (h : (s ∩ C).Nonempty) : (s \ C).card ≤ 2 := by
  have hcard : (s \ C).card + (s ∩ C).card = s.card := by
    have hh := Finset.card_sdiff_add_card_eq_card (s := s ∩ C) (t := s) Finset.inter_subset_left
    rw [show s \ (s ∩ C) = s \ C by ext x; simp] at hh
    exact hh
  have hpos : 0 < (s ∩ C).card := h.card_pos
  omega

private lemma finite_three_set_private_packing_conflict_degree_le_two_sdiff_card_eq_two
    {α : Type*} [DecidableEq α] {t C : Finset α}
    (ht : t.card = 3) (h : (t ∩ C).card = 1) : (t \ C).card = 2 := by
  have hcard : (t \ C).card + (t ∩ C).card = t.card := by
    have hh := Finset.card_sdiff_add_card_eq_card (s := t ∩ C) (t := t) Finset.inter_subset_left
    rw [show t \ (t ∩ C) = t \ C by ext x; simp] at hh
    exact hh
  omega

private lemma finite_three_set_private_packing_conflict_degree_le_two_card_filter_not_disjoint_le_card_sdiff
    {α : Type*} [DecidableEq α] {X : Finset (Finset α)} {z C : Finset α}
    (a0 : α) (hXdis : (X : Set (Finset α)).Pairwise Disjoint)
    (hex : ∀ t ∈ X, ¬ Disjoint z t → ∃ x, x ∈ z \ C ∧ x ∈ t) :
    (X.filter (fun t => ¬ Disjoint z t)).card ≤ (z \ C).card := by
  classical
  let D := X.filter (fun t => ¬ Disjoint z t)
  have hDsub : D ⊆ X := Finset.filter_subset _ _
  let f : Finset α → α := fun t =>
    if h : ∃ x, x ∈ z \ C ∧ x ∈ t then Classical.choose h else a0
  have hf_maps : Set.MapsTo f ↑D ↑(z \ C) := by
    intro t ht
    have htX : t ∈ X := hDsub ht
    have hconf : ¬ Disjoint z t := (Finset.mem_filter.mp ht).2
    have h := hex t htX hconf
    have hft : f t = Classical.choose h := by
      dsimp [f]
      rw [dif_pos h]
    rw [hft]
    exact (Classical.choose_spec h).1
  have hf_inj : Set.InjOn f ↑D := by
    intro t1 ht1 t2 ht2 heq
    by_contra hne
    have ht1X : t1 ∈ X := hDsub ht1
    have ht2X : t2 ∈ X := hDsub ht2
    have hconf1 : ¬ Disjoint z t1 := (Finset.mem_filter.mp ht1).2
    have hconf2 : ¬ Disjoint z t2 := (Finset.mem_filter.mp ht2).2
    have h1 := hex t1 ht1X hconf1
    have h2 := hex t2 ht2X hconf2
    have hf1 : f t1 = Classical.choose h1 := by dsimp [f]; rw [dif_pos h1]
    have hf2 : f t2 = Classical.choose h2 := by dsimp [f]; rw [dif_pos h2]
    have hx1 : Classical.choose h1 ∈ t1 := (Classical.choose_spec h1).2
    have hx2 : Classical.choose h2 ∈ t2 := (Classical.choose_spec h2).2
    have hxmem2 : Classical.choose h1 ∈ t2 := by
      rw [← hf1, heq, hf2]
      exact hx2
    have hdis : Disjoint t1 t2 := hXdis ht1X ht2X hne
    exact (Finset.disjoint_left.mp hdis hx1 hxmem2).elim
  calc
    (X.filter (fun t => ¬ Disjoint z t)).card = D.card := rfl
    _ ≤ (z \ C).card := Finset.card_le_card_of_injOn f hf_maps hf_inj

theorem finite_three_set_private_packing_conflict_degree_le_two
    {α : Type*} [DecidableEq α] (P W : Finset (Finset α)) (C : Finset α)
    (hPsize : ∀ s ∈ P, s.card = 3) (hWsize : ∀ t ∈ W, t.card = 3)
    (hPdis : (P : Set (Finset α)).Pairwise Disjoint)
    (hWdis : (W : Set (Finset α)).Pairwise Disjoint)
    (hC : ∀ s ∈ P, ¬ Disjoint C s)
    (hprivate : ∀ t ∈ W, (t ∩ C).card = 1 ∧
      Disjoint (t ∩ C) (P.biUnion id)) :
    (∀ s ∈ P, (W.filter fun t => ¬ Disjoint s t).card ≤ 2) ∧
    (∀ t ∈ W, (P.filter fun s => ¬ Disjoint s t).card ≤ 2) := by
  classical
  constructor
  · intro s hsP
    let a0 : α := Classical.choose (Finset.card_pos.mp (by
      rw [hPsize s hsP]
      norm_num))
    have hex : ∀ t ∈ W, ¬ Disjoint s t → ∃ x, x ∈ s \ C ∧ x ∈ t := by
      intro t htW hconf
      have hnon : (s ∩ t).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hconf
      obtain ⟨x, hx⟩ := hnon
      rw [Finset.mem_inter] at hx
      refine ⟨x, ?_, hx.2⟩
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      intro hxC
      have hxTC : x ∈ t ∩ C := by
        rw [Finset.mem_inter]
        exact ⟨hx.2, hxC⟩
      have hxUnion : x ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨s, hsP, hx.1⟩
      have hdis := (hprivate t htW).2
      exact (Finset.disjoint_left.mp hdis hxTC hxUnion).elim
    have hle := finite_three_set_private_packing_conflict_degree_le_two_card_filter_not_disjoint_le_card_sdiff
      a0 hWdis hex
    have hnonC : (s ∩ C).Nonempty := by
      have h := Finset.not_disjoint_iff_nonempty_inter.mp (hC s hsP)
      simpa [Finset.inter_comm] using h
    have htarget : (s \ C).card ≤ 2 :=
      finite_three_set_private_packing_conflict_degree_le_two_sdiff_card_le_two (hPsize s hsP) hnonC
    exact le_trans hle htarget
  · intro t htW
    let a0 : α := Classical.choose (Finset.card_pos.mp (by
      rw [hWsize t htW]
      norm_num))
    have hex : ∀ s ∈ P, ¬ Disjoint t s → ∃ x, x ∈ t \ C ∧ x ∈ s := by
      intro s hsP hconf
      have hnon : (t ∩ s).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hconf
      obtain ⟨x, hx⟩ := hnon
      rw [Finset.mem_inter] at hx
      refine ⟨x, ?_, hx.2⟩
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      intro hxC
      have hxTC : x ∈ t ∩ C := by
        rw [Finset.mem_inter]
        exact ⟨hx.1, hxC⟩
      have hxUnion : x ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨s, hsP, hx.2⟩
      have hdis := (hprivate t htW).2
      exact (Finset.disjoint_left.mp hdis hxTC hxUnion).elim
    have hle := finite_three_set_private_packing_conflict_degree_le_two_card_filter_not_disjoint_le_card_sdiff
      a0 hPdis hex
    have hfilter : (P.filter fun s => ¬ Disjoint s t) =
        (P.filter fun s => ¬ Disjoint t s) := by
      apply Finset.filter_congr
      intro s hs
      exact not_congr (disjoint_comm (a := s) (b := t))
    rw [hfilter]
    have htarget : (t \ C).card = 2 :=
      finite_three_set_private_packing_conflict_degree_le_two_sdiff_card_eq_two
        (hWsize t htW) (hprivate t htW).1
    exact le_trans hle (le_of_eq htarget)
