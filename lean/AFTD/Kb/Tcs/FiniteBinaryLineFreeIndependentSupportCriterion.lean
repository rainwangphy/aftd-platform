import AFTD.Prelude

/-!
# finite_binary_line_free_independent_support_criterion

Topic: graphs   Node: f88521d22cdb

Provenance: helper lemma. Conflict-graph support reduction in the triangle packing-cover campaign.

For a finite binary line family covered by a 3k-point set U, if U contains at least k points avoiding singleton-forced points, pair-sum conflicts and full lines, then their complement in U is a cover of size at most 2k.
-/

private lemma finite_binary_line_free_independent_support_criterion_third_point
    {n : ℕ} {t : Finset (Fin n → ZMod 2)}
    (hcard : t.card = 3) (hsum : t.sum id = 0)
    {x y : Fin n → ZMod 2} (hx : x ∈ t) (hy : y ∈ t) (hxy : x ≠ y) :
    ∃ z, z ∈ t ∧ z ∉ ({x, y} : Finset (Fin n → ZMod 2)) ∧
      t = ({x, y, z} : Finset (Fin n → ZMod 2)) ∧ z = x + y := by
  have hsub : ({x, y} : Finset (Fin n → ZMod 2)) ⊆ t := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hx
    · exact hy
  have hcardpair : ({x, y} : Finset (Fin n → ZMod 2)).card = 2 := by
    simp [hxy]
  have hcarddiff : (t \ ({x, y} : Finset (Fin n → ZMod 2))).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard, hcardpair]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcarddiff
  have hzmem : z ∈ t \ ({x, y} : Finset (Fin n → ZMod 2)) := by
    rw [hz]
    simp
  have hzt : z ∈ t := (Finset.mem_sdiff.mp hzmem).1
  have hznot : z ∉ ({x, y} : Finset (Fin n → ZMod 2)) := (Finset.mem_sdiff.mp hzmem).2
  have hxz : x ≠ z := by
    intro h
    exact hznot (by simp [h])
  have hyz : y ≠ z := by
    intro h
    exact hznot (by simp [h])
  have ht_eq : t = ({x, y, z} : Finset (Fin n → ZMod 2)) := by
    ext a
    constructor
    · intro ha
      by_cases h : a ∈ ({x, y} : Finset (Fin n → ZMod 2))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
        rcases h with rfl | rfl
        · simp
        · simp
      · have hmem : a ∈ t \ ({x, y} : Finset (Fin n → ZMod 2)) :=
          Finset.mem_sdiff.mpr ⟨ha, h⟩
        rw [hz] at hmem
        simp only [Finset.mem_singleton] at hmem
        subst a
        simp
    · intro ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hzt
  have hxnot : x ∉ ({y, z} : Finset (Fin n → ZMod 2)) := by
    simp [hxy, hxz]
  have hynot : y ∉ ({z} : Finset (Fin n → ZMod 2)) := by
    simp [hyz]
  have hsum3 : x + y + z = 0 := by
    rw [ht_eq] at hsum
    rw [Finset.sum_insert hxnot, Finset.sum_insert hynot, Finset.sum_singleton] at hsum
    simpa only [id_eq, add_assoc] using hsum
  have hz_eq : z = x + y := by
    have h := neg_eq_of_add_eq_zero_right hsum3
    have hneg : -(x + y) = x + y := by
      funext i
      exact CharTwo.neg_eq ((x + y) i)
    rw [hneg] at h
    exact h.symm
  exact ⟨z, hzt, hznot, ht_eq, hz_eq⟩

theorem finite_binary_line_free_independent_support_criterion
    (n k : ℕ) (S U I : Finset (Fin n → ZMod 2))
    (F : Finset (Finset (Fin n → ZMod 2)))
    (hF : ∀ t : Finset (Fin n → ZMod 2),
      t ∈ F ↔ t ⊆ S ∧ t.card = 3 ∧ t.sum id = 0)
    (hcover : ∀ t ∈ F, ¬ Disjoint U t)
    (hcardU : U.card = 3 * k) (hIU : I ⊆ U) (hcardI : k ≤ I.card)
    (hsingle : ∀ t ∈ F, (t ∩ U).card = 1 → Disjoint I t)
    (hpair : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → x + y ∉ S \ U)
    (hlinefree : ∀ t ∈ F, ¬ t ⊆ I) :
    (U \ I).card ≤ 2 * k ∧ ∀ t ∈ F, ¬ Disjoint (U \ I) t := by
  constructor
  · rw [Finset.card_sdiff_of_subset hIU, hcardU]
    omega
  · intro t ht
    intro hdisj
    have htS : t ⊆ S := ((hF t).mp ht).1
    have htcard : t.card = 3 := ((hF t).mp ht).2.1
    have htsum : t.sum id = 0 := ((hF t).mp ht).2.2
    have hsubI : t ∩ U ⊆ I := by
      intro a ha
      have hat : a ∈ t := (Finset.mem_inter.mp ha).1
      have hau : a ∈ U := (Finset.mem_inter.mp ha).2
      by_contra haI
      have haUS : a ∈ U \ I := Finset.mem_sdiff.mpr ⟨hau, haI⟩
      have hamem : a ∈ (U \ I) ∩ t := Finset.mem_inter.mpr ⟨haUS, hat⟩
      have hdisj_eq : (U \ I) ∩ t = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
      rw [hdisj_eq] at hamem
      simpa using hamem
    obtain ⟨a, haU, hat⟩ := Finset.not_disjoint_iff.mp (hcover t ht)
    have haInter : a ∈ t ∩ U := Finset.mem_inter.mpr ⟨hat, haU⟩
    have hpos : 0 < (t ∩ U).card := Finset.card_pos.mpr ⟨a, haInter⟩
    have hle : (t ∩ U).card ≤ 3 := by
      calc
        (t ∩ U).card ≤ t.card := Finset.card_le_card Finset.inter_subset_left
        _ = 3 := htcard
    have hcases : (t ∩ U).card = 1 ∨ (t ∩ U).card = 2 ∨ (t ∩ U).card = 3 := by
      omega
    rcases hcases with hcard1 | hcard2 | hcard3
    · have hdisjIt : Disjoint I t := hsingle t ht hcard1
      have haI : a ∈ I := hsubI haInter
      have hamem : a ∈ I ∩ t := Finset.mem_inter.mpr ⟨haI, hat⟩
      have hdisj_eq : I ∩ t = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisjIt
      rw [hdisj_eq] at hamem
      simpa using hamem
    · obtain ⟨x, y, hxy, h_inter⟩ := Finset.card_eq_two.mp hcard2
      have hxInter : x ∈ t ∩ U := by rw [h_inter]; simp
      have hyInter : y ∈ t ∩ U := by rw [h_inter]; simp
      have hxt : x ∈ t := (Finset.mem_inter.mp hxInter).1
      have hyt : y ∈ t := (Finset.mem_inter.mp hyInter).1
      have hxI : x ∈ I := hsubI hxInter
      have hyI : y ∈ I := hsubI hyInter
      obtain ⟨z, hzt, hznotpair, ht_eq, hz_eq⟩ :=
        finite_binary_line_free_independent_support_criterion_third_point htcard htsum hxt hyt hxy
      have hznotU : z ∉ U := by
        intro hzU
        have hzInter : z ∈ t ∩ U := Finset.mem_inter.mpr ⟨hzt, hzU⟩
        rw [h_inter] at hzInter
        exact hznotpair hzInter
      have hzS : z ∈ S := htS hzt
      have hzSdiff : z ∈ S \ U := Finset.mem_sdiff.mpr ⟨hzS, hznotU⟩
      have hpair' : x + y ∉ S \ U := hpair x hxI y hyI hxy
      rw [hz_eq] at hzSdiff
      exact hpair' hzSdiff
    · have ht_eq_inter : t ∩ U = t := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        rw [htcard, hcard3]
      have htI : t ⊆ I := by
        intro x hx
        apply hsubI
        rw [ht_eq_inter]
        exact hx
      exact hlinefree t ht htI
