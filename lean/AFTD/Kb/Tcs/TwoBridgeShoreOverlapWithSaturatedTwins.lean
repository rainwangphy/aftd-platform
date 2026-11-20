import AFTD.Prelude

/-!
# two_bridge_shore_overlap_with_saturated_twins

Topic: graphs   Node: e68b9f19fcb8

Provenance: helper lemma. Two-critical-edge overlap reduction for the saturated-twin branch of OP-1957; finite compatibility tests in experiment 35071.

Let H have maximum degree seven and adjacent true twins x,y. Let Q₁,Q₂,W₁,W₂ each have four vertices, with x,y outside both Q sets, W₁,W₂ contained in the neighbors of x other than y, and each Qᵢ complete to Wᵢ. Let distinct vertices z₁,z₂, both different from x, be nonneighbors of x, absent from both Q sets, and adjacent to every vertex in Q₁ and Q₂ respectively. Suppose H has no four vertices with identical open neighborhoods and degree seven. Then either both pairs of sets agree, or each pair overlaps in exactly three vertices; in the latter case the common Q vertices all have neighborhood (W₁ ∪ W₂) ∪ {z₁,z₂}, and the common W vertices all have neighborhood (Q₁ ∪ Q₂) ∪ {x,y}.
-/

theorem two_bridge_shore_overlap_with_saturated_twins
    {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (x y z₁ z₂ : Fin n) (Q₁ Q₂ W₁ W₂ : Finset (Fin n))
    (hxy : H.Adj x y) (hz : z₁ ≠ z₂)
    (hz₁x : z₁ ≠ x) (hz₂x : z₂ ≠ x)
    (hxz₁ : ¬ H.Adj x z₁) (hxz₂ : ¬ H.Adj x z₂)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 7)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a))
    (hq₁x : x ∉ Q₁) (hq₂x : x ∉ Q₂)
    (hq₁y : y ∉ Q₁) (hq₂y : y ∉ Q₂)
    (hz₁q₁ : z₁ ∉ Q₁) (hz₁q₂ : z₁ ∉ Q₂)
    (hz₂q₁ : z₂ ∉ Q₁) (hz₂q₂ : z₂ ∉ Q₂)
    (hw₁ : W₁ ⊆ (H.neighborFinset x).erase y)
    (hw₂ : W₂ ⊆ (H.neighborFinset x).erase y)
    (hcross₁ : ∀ q ∈ Q₁, ∀ w ∈ W₁, H.Adj q w)
    (hcross₂ : ∀ q ∈ Q₂, ∀ w ∈ W₂, H.Adj q w)
    (hqz₁ : ∀ q ∈ Q₁, H.Adj q z₁)
    (hqz₂ : ∀ q ∈ Q₂, H.Adj q z₂)
    (hq₁ : Q₁.card = 4) (hq₂ : Q₂.card = 4)
    (hw₁c : W₁.card = 4) (hw₂c : W₂.card = 4)
    (hfour : ∀ T : Finset (Fin n), T.card = 4 →
      (∀ a ∈ T, (H.neighborFinset a).card = 7) →
      ¬ (∀ a ∈ T, ∀ b ∈ T, H.neighborFinset a = H.neighborFinset b)) :
    (Q₁ = Q₂ ∧ W₁ = W₂) ∨
      ((Q₁ ∩ Q₂).card = 3 ∧ (W₁ ∩ W₂).card = 3 ∧
       (∀ q ∈ Q₁ ∩ Q₂, H.neighborFinset q = W₁ ∪ W₂ ∪ {z₁, z₂}) ∧
       (∀ w ∈ W₁ ∩ W₂, H.neighborFinset w = Q₁ ∪ Q₂ ∪ {x, y})) := by
  -- ===== basic =====
  have hyNx : y ∈ H.neighborFinset x := by rw [H.mem_neighborFinset]; exact hxy
  have hWsub : W₁ ∪ W₂ ⊆ (H.neighborFinset x).erase y := Finset.union_subset hw₁ hw₂
  have hb6 : (W₁ ∪ W₂).card ≤ 6 := by
    have h1 := Finset.card_le_card hWsub
    rw [Finset.card_erase_of_mem hyNx] at h1
    have h2 := hmax x
    omega
  have hWinter : (W₁ ∩ W₂).Nonempty := by
    rw [← Finset.card_pos]
    have hcard := Finset.card_inter W₁ W₂
    rw [hw₁c, hw₂c] at hcard
    omega
  obtain ⟨w₀, hw₀mem⟩ := hWinter
  rw [Finset.mem_inter] at hw₀mem
  obtain ⟨hw₀₁, hw₀₂⟩ := hw₀mem
  -- ===== a <= 5 =====
  have ha5 : (Q₁ ∪ Q₂).card ≤ 5 := by
    have hw₀erase : w₀ ∈ (H.neighborFinset x).erase y := hw₁ hw₀₁
    rw [Finset.mem_erase] at hw₀erase
    obtain ⟨hw₀ne_y, hw₀N⟩ := hw₀erase
    have hAdjxw : H.Adj x w₀ := (H.mem_neighborFinset x w₀).mp hw₀N
    have hw₀ne_x : w₀ ≠ x := by intro h; exact hAdjxw.ne h.symm
    have hAdjw₀x : H.Adj w₀ x := hAdjxw.symm
    have hAdjw₀y : H.Adj w₀ y := ((htwin w₀ hw₀ne_x hw₀ne_y).mp hAdjxw).symm
    have hSsub : ({x, y} : Finset (Fin n)) ∪ (Q₁ ∪ Q₂) ⊆ H.neighborFinset w₀ := by
      intro a ha'
      rw [Finset.mem_union] at ha'
      rcases ha' with ha' | ha'
      · rw [Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with rfl | rfl
        · rw [H.mem_neighborFinset]; exact hAdjw₀x
        · rw [H.mem_neighborFinset]; exact hAdjw₀y
      · rw [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · rw [H.mem_neighborFinset]; exact (hcross₁ a ha' w₀ hw₀₁).symm
        · rw [H.mem_neighborFinset]; exact (hcross₂ a ha' w₀ hw₀₂).symm
    have hxnot : x ∉ Q₁ ∪ Q₂ := by simp only [Finset.mem_union, not_or]; exact ⟨hq₁x, hq₂x⟩
    have hynot : y ∉ Q₁ ∪ Q₂ := by simp only [Finset.mem_union, not_or]; exact ⟨hq₁y, hq₂y⟩
    have hdisj : Disjoint ({x, y} : Finset (Fin n)) (Q₁ ∪ Q₂) := by
      rw [Finset.disjoint_left]
      intro a ha' haq
      rw [Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl
      · exact hxnot haq
      · exact hynot haq
    have hSc : (({x, y} : Finset (Fin n)) ∪ (Q₁ ∪ Q₂)).card = 2 + (Q₁ ∪ Q₂).card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hxy.ne]
    have hc := Finset.card_le_card hSsub
    rw [hSc] at hc
    have := hmax w₀
    omega
  -- ===== Q intersection nonempty =====
  have hQinter : (Q₁ ∩ Q₂).Nonempty := by
    rw [← Finset.card_pos]
    have hcard := Finset.card_inter Q₁ Q₂
    rw [hq₁, hq₂] at hcard
    omega
  obtain ⟨q₀, hq₀mem⟩ := hQinter
  rw [Finset.mem_inter] at hq₀mem
  obtain ⟨hq₀₁, hq₀₂⟩ := hq₀mem
  -- ===== b <= 5 =====
  have hb5 : (W₁ ∪ W₂).card ≤ 5 := by
    have hz₁W1 : z₁ ∉ W₁ := by
      intro h
      have := hw₁ h
      rw [Finset.mem_erase] at this
      exact hxz₁ ((H.mem_neighborFinset x z₁).mp this.2)
    have hz₁W2 : z₁ ∉ W₂ := by
      intro h
      have := hw₂ h
      rw [Finset.mem_erase] at this
      exact hxz₁ ((H.mem_neighborFinset x z₁).mp this.2)
    have hz₂W1 : z₂ ∉ W₁ := by
      intro h
      have := hw₁ h
      rw [Finset.mem_erase] at this
      exact hxz₂ ((H.mem_neighborFinset x z₂).mp this.2)
    have hz₂W2 : z₂ ∉ W₂ := by
      intro h
      have := hw₂ h
      rw [Finset.mem_erase] at this
      exact hxz₂ ((H.mem_neighborFinset x z₂).mp this.2)
    have hz₁not : z₁ ∉ W₁ ∪ W₂ := by simp only [Finset.mem_union, not_or]; exact ⟨hz₁W1, hz₁W2⟩
    have hz₂not : z₂ ∉ W₁ ∪ W₂ := by simp only [Finset.mem_union, not_or]; exact ⟨hz₂W1, hz₂W2⟩
    have hSsub : ({z₁, z₂} : Finset (Fin n)) ∪ (W₁ ∪ W₂) ⊆ H.neighborFinset q₀ := by
      intro a ha'
      rw [Finset.mem_union] at ha'
      rcases ha' with ha' | ha'
      · rw [Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with rfl | rfl
        · rw [H.mem_neighborFinset]; exact hqz₁ q₀ hq₀₁
        · rw [H.mem_neighborFinset]; exact hqz₂ q₀ hq₀₂
      · rw [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · rw [H.mem_neighborFinset]; exact hcross₁ q₀ hq₀₁ a ha'
        · rw [H.mem_neighborFinset]; exact hcross₂ q₀ hq₀₂ a ha'
    have hdisj : Disjoint ({z₁, z₂} : Finset (Fin n)) (W₁ ∪ W₂) := by
      rw [Finset.disjoint_left]
      intro a ha' haq
      rw [Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl
      · exact hz₁not haq
      · exact hz₂not haq
    have hSc : (({z₁, z₂} : Finset (Fin n)) ∪ (W₁ ∪ W₂)).card = 2 + (W₁ ∪ W₂).card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hz]
    have hc := Finset.card_le_card hSsub
    rw [hSc] at hc
    have := hmax q₀
    omega
  have ha4 : 4 ≤ (Q₁ ∪ Q₂).card := by
    have := Finset.card_le_card (Finset.subset_union_left : Q₁ ⊆ Q₁ ∪ Q₂)
    omega
  have hb4 : 4 ≤ (W₁ ∪ W₂).card := by
    have := Finset.card_le_card (Finset.subset_union_left : W₁ ⊆ W₁ ∪ W₂)
    omega
  have ha_cases : (Q₁ ∪ Q₂).card = 4 ∨ (Q₁ ∪ Q₂).card = 5 := by omega
  have hb_cases : (W₁ ∪ W₂).card = 4 ∨ (W₁ ∪ W₂).card = 5 := by omega
  rcases ha_cases with ha | ha <;> rcases hb_cases with hb | hb
  · -- a = 4, b = 4
    left
    refine ⟨?_, ?_⟩
    · have h1 : Q₁ = Q₁ ∪ Q₂ := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by rw [ha, hq₁])
      have h2 : Q₂ = Q₁ ∪ Q₂ := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by rw [ha, hq₂])
      exact h1.trans h2.symm
    · have h1 : W₁ = W₁ ∪ W₂ := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by rw [hb, hw₁c])
      have h2 : W₂ = W₁ ∪ W₂ := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by rw [hb, hw₂c])
      exact h1.trans h2.symm
  · -- a = 4, b = 5 : contradiction
    exfalso
    have hQeq : Q₁ = Q₂ := by
      have h1 : Q₁ = Q₁ ∪ Q₂ := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by rw [ha, hq₁])
      have h2 : Q₂ = Q₁ ∪ Q₂ := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by rw [ha, hq₂])
      exact h1.trans h2.symm
    have hz₁not : z₁ ∉ W₁ ∪ W₂ := by
      rw [Finset.mem_union]; intro h; rcases h with h | h
      · have := hw₁ h; rw [Finset.mem_erase] at this
        exact hxz₁ ((H.mem_neighborFinset x z₁).mp this.2)
      · have := hw₂ h; rw [Finset.mem_erase] at this
        exact hxz₁ ((H.mem_neighborFinset x z₁).mp this.2)
    have hz₂not : z₂ ∉ W₁ ∪ W₂ := by
      rw [Finset.mem_union]; intro h; rcases h with h | h
      · have := hw₁ h; rw [Finset.mem_erase] at this
        exact hxz₂ ((H.mem_neighborFinset x z₂).mp this.2)
      · have := hw₂ h; rw [Finset.mem_erase] at this
        exact hxz₂ ((H.mem_neighborFinset x z₂).mp this.2)
    have hdisj : Disjoint ({z₁, z₂} : Finset (Fin n)) (W₁ ∪ W₂) := by
      rw [Finset.disjoint_left]
      intro a ha' haq
      rw [Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl
      · exact hz₁not haq
      · exact hz₂not haq
    have hScard' : (({z₁, z₂} : Finset (Fin n)) ∪ (W₁ ∪ W₂)).card = 7 := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hz, hb]
    have keyeq : ∀ q ∈ Q₁, H.neighborFinset q = ({z₁, z₂} : Finset (Fin n)) ∪ (W₁ ∪ W₂) := by
      intro q hq
      have hq₂' : q ∈ Q₂ := by rw [← hQeq]; exact hq
      have hSsub : ({z₁, z₂} : Finset (Fin n)) ∪ (W₁ ∪ W₂) ⊆ H.neighborFinset q := by
        intro a ha'
        rw [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · rw [Finset.mem_insert, Finset.mem_singleton] at ha'
          rcases ha' with rfl | rfl
          · rw [H.mem_neighborFinset]; exact hqz₁ q hq
          · rw [H.mem_neighborFinset]; exact hqz₂ q hq₂'
        · rw [Finset.mem_union] at ha'
          rcases ha' with ha' | ha'
          · rw [H.mem_neighborFinset]; exact hcross₁ q hq a ha'
          · rw [H.mem_neighborFinset]; exact hcross₂ q hq₂' a ha'
      exact (Finset.eq_of_subset_of_card_le hSsub (by rw [hScard']; exact hmax q)).symm
    exact hfour Q₁ hq₁ (fun a ha' => by rw [keyeq a ha', hScard'])
      (fun a ha' b hb' => by rw [keyeq a ha', keyeq b hb'])
  · -- a = 5, b = 4 : contradiction
    exfalso
    have hWeq : W₁ = W₂ := by
      have h1 : W₁ = W₁ ∪ W₂ := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by rw [hb, hw₁c])
      have h2 : W₂ = W₁ ∪ W₂ := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by rw [hb, hw₂c])
      exact h1.trans h2.symm
    have hxnot : x ∉ Q₁ ∪ Q₂ := by simp only [Finset.mem_union, not_or]; exact ⟨hq₁x, hq₂x⟩
    have hynot : y ∉ Q₁ ∪ Q₂ := by simp only [Finset.mem_union, not_or]; exact ⟨hq₁y, hq₂y⟩
    have hdisjX : Disjoint ({x, y} : Finset (Fin n)) (Q₁ ∪ Q₂) := by
      rw [Finset.disjoint_left]
      intro a ha' haq
      rw [Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl
      · exact hxnot haq
      · exact hynot haq
    have hScardX : (({x, y} : Finset (Fin n)) ∪ (Q₁ ∪ Q₂)).card = 7 := by
      rw [Finset.card_union_of_disjoint hdisjX, Finset.card_pair hxy.ne, ha]
    have keyeq : ∀ w ∈ W₁, H.neighborFinset w = ({x, y} : Finset (Fin n)) ∪ (Q₁ ∪ Q₂) := by
      intro w hw
      have hw₂' : w ∈ W₂ := by rw [← hWeq]; exact hw
      have hw₁erase : w ∈ (H.neighborFinset x).erase y := hw₁ hw
      rw [Finset.mem_erase] at hw₁erase
      obtain ⟨hwne_y, hwN⟩ := hw₁erase
      have hAdjxw : H.Adj x w := (H.mem_neighborFinset x w).mp hwN
      have hwne_x : w ≠ x := by intro h; exact hAdjxw.ne h.symm
      have hAdjwx : H.Adj w x := hAdjxw.symm
      have hAdjwy : H.Adj w y := ((htwin w hwne_x hwne_y).mp hAdjxw).symm
      have hSsub : ({x, y} : Finset (Fin n)) ∪ (Q₁ ∪ Q₂) ⊆ H.neighborFinset w := by
        intro a ha'
        rw [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · rw [Finset.mem_insert, Finset.mem_singleton] at ha'
          rcases ha' with rfl | rfl
          · rw [H.mem_neighborFinset]; exact hAdjwx
          · rw [H.mem_neighborFinset]; exact hAdjwy
        · rw [Finset.mem_union] at ha'
          rcases ha' with ha' | ha'
          · rw [H.mem_neighborFinset]; exact (hcross₁ a ha' w hw).symm
          · rw [H.mem_neighborFinset]; exact (hcross₂ a ha' w hw₂').symm
      exact (Finset.eq_of_subset_of_card_le hSsub (by rw [hScardX]; exact hmax w)).symm
    exact hfour W₁ hw₁c (fun a ha' => by rw [keyeq a ha', hScardX])
      (fun a ha' b hb' => by rw [keyeq a ha', keyeq b hb'])
  · -- a = 5, b = 5 : conclusion
    right
    have hz₁not : z₁ ∉ W₁ ∪ W₂ := by
      rw [Finset.mem_union]; intro h; rcases h with h | h
      · have := hw₁ h; rw [Finset.mem_erase] at this
        exact hxz₁ ((H.mem_neighborFinset x z₁).mp this.2)
      · have := hw₂ h; rw [Finset.mem_erase] at this
        exact hxz₁ ((H.mem_neighborFinset x z₁).mp this.2)
    have hz₂not : z₂ ∉ W₁ ∪ W₂ := by
      rw [Finset.mem_union]; intro h; rcases h with h | h
      · have := hw₁ h; rw [Finset.mem_erase] at this
        exact hxz₂ ((H.mem_neighborFinset x z₂).mp this.2)
      · have := hw₂ h; rw [Finset.mem_erase] at this
        exact hxz₂ ((H.mem_neighborFinset x z₂).mp this.2)
    have hdisjZ : Disjoint ({z₁, z₂} : Finset (Fin n)) (W₁ ∪ W₂) := by
      rw [Finset.disjoint_left]
      intro a ha' haq
      rw [Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl
      · exact hz₁not haq
      · exact hz₂not haq
    have hScardW : (({z₁, z₂} : Finset (Fin n)) ∪ (W₁ ∪ W₂)).card = 7 := by
      rw [Finset.card_union_of_disjoint hdisjZ, Finset.card_pair hz, hb]
    have hQcard3 : (Q₁ ∩ Q₂).card = 3 := by
      have h := Finset.card_inter Q₁ Q₂
      rw [hq₁, hq₂, ha] at h; omega
    have hWcard3 : (W₁ ∩ W₂).card = 3 := by
      have h := Finset.card_inter W₁ W₂
      rw [hw₁c, hw₂c, hb] at h; omega
    have hNq : ∀ q ∈ Q₁ ∩ Q₂, H.neighborFinset q = W₁ ∪ W₂ ∪ {z₁, z₂} := by
      intro q hq'
      rw [Finset.mem_inter] at hq'
      obtain ⟨hq₁', hq₂'⟩ := hq'
      have hSsub : ({z₁, z₂} : Finset (Fin n)) ∪ (W₁ ∪ W₂) ⊆ H.neighborFinset q := by
        intro a ha'
        rw [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · rw [Finset.mem_insert, Finset.mem_singleton] at ha'
          rcases ha' with rfl | rfl
          · rw [H.mem_neighborFinset]; exact hqz₁ q hq₁'
          · rw [H.mem_neighborFinset]; exact hqz₂ q hq₂'
        · rw [Finset.mem_union] at ha'
          rcases ha' with ha' | ha'
          · rw [H.mem_neighborFinset]; exact hcross₁ q hq₁' a ha'
          · rw [H.mem_neighborFinset]; exact hcross₂ q hq₂' a ha'
      have heq : ({z₁, z₂} : Finset (Fin n)) ∪ (W₁ ∪ W₂) = H.neighborFinset q :=
        Finset.eq_of_subset_of_card_le hSsub (by rw [hScardW]; exact hmax q)
      rw [← heq, Finset.union_comm]
    have hxnot : x ∉ Q₁ ∪ Q₂ := by simp only [Finset.mem_union, not_or]; exact ⟨hq₁x, hq₂x⟩
    have hynot : y ∉ Q₁ ∪ Q₂ := by simp only [Finset.mem_union, not_or]; exact ⟨hq₁y, hq₂y⟩
    have hNw : ∀ w ∈ W₁ ∩ W₂, H.neighborFinset w = Q₁ ∪ Q₂ ∪ {x, y} := by
      intro w hw'
      rw [Finset.mem_inter] at hw'
      obtain ⟨hw₁', hw₂'⟩ := hw'
      have hw₁erase : w ∈ (H.neighborFinset x).erase y := hw₁ hw₁'
      rw [Finset.mem_erase] at hw₁erase
      obtain ⟨hwne_y, hwN⟩ := hw₁erase
      have hAdjxw : H.Adj x w := (H.mem_neighborFinset x w).mp hwN
      have hwne_x : w ≠ x := by intro h; exact hAdjxw.ne h.symm
      have hAdjwx : H.Adj w x := hAdjxw.symm
      have hAdjwy : H.Adj w y := ((htwin w hwne_x hwne_y).mp hAdjxw).symm
      have hSsub : ({x, y} : Finset (Fin n)) ∪ (Q₁ ∪ Q₂) ⊆ H.neighborFinset w := by
        intro a ha'
        rw [Finset.mem_union] at ha'
        rcases ha' with ha' | ha'
        · rw [Finset.mem_insert, Finset.mem_singleton] at ha'
          rcases ha' with rfl | rfl
          · rw [H.mem_neighborFinset]; exact hAdjwx
          · rw [H.mem_neighborFinset]; exact hAdjwy
        · rw [Finset.mem_union] at ha'
          rcases ha' with ha' | ha'
          · rw [H.mem_neighborFinset]; exact (hcross₁ a ha' w hw₁').symm
          · rw [H.mem_neighborFinset]; exact (hcross₂ a ha' w hw₂').symm
      have hdisjX : Disjoint ({x, y} : Finset (Fin n)) (Q₁ ∪ Q₂) := by
        rw [Finset.disjoint_left]
        intro a ha' haq
        rw [Finset.mem_insert, Finset.mem_singleton] at ha'
        rcases ha' with rfl | rfl
        · exact hxnot haq
        · exact hynot haq
      have hScardX : (({x, y} : Finset (Fin n)) ∪ (Q₁ ∪ Q₂)).card = 7 := by
        rw [Finset.card_union_of_disjoint hdisjX, Finset.card_pair hxy.ne, ha]
      have heq : ({x, y} : Finset (Fin n)) ∪ (Q₁ ∪ Q₂) = H.neighborFinset w :=
        Finset.eq_of_subset_of_card_le hSsub (by rw [hScardX]; exact hmax w)
      rw [← heq, Finset.union_comm]
    exact ⟨hQcard3, hWcard3, hNq, hNw⟩
