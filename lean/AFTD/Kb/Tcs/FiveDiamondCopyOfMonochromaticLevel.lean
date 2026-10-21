import AFTD.Prelude

/-!
# five_diamond_copy_of_monochromatic_level

Topic: combinatorics   Node: 8b8178885577

Provenance: helper lemma. step towards five_diamond_ramsey_property_at_four_mul

If level m is monochromatic of color col and there exist B ⊆ T of color col with |B| + 2 = m = |T| - 2, then there exist 5 middle sets forming an induced monochromatic 5-diamond copy.
-/

/-- If level m is monochromatic of color col and there exist B ⊆ T of color col with |B| + 2 = m = |T| - 2, then there exist 5 middle sets forming an induced monochromatic 5-diamond copy. -/
theorem five_diamond_copy_of_monochromatic_level
    (d k : ℕ) (c : Finset (Fin d) → Fin k) (col : Fin k) (m : ℕ)
    (h_level : ∀ A : Finset (Fin d), A.card = m → c A = col)
    (B T : Finset (Fin d)) (hB : c B = col) (hT : c T = col)
    (hBT : B ⊆ T) (hB_card : B.card + 2 = m) (hT_card : T.card = m + 2) :
    ∃ (M : Fin 5 → Finset (Fin d)),
      c B = col ∧ c T = col ∧
      (∀ i, c (M i) = col) ∧
      B ⊂ T ∧
      (∀ i, B ⊂ M i ∧ M i ⊂ T) ∧
      (∀ i i', i ≠ i' → ¬ (M i ⊆ M i')) := by
  have hTB_card : (T \ B).card = 4 := by
    have := Finset.card_sdiff_of_subset hBT
    omega
  have hP_card : ((T \ B).powersetCard 2).card = 6 := by
    rw [Finset.card_powersetCard, hTB_card]
    rfl
  obtain ⟨s, hs_sub, hs_card⟩ : ∃ s ⊆ (T \ B).powersetCard 2, s.card = 5 := by
    apply Finset.exists_subset_card_eq
    omega
  let e := (Finset.equivFinOfCardEq hs_card).symm
  let M : Fin 5 → Finset (Fin d) := fun i => B ∪ (e i).val
  have h_mem (i : Fin 5) : (e i).val ∈ (T \ B).powersetCard 2 := hs_sub (e i).2
  have h_sub (i : Fin 5) : (e i).val ⊆ T \ B := (Finset.mem_powersetCard.mp (h_mem i)).1
  have h_disj (i : Fin 5) : Disjoint B (e i).val := Finset.disjoint_sdiff.mono_right (h_sub i)
  have h_card_ei (i : Fin 5) : ((e i).val).card = 2 := (Finset.mem_powersetCard.mp (h_mem i)).2
  have hM_card (i : Fin 5) : (M i).card = m := by
    show (B ∪ (e i).val).card = m
    rw [Finset.card_union_of_disjoint (h_disj i), h_card_ei i]
    omega
  have hBT_ssub : B ⊂ T := by
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hBT, by rintro rfl; omega⟩
  refine ⟨M, hB, hT, fun i => h_level (M i) (hM_card i), hBT_ssub, ?_, ?_⟩
  · intro i
    have hMi := hM_card i
    refine ⟨?_, ?_⟩
    · rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, ?_⟩
      rintro h
      have : (M i).card = B.card := by rw [← h]
      omega
    · rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro x hx
        have hx' : x ∈ B ∪ (e i).val := hx
        rcases Finset.mem_union.mp hx' with hxB | hx_ei
        · exact hBT hxB
        · have := h_sub i hx_ei
          exact (Finset.mem_sdiff.mp this).1
      · rintro h
        have : (M i).card = T.card := by rw [h]
        omega
  · intro i i' hne hsub
    have heq : M i = M i' := Finset.eq_of_subset_of_card_le hsub (by rw [hM_card, hM_card])
    have h_cancel : ((B ∪ (e i).val) \ B) = ((B ∪ (e i').val) \ B) := by
      change (M i \ B) = (M i' \ B)
      rw [heq]
    rw [Finset.union_sdiff_cancel_left (h_disj i), Finset.union_sdiff_cancel_left (h_disj i')] at h_cancel
    have he_eq : e i = e i' := Subtype.ext h_cancel
    have hi_eq : i = i' := e.injective he_eq
    exact hne hi_eq
