import AFTD.Prelude

/-!
# op861_selector_palette_lower_bound

Topic: graphs   Node: 56964ae90cf7

Provenance: helper lemma. A used-palette restriction for the standard-list coloring in arXiv:2610.42094; the case of two size-six palettes at k=6, r=3 is illustrated by experiment 26970.

In any pair of proper standard-list selectors at positive k and threshold r, each selector uses at least k+r distinct colors.
-/

open Finset in
theorem op861_selector_palette_lower_bound_one_side (k r : ℕ) (hk : 1 ≤ k)
    (f g : {S : Finset (Fin (2*k-1)) // S.card = k} → Fin (2*k-1))
    (hf : ∀ S, f S ∈ S.val)
    (hg : ∀ S, g S ∈ S.val)
    (hfg : ∀ S T, (S.val ∩ T.val).card ≤ r → f S ≠ g T) :
    k + r ≤ (Finset.univ.image f).card := by
  set P := Finset.univ.image f
  have hk_le : k ≤ P.card := by
    by_contra! hlt
    have hcompl : k ≤ Pᶜ.card := by
      rw [card_compl, Fintype.card_fin]
      omega
    obtain ⟨t, ht_sub, ht_card⟩ := exists_subset_card_eq hcompl
    let S : {S : Finset (Fin (2*k-1)) // S.card = k} := ⟨t, ht_card⟩
    have hfS_in_compl : f S ∈ Pᶜ := ht_sub (hf S)
    have hfS_in_P : f S ∈ P := mem_image_of_mem _ (mem_univ S)
    rw [mem_compl] at hfS_in_compl
    exact hfS_in_compl hfS_in_P
  by_contra! hlt
  set s := P.card - k
  have hPcard : P.card = k + s := by omega
  have hsr : s + 1 ≤ r := by omega
  have hPle : P.card ≤ 2 * k - 1 := by
    have h1 := card_le_card (subset_univ P)
    rw [card_univ, Fintype.card_fin] at h1
    exact h1
  have hc : Pᶜ.card = k - 1 - s := by
    rw [card_compl, Fintype.card_fin, hPcard]
    omega
  let S_of : (X : Finset (Fin (2*k-1))) → X ∈ P.powersetCard (s + 1) →
      {S : Finset (Fin (2*k-1)) // S.card = k} := fun X hX =>
    have hX' := mem_powersetCard.mp hX
    have hdisj : Disjoint X Pᶜ := disjoint_compl_right.mono_left hX'.1
    ⟨X ∪ Pᶜ, by rw [card_union_eq_card_add_card.2 hdisj, hX'.2, hc]; omega⟩
  let A := (P.powersetCard (s + 1)).attach.image (fun ⟨X, hX⟩ => f (S_of X hX))
  have hAP : A ⊆ P := by
    intro a ha
    simp only [A, mem_image, mem_attach, true_and, Subtype.exists] at ha
    obtain ⟨X, hX, rfl⟩ := ha
    exact mem_image_of_mem _ (mem_univ _)
  have hdiff : (P \ A).card ≤ s := by
    by_contra! hgt
    obtain ⟨X, hX_sub, hX_card⟩ := exists_subset_card_eq hgt
    have hXP : X ⊆ P := hX_sub.trans sdiff_subset
    have hX_mem : X ∈ P.powersetCard (s + 1) := by
      rw [mem_powersetCard]
      exact ⟨hXP, hX_card⟩
    have hf_in_X : f (S_of X hX_mem) ∈ X := by
      have h1 : f (S_of X hX_mem) ∈ (S_of X hX_mem).val := hf _
      rw [mem_union] at h1
      cases h1 with
      | inl hX_in => exact hX_in
      | inr hcompl =>
        have hP_in : f (S_of X hX_mem) ∈ P := mem_image_of_mem _ (mem_univ _)
        rw [mem_compl] at hcompl
        exact (hcompl hP_in).elim
    have hf_in_A : f (S_of X hX_mem) ∈ A := by
      simp only [A, mem_image, mem_attach, true_and, Subtype.exists]
      exact ⟨X, hX_mem, rfl⟩
    have hf_in_sdiff : f (S_of X hX_mem) ∈ P \ A := hX_sub hf_in_X
    rw [mem_sdiff] at hf_in_sdiff
    exact hf_in_sdiff.2 hf_in_A
  have hk_le_A : k ≤ A.card := by
    have := card_sdiff_add_card_eq_card hAP
    omega
  have hA_lt_k : A.card < k := by
    by_contra! hge
    obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hge
    have hTP : T ⊆ P := hTsub.trans hAP
    have hg_in_A : g ⟨T, hTcard⟩ ∈ A := hTsub (hg ⟨T, hTcard⟩)
    simp only [A, mem_image, mem_attach, true_and, Subtype.exists] at hg_in_A
    obtain ⟨X, hX_mem, hf_eq⟩ := hg_in_A
    have hX' := mem_powersetCard.mp hX_mem
    let S := S_of X hX_mem
    let T_sub : {S : Finset (Fin (2*k-1)) // S.card = k} := ⟨T, hTcard⟩
    have hinter : (S.val ∩ T_sub.val) = X ∩ T := by
      dsimp [S, S_of, T_sub]
      ext x
      simp only [mem_inter, mem_union, mem_compl]
      constructor
      · rintro ⟨h1 | h2, hxT⟩
        · exact ⟨h1, hxT⟩
        · exact (h2 (hTP hxT)).elim
      · rintro ⟨hxX, hxT⟩
        exact ⟨Or.inl hxX, hxT⟩
    have hcard_inter : (S.val ∩ T_sub.val).card ≤ r := by
      rw [hinter]
      have : (X ∩ T).card ≤ X.card := card_le_card inter_subset_left
      rw [hX'.2] at this
      omega
    have hne := hfg S T_sub hcard_inter
    exact hne hf_eq
  omega

theorem op861_selector_palette_lower_bound (k r : ℕ) (hk : 1 ≤ k) (f g : {S : Finset (Fin (2*k-1)) // S.card = k} → Fin (2*k-1)) (hf : ∀ S, f S ∈ S.val) (hg : ∀ S, g S ∈ S.val) (hfg : ∀ S T, (S.val ∩ T.val).card ≤ r → f S ≠ g T) : k+r ≤ (Finset.univ.image f).card ∧ k+r ≤ (Finset.univ.image g).card := by
  refine ⟨op861_selector_palette_lower_bound_one_side k r hk f g hf hg hfg, ?_⟩
  apply op861_selector_palette_lower_bound_one_side k r hk g f hg hf
  intro S T hST
  rw [Finset.inter_comm] at hST
  exact (hfg T S hST).symm
