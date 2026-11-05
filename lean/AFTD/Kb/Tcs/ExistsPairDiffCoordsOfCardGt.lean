import AFTD.Prelude

/-!
# exists_pair_diff_coords_of_card_gt

Topic: combinatorics   Node: fcb42ec451ff

Provenance: helper lemma. arXiv:2611.03878 Theorem 3.1

Every finite subset S of Fin m × Fin m with cardinality strictly greater than m contains two elements that differ in both coordinates.
-/

lemma exists_pair_diff_coords_of_card_gt_card_le_of_fst_inj {m : ℕ} {S : Finset (Fin m × Fin m)}
    (h : ∀ u ∈ S, ∀ v ∈ S, u.1 = v.1 → u = v) : S.card ≤ m := by
  have h_inj : Set.InjOn Prod.fst (↑S : Set (Fin m × Fin m)) := fun u hu v hv huv => h u hu v hv huv
  have h_maps : Set.MapsTo Prod.fst (↑S : Set (Fin m × Fin m)) (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := fun _ _ => by simp
  simpa using Finset.card_le_card_of_injOn Prod.fst h_maps h_inj

lemma exists_pair_diff_coords_of_card_gt_card_le_of_snd_inj {m : ℕ} {S : Finset (Fin m × Fin m)}
    (h : ∀ u ∈ S, ∀ v ∈ S, u.2 = v.2 → u = v) : S.card ≤ m := by
  have h_inj : Set.InjOn Prod.snd (↑S : Set (Fin m × Fin m)) := fun u hu v hv huv => h u hu v hv huv
  have h_maps : Set.MapsTo Prod.snd (↑S : Set (Fin m × Fin m)) (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := fun _ _ => by simp
  simpa using Finset.card_le_card_of_injOn Prod.snd h_maps h_inj

/-- Any subset of Fin m × Fin m of cardinality strictly greater than m contains two elements with both coordinates different. -/
theorem exists_pair_diff_coords_of_card_gt {m : ℕ} {S : Finset (Fin m × Fin m)} (hS : m < S.card) :
  ∃ u ∈ S, ∃ v ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 := by
  by_contra h
  push Not at h
  by_cases h_fst : ∀ u ∈ S, ∀ v ∈ S, u.1 = v.1
  · have h_inj : ∀ u ∈ S, ∀ v ∈ S, u.2 = v.2 → u = v := by
      intro u hu v hv huv
      exact Prod.ext (h_fst u hu v hv) huv
    have := exists_pair_diff_coords_of_card_gt_card_le_of_snd_inj h_inj
    omega
  · push Not at h_fst
    rcases h_fst with ⟨a, ha, b, hb, hab⟩
    have hab2 : a.2 = b.2 := h a ha b hb hab
    have h_snd : ∀ w ∈ S, w.2 = a.2 := by
      intro w hw
      by_cases hwa : w.1 = a.1
      · have hwb : w.1 ≠ b.1 := by
          intro hwb_eq
          exact hab (hwa.symm.trans hwb_eq)
        have := h w hw b hb hwb
        rw [this, ← hab2]
      · exact h w hw a ha hwa
    have h_inj : ∀ u ∈ S, ∀ v ∈ S, u.1 = v.1 → u = v := by
      intro u hu v hv huv
      exact Prod.ext huv ((h_snd u hu).trans (h_snd v hv).symm)
    have := exists_pair_diff_coords_of_card_gt_card_le_of_fst_inj h_inj
    omega
