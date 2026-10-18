import AFTD.Prelude
import AFTD.Kb.Tcs.MdfrbfCompress

/-!
# mdfrbf_compress_subset_iff

Topic: combinatorics   Node: 0d778011cd82

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound_all_singletons_fan_colours

The compression map is an order embedding: for all sets A, A' of points outside W, T A ⊆ T A' holds if and only if A ⊆ A'. Consequently T is injective, monotone, and reflects inclusions (hence strict inclusions), which is what lets an induced copy be pushed back from the compressed colouring to χ.
-/

/-- The compression map is an order embedding of the subsets of the complement of W; it yields injectivity, monotonicity and reflection of inclusions at once. -/
theorem mdfrbf_compress_subset_iff {d k : ℕ} (W : Finset (Fin d)) (χ : Finset (Fin d) → Fin k) (c : Fin k)
    (A A' : Finset ↥(Finset.univ \ W)) :
    mdfrbf_compress W χ c A ⊆ mdfrbf_compress W χ c A' ↔ A ⊆ A' := by
  classical
  set emb : ↥(Finset.univ \ W) ↪ Fin d := Function.Embedding.subtype fun x => x ∈ Finset.univ \ W with hemb
  have hdef : ∀ A : Finset ↥(Finset.univ \ W), mdfrbf_compress W χ c A
      = A.map emb ∪ (if (A.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A ∧ χ (B.map emb) = c) then W else ∅) := by
    intro A
    unfold mdfrbf_compress
    simp only [← hemb]
    by_cases h : (A.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A ∧ χ (B.map emb) = c)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; simp
  have hnotW : ∀ x : ↥(Finset.univ \ W), (emb x : Fin d) ∉ W := by
    intro x hx
    have hx2 : (x : Fin d) ∈ Finset.univ \ W := x.2
    rw [Finset.mem_sdiff] at hx2
    have hv : (emb x : Fin d) = (x : Fin d) := rfl
    rw [hv] at hx
    exact hx2.2 hx
  have hdisj : ∀ A : Finset ↥(Finset.univ \ W), Disjoint (A.map emb) W := by
    intro A
    rw [Finset.disjoint_left]
    intro y hy hyW
    rw [Finset.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact hnotW x hyW
  have hWa : ∀ A : Finset ↥(Finset.univ \ W),
      (if (A.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A ∧ χ (B.map emb) = c) then W else ∅) ⊆ W := by
    intro A
    split_ifs <;> simp
  have hdiff : ∀ A : Finset ↥(Finset.univ \ W), mdfrbf_compress W χ c A \ W = A.map emb := by
    intro A
    rw [hdef A]
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hy | hy, hyW⟩
      · exact hy
      · exact absurd (hWa A hy) hyW
    · intro hy
      exact ⟨Or.inl hy, fun h => Finset.disjoint_left.mp (hdisj A) hy h⟩
  constructor
  · intro hsub x hx
    have h1 : emb x ∈ A.map emb := by rw [Finset.mem_map]; exact ⟨x, hx, rfl⟩
    have h2 : emb x ∈ mdfrbf_compress W χ c A' := by
      apply hsub
      rw [hdef A]
      exact Finset.mem_union_left _ h1
    have h4 : emb x ∈ A'.map emb := by
      rw [← hdiff A', Finset.mem_sdiff]
      exact ⟨h2, hnotW x⟩
    rw [Finset.mem_map] at h4
    obtain ⟨y, hy, hyx⟩ := h4
    rw [emb.injective hyx] at hy
    exact hy
  · intro hsub
    rw [hdef A, hdef A']
    have hmap : A.map emb ⊆ A'.map emb := Finset.map_subset_map.mpr hsub
    have hHA : (A.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A ∧ χ (B.map emb) = c) →
        (A'.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A' ∧ χ (B.map emb) = c) := by
      rintro ⟨hne, B, hBne, hBsub, hBc⟩
      exact ⟨hne.mono hsub, B, hBne, hBsub.trans hsub, hBc⟩
    by_cases hA : (A.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A ∧ χ (B.map emb) = c)
    · rw [if_pos hA, if_pos (hHA hA)]
      exact Finset.union_subset_union hmap (le_refl W)
    · by_cases hA' : (A'.Nonempty ∧ ∃ B : Finset ↥(Finset.univ \ W), B.Nonempty ∧ B ⊆ A' ∧ χ (B.map emb) = c)
      · rw [if_neg hA, if_pos hA']
        intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · exact Finset.mem_union_left _ (hmap h)
        · exact absurd h (by simp)
      · rw [if_neg hA, if_neg hA']
        intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · exact Finset.mem_union_left _ (hmap h)
        · exact absurd h (by simp)
