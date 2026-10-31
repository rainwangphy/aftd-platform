import AFTD.Prelude

/-!
# greedy_vector_chain_saturation

Topic: submodular   Node: 9429ddea6e13

Provenance: helper lemma. arXiv:2610.35433 Corollary 1

For any set function C on Finset (Fin n) with C(∅) = 0, any permutation π, and any k ≤ n, the sum of the greedy marginal differences z_i = C(S_{rank(i)}) - C(S_{rank(i)+1}) over the upper set S_k equals C(S_k).
-/

/-- The greedy marginal difference vector along a chain saturates the chain's sets for any normalized set function. -/
theorem greedy_vector_chain_saturation {n : ℕ} (C : Finset (Fin n) → ℝ)
    (hC_empty : C ∅ = 0) (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    ∑ i ∈ (Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ))).map π.toEmbedding,
      (C ((Finset.univ.filter (fun j : Fin n => (π.symm i : ℕ) ≤ (j : ℕ))).map π.toEmbedding) -
       C ((Finset.univ.filter (fun j : Fin n => (π.symm i : ℕ) + 1 ≤ (j : ℕ))).map π.toEmbedding)) =
      C ((Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ))).map π.toEmbedding) := by
  let F : ℕ → ℝ := fun m => C ((Finset.univ.filter (fun j : Fin n => m ≤ (j : ℕ))).map π.toEmbedding)
  have h1 : ∑ i ∈ (Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ))).map π.toEmbedding,
      (C ((Finset.univ.filter (fun j : Fin n => (π.symm i : ℕ) ≤ (j : ℕ))).map π.toEmbedding) -
       C ((Finset.univ.filter (fun j : Fin n => (π.symm i : ℕ) + 1 ≤ (j : ℕ))).map π.toEmbedding)) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ)), (F j - F (j + 1)) := by
    rw [Finset.sum_map]
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    rfl
  rw [h1]
  have hmap : Finset.Ico k n = (Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ))).map Fin.valEmbedding := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨hkx, hx⟩
      exact ⟨⟨x, hx⟩, hkx, rfl⟩
    · rintro ⟨a, hka, rfl⟩
      exact ⟨hka, a.isLt⟩
  have h2 : ∑ j ∈ Finset.univ.filter (fun j : Fin n => k ≤ (j : ℕ)), (F j - F (j + 1)) =
      ∑ x ∈ Finset.Ico k n, (F x - F (x + 1)) := by
    rw [hmap, Finset.sum_map]
    rfl
  rw [h2]
  have htelescope : ∑ x ∈ Finset.Ico k n, (F x - F (x + 1)) = F k - F n := by
    rw [Finset.sum_Ico_eq_sub _ hk, Finset.sum_range_sub', Finset.sum_range_sub']
    abel
  rw [htelescope]
  have hFn : F n = 0 := by
    have hempty : Finset.univ.filter (fun j : Fin n => n ≤ (j : ℕ)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _
      exact not_le_of_gt x.isLt
    change C ((Finset.univ.filter (fun j : Fin n => n ≤ (j : ℕ))).map π.toEmbedding) = 0
    rw [hempty, Finset.map_empty, hC_empty]
  rw [hFn, sub_zero]
