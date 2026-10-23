import AFTD.Prelude

/-!
# exists_le_div_of_sum_le

Topic: combinatorics   Node: 5853346c3179

Provenance: helper lemma. arXiv:2610.31489, Lemma 4.1

If T ≥ 1 and a sequence of real numbers D_1, ..., D_T has sum at most C, then there exists an index r ∈ {1, ..., T} such that D_r ≤ C / T.
-/

/-- An average bound implies existence of an element bounded by the average. -/
theorem exists_le_div_of_sum_le {T : ℕ} (hT : 0 < T) (D : ℕ → ℝ) (C : ℝ) (hD : ∑ t ∈ Finset.Icc 1 T, D t ≤ C) : ∃ r ∈ Finset.Icc 1 T, D r ≤ C / T := by
  by_contra h
  push Not at h
  have hnonempty : (Finset.Icc 1 T).Nonempty := ⟨1, by simp only [Finset.mem_Icc]; omega⟩
  have hlt : ∑ t ∈ Finset.Icc 1 T, (C / T) < ∑ t ∈ Finset.Icc 1 T, D t := by
    apply Finset.sum_lt_sum_of_nonempty hnonempty
    intro i hi
    exact h i hi
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hlt
  have hcard : T + 1 - 1 = T := by omega
  rw [hcard] at hlt
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hmul : (T : ℝ) * (C / T) = C := by field_simp
  linarith
