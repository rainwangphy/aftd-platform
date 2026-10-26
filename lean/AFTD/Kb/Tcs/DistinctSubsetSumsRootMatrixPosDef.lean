import AFTD.Prelude
import AFTD.Kb.Tcs.DistinctSubsetSumsRootMatrix

/-!
# distinct_subset_sums_root_matrix_pos_def

Topic: combinatorics   Node: 8463d58a1a12

Provenance: helper lemma. arXiv:2610.26970 Proposition 3.2

For any natural number k ≥ 1, the root lattice matrix distinct_subset_sums_root_matrix k is positive definite.
-/

/-- The root lattice matrix H is positive definite for every k ≥ 1. -/
theorem distinct_subset_sums_root_matrix_pos_def (k : ℕ) (hk : 1 ≤ k) :
  Matrix.PosDef (distinct_subset_sums_root_matrix k) := by
  open Matrix Finset in
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp only [conjTranspose_apply, star_trivial, distinct_subset_sums_root_matrix]
    by_cases h : i = j
    · subst h; rfl
    · have h' : j ≠ i := Ne.symm h
      simp [h, h']
  · intro x hx
    have h_dot : star x ⬝ᵥ (distinct_subset_sums_root_matrix k *ᵥ x) =
        ∑ i, (x i) ^ 2 - (1 / ((k : ℝ) + 1)) * (∑ i, x i) ^ 2 := by
      simp only [dotProduct, mulVec, star_trivial, distinct_subset_sums_root_matrix]
      have h (i : Fin k) : (∑ j, ((if i = j then (1 : ℝ) else 0) - 1 / ((k : ℝ) + 1)) * x j) =
          x i - (1 / ((k : ℝ) + 1)) * ∑ j, x j := by
        simp [sub_mul, sum_sub_distrib, ← mul_sum]
      simp_rw [h]
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, sq]
      ring
    rw [h_dot]
    have hne : ∃ i, x i ≠ 0 := by
      contrapose! hx
      ext i
      exact hx i
    obtain ⟨i, hi⟩ := hne
    have hS : 0 < ∑ j, (x j) ^ 2 := by
      have hi_pos : 0 < (x i) ^ 2 := sq_pos_of_ne_zero hi
      have hle : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 := single_le_sum (fun j _ => sq_nonneg (x j)) (mem_univ i)
      linarith
    have hCS : (∑ i, x i) ^ 2 ≤ (k : ℝ) * ∑ i, (x i) ^ 2 := by
      have := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin k)) x (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    set S := ∑ i, (x i) ^ 2
    set C := (∑ i, x i) ^ 2
    have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk1 : 0 < (k : ℝ) + 1 := by linarith
    have h1 : C / ((k : ℝ) + 1) ≤ ((k : ℝ) * S) / ((k : ℝ) + 1) :=
      div_le_div_of_nonneg_right hCS (le_of_lt hk1)
    have h2 : (1 / ((k : ℝ) + 1)) * C = C / ((k : ℝ) + 1) := by ring
    rw [h2]
    have h3 : ((k : ℝ) * S) / ((k : ℝ) + 1) < S := by
      rw [div_lt_iff₀ hk1]
      nlinarith
    linarith
