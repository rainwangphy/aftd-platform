import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedBlowupMatrix

/-!
# balanced_blowup_matrix_off_diag

Topic: graphs   Node: d1696b9f7933

Provenance: helper lemma. scout/2610-14100-digraph-laplacian-spectra-the-2005-polygon-conjecture-fails.md:1049

For natural numbers m and d with 1 ≤ m and 1 ≤ d, and an m x m real matrix L on Fin m with off-diagonal entries in [-1/m, 0], all off-diagonal entries of balanced_blowup_matrix m d L lie in [-1/(m*d), 0].
-/

/-- The off-diagonal entries of the balanced blow-up matrix lie in [-1/(m*d), 0]. -/
theorem balanced_blowup_matrix_off_diag (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d)
    (L : Matrix (Fin m) (Fin m) ℝ)
    (hL : ∀ i j : Fin m, i ≠ j → -(1 : ℝ) / m ≤ L i j ∧ L i j ≤ 0)
    (i j : Fin m) (s t : Fin d) (hne : (i, s) ≠ (j, t)) :
    -(1 : ℝ) / (m * d) ≤ balanced_blowup_matrix m d L (i, s) (j, t) ∧
      balanced_blowup_matrix m d L (i, s) (j, t) ≤ 0 := by
  have h_entry :
      balanced_blowup_matrix m d L (i, s) (j, t) =
        (if i = j then L i i else 0) * (if s = t then 1 else 0) -
          (1 / (d : ℝ)) * (if i = j then 0 else - L i j) := by
    unfold balanced_blowup_matrix
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  rw [h_entry]
  have hd_pos : 0 < (d : ℝ) := by positivity
  by_cases hij : i = j
  · subst hij
    have hst : s ≠ t := by
      intro h
      apply hne
      rw [h]
    simp [hst]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · simp only [hij, ↓reduceIte, MulZeroClass.zero_mul, zero_sub, mul_neg, neg_neg]
    have hL_ij := hL i j hij
    constructor
    · rw [← div_div]
      have : 1 / (d : ℝ) * L i j = L i j / d := by ring
      rw [this]
      exact div_le_div_of_nonneg_right hL_ij.1 (le_of_lt hd_pos)
    · have : 1 / (d : ℝ) * L i j = L i j / d := by ring
      rw [this]
      exact div_nonpos_of_nonpos_of_nonneg hL_ij.2 (le_of_lt hd_pos)
