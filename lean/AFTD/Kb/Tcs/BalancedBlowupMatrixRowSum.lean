import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedBlowupMatrix

/-!
# balanced_blowup_matrix_row_sum

Topic: graphs   Node: ea56e6061bd9

Provenance: helper lemma. scout/2610-14100-digraph-laplacian-spectra-the-2005-polygon-conjecture-fails.md:1049

For natural numbers m and d with 1 ≤ d, and an m x m real matrix L on Fin m with zero row sums, each row of the balanced blow-up matrix balanced_blowup_matrix m d L sums to zero.
-/

/-- Each row of the balanced blow-up matrix sums to zero if L has zero row sums. -/
theorem balanced_blowup_matrix_row_sum (m d : ℕ) (hd : 1 ≤ d) (L : Matrix (Fin m) (Fin m) ℝ)
    (hL : ∀ i : Fin m, ∑ j : Fin m, L i j = 0) (i : Fin m) (s : Fin d) :
    ∑ j : Fin m, ∑ t : Fin d, balanced_blowup_matrix m d L (i, s) (j, t) = 0 := by
  have hd_pos : (d : ℝ) ≠ 0 := by
    norm_cast
    omega
  have h_entry (j : Fin m) (t : Fin d) :
      balanced_blowup_matrix m d L (i, s) (j, t) =
        (if i = j then L i i else 0) * (if s = t then 1 else 0) -
          (1 / (d : ℝ)) * (if i = j then 0 else - L i j) := by
    unfold balanced_blowup_matrix
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  simp_rw [h_entry, Finset.sum_sub_distrib]
  have h1 : (∑ j : Fin m, ∑ t : Fin d, (if i = j then L i i else 0) * (if s = t then 1 else 0 : ℝ)) = L i i := by
    simp
  have h2 : (∑ j : Fin m, ∑ _t : Fin d, (1 / (d : ℝ)) * (if i = j then 0 else - L i j)) = L i i := by
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hd_mul (x : ℝ) : d • (1 / (d : ℝ) * x) = x := by
      rw [nsmul_eq_mul, ← mul_assoc, mul_one_div_cancel hd_pos, one_mul]
    simp_rw [hd_mul]
    have h (j : Fin m) : (if i = j then (0 : ℝ) else - L i j) = (if i = j then L i i else 0) - L i j := by
      split_ifs with hij
      · subst hij; ring
      · ring
    simp_rw [h, Finset.sum_sub_distrib]
    simp [hL i]
  rw [h1, h2, sub_self]
