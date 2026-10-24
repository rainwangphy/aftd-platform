import AFTD.Prelude

/-!
# rat_abs_half_sum_add_abs_half_diff_le

Topic: graphs   Node: cbf2b2b6af75

Provenance: helper lemma. Helper for digraph_both_cuts_ge_ceil_div_six_of_indegree_lt, arXiv:2610.21381, proof of Theorem 1.4, Case 2. The two-partition certificate and paired-outcome inequality are a deterministic formulation of the paper's averaging argument; no research advance is claimed.

If the absolute values of rational numbers p and q are at most M, the sum of the absolute values of (p+q)/2 and (p-q)/2 is at most M.
-/

theorem rat_abs_half_sum_add_abs_half_diff_le (p q M : ℚ)
    (hp : |p| ≤ M) (hq : |q| ≤ M) : |(p+q)/2| + |(p-q)/2| ≤ M := by
  have hp' := abs_le.mp hp
  have hq' := abs_le.mp hq
  have hh : |p+q| + |p-q| ≤ 2*M := by
    rcases le_total 0 (p+q) with ha | ha
    · rcases le_total 0 (p-q) with hb | hb
      · rw [abs_of_nonneg ha, abs_of_nonneg hb]
        linarith
      · rw [abs_of_nonneg ha, abs_of_nonpos hb]
        linarith
    · rcases le_total 0 (p-q) with hb | hb
      · rw [abs_of_nonpos ha, abs_of_nonneg hb]
        linarith
      · rw [abs_of_nonpos ha, abs_of_nonpos hb]
        linarith
  rw [abs_div, abs_div]
  norm_num
  linarith
