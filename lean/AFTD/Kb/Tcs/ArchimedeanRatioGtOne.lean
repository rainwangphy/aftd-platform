import AFTD.Prelude

/-!
# archimedean_ratio_gt_one

Topic: online_algorithms   Node: 6ebf042bdbb4

Provenance: helper lemma. step towards op182_deferred_to_deadline_beyond_half_against_stopping

For any real constant `c > 1/2`, there exists a natural number `M > 1` such that `1 < c * (2 - 1 / M)`.
-/

/-- For any constant c > 1/2, there exists an integer M > 1 such that c * (2 - 1/M) > 1. -/
theorem archimedean_ratio_gt_one (c : ℝ) (hc : 1 / 2 < c) :
    ∃ M : ℕ, 1 < M ∧ 1 < c * (2 - (1 : ℝ) / M) := by
  have hcpos : 0 < c := by linarith
  have hdiff : 0 < 2 - 1 / c := by
    have : 1 / c < 2 := by
      rw [div_lt_iff₀ hcpos]
      linarith
    linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (1 / (2 - 1 / c)))
  have h1 : 1 < M := by
    have : (1 : ℝ) < M := lt_of_le_of_lt (le_max_left _ _) hM
    exact_mod_cast this
  have h2 : 1 / (2 - 1 / c) < (M : ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
  have hMpos : 0 < (M : ℝ) := by positivity
  have hinv : 1 / (M : ℝ) < 2 - 1 / c := by
    rwa [one_div_lt hMpos hdiff]
  refine ⟨M, h1, ?_⟩
  have : 1 / c < 2 - 1 / (M : ℝ) := by linarith
  have : 1 < (2 - 1 / (M : ℝ)) * c := by
    rwa [div_lt_iff₀ hcpos] at this
  linarith
