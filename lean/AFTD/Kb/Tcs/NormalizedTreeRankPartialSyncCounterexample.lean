import AFTD.Prelude
import AFTD.Kb.Tcs.NormalizedTreeRankPartialMixture

/-!
# normalized_tree_rank_partial_sync_counterexample

Topic: combinatorics   Node: c5b709f18b24

Provenance: helper lemma. A synthetic obstruction to an abstract closure argument for OP-1399.

Full partial synchronization can fail after one-vertex extension even when the input has the stated analytic invariants and its first three ranks match a rooted 19-vertex tree.
-/

private noncomputable def normalized_psw_u (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 1 else if k ≤ 6 then (56 / 57) * (47 / 54) ^ (k - 2) else 0
private noncomputable def normalized_psw_a (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 18 / 19 else if k ≤ 6 then (47 / 57) * (47 / 54) ^ (k - 2) else 0

private theorem normalized_psw_a_zero (k : ℕ) (h : 6 < k) : normalized_psw_a k = 0 := by
  simp [normalized_psw_a, show k ≠ 0 by omega, show k ≠ 1 by omega, show ¬ k ≤ 6 by omega]
private theorem normalized_psw_u_zero (k : ℕ) (h : 6 < k) : normalized_psw_u k = 0 := by
  simp [normalized_psw_u, show k ≠ 0 by omega, show k ≠ 1 by omega, show ¬ k ≤ 6 by omega]

private theorem normalized_psw_input_valid : normalized_tree_rank_partial_mixture normalized_psw_u normalized_psw_a := by
  refine ⟨by norm_num [normalized_psw_a], by norm_num [normalized_psw_u], by norm_num [normalized_psw_a], by norm_num [normalized_psw_u], by norm_num [normalized_psw_u], by norm_num [normalized_psw_a], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k ≤ 6
    · interval_cases k <;> norm_num [normalized_psw_a, normalized_psw_u]
    · have h : 6 < k := by omega
      simp [normalized_psw_a_zero k h, normalized_psw_u_zero k h]
  · intro k hk
    simp [normalized_psw_a_zero k hk, normalized_psw_u_zero k hk]
  · intro i j hij
    by_cases hj : j ≤ 6
    · have hi : i ≤ 6 := by omega
      interval_cases i <;> interval_cases j <;> norm_num [normalized_psw_a, normalized_psw_u] at *
    · have hj' : 6 < j := by omega
      simp [normalized_psw_a_zero j hj', normalized_psw_u_zero j hj']
  · intro k
    by_cases hk : k ≤ 4
    · interval_cases k <;> norm_num [normalized_psw_a, normalized_psw_u]
    · have h : 6 < k + 2 := by omega
      simp only [normalized_psw_a_zero (k+2) h, normalized_psw_u_zero (k+2) h, sub_self, mul_zero]
      exact sq_nonneg _
  · intro t ht0 ht1 k
    by_cases hk : k ≤ 4
    · interval_cases k <;> norm_num [normalized_psw_a, normalized_psw_u] <;>
        nlinarith [sq_nonneg t, sq_nonneg (1-t), mul_nonneg ht0 (show 0 ≤ 1-t by linarith)]
    · have h : 6 < k + 2 := by omega
      simp only [normalized_psw_a_zero (k+2) h, normalized_psw_u_zero (k+2) h, sub_self, mul_zero, add_zero]
      exact sq_nonneg _
  · intro i j hj hji
    by_cases hi : i ≤ 6
    · have hj' : j ≤ 6 := by omega
      interval_cases i <;> interval_cases j <;> norm_num [normalized_psw_a, normalized_psw_u] at *
    · have h0 : 6 < i := by omega
      have h1 : 6 < i+1 := by omega
      simp [normalized_psw_a_zero i h0, normalized_psw_u_zero i h0, normalized_psw_a_zero (i+1) h1, normalized_psw_u_zero (i+1) h1]

theorem normalized_tree_rank_partial_sync_counterexample : ∃ u a : ℕ → ℝ, normalized_tree_rank_partial_mixture u a ∧ (let g : ℕ → ℝ := fun k => (20 - (k : ℝ)) * u k + (k : ℝ) * a (k - 1); let q : ℕ → ℝ := fun k => (20 - (k : ℝ)) * u k + (k : ℝ) * u (k - 1); g 5 * q 4 + g 4 * q 5 < g 6 * q 3 + g 3 * q 6) := by
  refine ⟨normalized_psw_u, normalized_psw_a, normalized_psw_input_valid, ?_⟩
  norm_num [normalized_psw_u, normalized_psw_a]
