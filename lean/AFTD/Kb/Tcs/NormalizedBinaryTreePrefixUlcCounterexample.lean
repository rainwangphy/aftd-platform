import AFTD.Prelude
import AFTD.Kb.Tcs.NormalizedBinaryTreePrefixInput

/-!
# normalized_binary_tree_prefix_ulc_counterexample

Topic: combinatorics   Node: 500631c59062

Provenance: helper lemma. A synthetic obstruction to a binary-extension argument for OP-1399.

Even with bounded-mixture ULC, likelihood order, and full partial synchronization, normalized sequences having initial counts U=(1,100,4760) and A=(1,80,3160) can have a non-ULC one-vertex extension.
-/

private noncomputable def binary_tree_prefix_u (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 476 / 495
  else if k = 3 then 10338 / 13475 else if k = 4 then 77401 / 1307075
  else if k = 5 then 42527 / 15057504 else if k = 6 then 160541 / 1192052400 else 0
private noncomputable def binary_tree_prefix_a (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 4 / 5 else if k = 2 then 316 / 495
  else if k = 3 then 6863 / 13475 else if k = 4 then 19627 / 1307075
  else if k = 5 then 2777 / 6273960 else 0

private theorem binary_tree_prefix_a_zero (k : ℕ) (h : 6 < k) : binary_tree_prefix_a k = 0 := by
  simp [binary_tree_prefix_a, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega, show k ≠ 4 by omega, show k ≠ 5 by omega]
private theorem binary_tree_prefix_u_zero (k : ℕ) (h : 6 < k) : binary_tree_prefix_u k = 0 := by
  simp [binary_tree_prefix_u, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega, show k ≠ 4 by omega, show k ≠ 5 by omega, show k ≠ 6 by omega]

private theorem binary_tree_prefix_input_valid : normalized_binary_tree_prefix_input binary_tree_prefix_u binary_tree_prefix_a := by
  refine ⟨by norm_num [binary_tree_prefix_a], by norm_num [binary_tree_prefix_u], by norm_num [binary_tree_prefix_a], by norm_num [binary_tree_prefix_u], by norm_num [binary_tree_prefix_u], by norm_num [binary_tree_prefix_a], ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k ≤ 6
    · interval_cases k <;> norm_num [binary_tree_prefix_a, binary_tree_prefix_u]
    · have h : 6 < k := by omega
      simp [binary_tree_prefix_a_zero k h, binary_tree_prefix_u_zero k h]
  · intro k hk
    simp [binary_tree_prefix_a_zero k hk, binary_tree_prefix_u_zero k hk]
  · intro i j hij
    by_cases hj : j ≤ 6
    · have hi : i ≤ 6 := by omega
      interval_cases i <;> interval_cases j <;> norm_num [binary_tree_prefix_a, binary_tree_prefix_u] at *
    · have hj' : 6 < j := by omega
      simp [binary_tree_prefix_a_zero j hj', binary_tree_prefix_u_zero j hj']
  · intro t ht0 ht1 k
    by_cases hk : k ≤ 4
    · interval_cases k <;> norm_num [binary_tree_prefix_a, binary_tree_prefix_u] <;>
        nlinarith [sq_nonneg t, sq_nonneg (1-t), mul_nonneg ht0 (show 0 ≤ 1-t by linarith)]
    · have h : 6 < k + 2 := by omega
      simp only [binary_tree_prefix_a_zero (k+2) h, binary_tree_prefix_u_zero (k+2) h, sub_self, mul_zero, add_zero]
      exact sq_nonneg _
  · intro i j hj hji
    by_cases hi : i ≤ 6
    · have hj' : j ≤ 6 := by omega
      interval_cases i <;> interval_cases j <;> norm_num [binary_tree_prefix_a, binary_tree_prefix_u] at *
    · have h0 : 6 < i := by omega
      have h1 : 6 < i+1 := by omega
      simp [binary_tree_prefix_a_zero i h0, binary_tree_prefix_u_zero i h0, binary_tree_prefix_a_zero (i+1) h1, binary_tree_prefix_u_zero (i+1) h1]

theorem normalized_binary_tree_prefix_ulc_counterexample : ∃ u a : ℕ → ℝ, normalized_binary_tree_prefix_input u a ∧ (let g : ℕ → ℝ := fun k => (101 - (k : ℝ)) * u k + (k : ℝ) * a (k - 1); g 5 ^ 2 < g 4 * g 6) := by
  refine ⟨binary_tree_prefix_u, binary_tree_prefix_a, binary_tree_prefix_input_valid, ?_⟩
  norm_num [binary_tree_prefix_u, binary_tree_prefix_a]
