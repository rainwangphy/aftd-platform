import AFTD.Prelude

/-!
# op861_cubic_norm_sum_bound

Topic: graphs   Node: 1de5c45bad91

Provenance: helper lemma. A norm estimate used for op861_ternary_crossing_pairs_dense.

For a finite family of complex numbers whose norms satisfy three times each norm at most n, three times the norm of the sum of their cubes is at most n times the sum of their squared norms.
-/

open scoped BigOperators
set_option maxHeartbeats 1000000

theorem op861_cubic_norm_sum_bound (ι : Type*) [DecidableEq ι]
    (s : Finset ι) (F : ι → ℂ) (n : ℝ)
    (h : ∀ i ∈ s, 3 * ‖F i‖ ≤ n) :
    3 * ‖∑ i ∈ s, F i ^ 3‖ ≤ n * ∑ i ∈ s, ‖F i‖^2 := by
  calc
    _ ≤ 3 * ∑ i ∈ s, ‖F i ^ 3‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le s (fun i => F i ^ 3)) (by norm_num)
    _ = ∑ i ∈ s, (3 * ‖F i‖^3) := by simp [Finset.mul_sum, norm_pow]
    _ ≤ ∑ i ∈ s, (n * ‖F i‖^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := mul_le_mul_of_nonneg_right (h i hi) (sq_nonneg ‖F i‖)
      nlinarith [hi']
    _ = _ := by rw [Finset.mul_sum]
