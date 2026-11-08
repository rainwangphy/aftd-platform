import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTreeNumLeaves
import AFTD.Kb.Tcs.ComparisonTreeDepth
import AFTD.Kb.Tcs.ComparisonTree

/-!
# comparison_tree_num_leaves_le_two_pow_depth

Topic: algorithms   Node: 1cf69eac3ce8

Provenance: helper lemma. arXiv:2610.18740 Remark 9, Selecting the 7th Smallest of 16 Elements Takes Exactly 28 Comparisons

For any natural number n and any comparison decision tree T on n elements, the number of leaves of T is at most 2 raised to the depth of T.
-/

/-- Every comparison decision tree has at most 2^depth leaves. -/
theorem comparison_tree_num_leaves_le_two_pow_depth {n : ℕ} (T : ComparisonTree n) :
    comparison_tree_num_leaves T ≤ 2 ^ (comparison_tree_depth T) := by
  induction T with
  | leaf a =>
    rw [comparison_tree_num_leaves.eq_1, comparison_tree_depth.eq_1]
    omega
  | branch i j l r ih_l ih_r =>
    rw [comparison_tree_num_leaves.eq_2, comparison_tree_depth.eq_2]
    have h1 : 2 ^ comparison_tree_depth l ≤ 2 ^ max (comparison_tree_depth l) (comparison_tree_depth r) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h2 : 2 ^ comparison_tree_depth r ≤ 2 ^ max (comparison_tree_depth l) (comparison_tree_depth r) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hpow : 2 ^ (1 + max (comparison_tree_depth l) (comparison_tree_depth r)) =
        2 * 2 ^ max (comparison_tree_depth l) (comparison_tree_depth r) := by
      rw [pow_add, pow_one, mul_comm]
    omega
