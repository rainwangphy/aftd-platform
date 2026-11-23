import AFTD.Prelude
import AFTD.Kb.Tcs.HChainLen

/-!
# h_chain_index_lt

Topic: algorithms   Node: 754d954e9746

Provenance: helper lemma. arXiv:2611.27671 "Shellsort with O(n log n) Average-Case Complexity", Lemma 2.2

For any $t$ strictly less than the length of the $h$-chain starting at residue $r$ in an array of length $n$, the index $r + t \cdot h$ is strictly less than $n$.
-/

/-- Valid chain steps produce array indices strictly less than n. -/
theorem h_chain_index_lt (n h r : ℕ) (t : ℕ) (ht : t < h_chain_len n h r) : r + t * h < n := by
  unfold h_chain_len at ht
  by_cases hcond : h = 0 ∨ n ≤ r
  · rw [if_pos hcond] at ht
    exact absurd ht (Nat.not_lt_zero _)
  · rw [if_neg hcond] at ht
    have htle : t ≤ (n - 1 - r) / h := by omega
    have hmul : t * h ≤ ((n - 1 - r) / h) * h := Nat.mul_le_mul_right h htle
    have hdiv : ((n - 1 - r) / h) * h ≤ n - 1 - r := Nat.div_mul_le_self _ _
    have hle : t * h ≤ n - 1 - r := le_trans hmul hdiv
    have hnr : ¬ n ≤ r := fun h' => hcond (Or.inr h')
    have hr : r < n := Nat.lt_of_not_le hnr
    omega
