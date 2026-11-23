import AFTD.Prelude
import AFTD.Kb.Tcs.HChainLen

/-!
# h_chain_pos_lt

Topic: algorithms   Node: 438f37f79c72

Provenance: helper lemma. arXiv:2611.27671 "Shellsort with O(n log n) Average-Case Complexity", Lemma 2.2

For any index $i$ in an array of length $n$ and any positive step $h$, the quotient $i / h$ is strictly less than the length of the $h$-chain of residue $i \pmod h$.
-/

/-- The chain position i / h is strictly less than the chain length. -/
theorem h_chain_pos_lt (n h : ℕ) (hpos : 0 < h) (i : Fin n) : i.val / h < h_chain_len n h (i.val % h) := by
  set r := i.val % h
  have hr_le : r ≤ i.val := Nat.mod_le _ _
  have hr_lt_n : r < n := lt_of_le_of_lt hr_le i.isLt
  have hif : ¬ (h = 0 ∨ n ≤ r) := by
    rintro (h0 | hn)
    · exact (Nat.ne_of_gt hpos) h0
    · exact absurd hn (Nat.not_le_of_gt hr_lt_n)
  rw [h_chain_len, if_neg hif]
  have hkey : i.val / h * h ≤ n - 1 - r := by
    have h1 : h * (i.val / h) + r = i.val := by
      simpa [r, Nat.mul_comm] using Nat.div_add_mod i.val h
    have h2 : h * (i.val / h) + r ≤ n - 1 := by
      rw [h1]; exact Nat.le_sub_one_of_lt i.isLt
    have h3 : h * (i.val / h) ≤ n - 1 - r := Nat.le_sub_of_add_le h2
    rwa [Nat.mul_comm] at h3
  have := (Nat.le_div_iff_mul_le hpos).mpr hkey
  omega
