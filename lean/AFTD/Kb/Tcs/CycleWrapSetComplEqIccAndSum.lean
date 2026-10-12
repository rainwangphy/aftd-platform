import AFTD.Prelude

/-!
# cycle_wrap_set_compl_eq_Icc_and_sum

Topic: combinatorics   Node: 7d080b09c833

Provenance: formalization of a published result. Source: arXiv:2610.08889 (Consecutive Cycle Sums), Lemma 1. Wrap sets and standard intervals are written out as Finset.Icc unions; the empty interval for j = i+1 is Icc (i+1) i.

For 1 ≤ i < j ≤ n, the complement in {1,…,n} of the wrap set W = {j,…,n} ∪ {1,…,i} of the n-cycle is the standard interval {i+1,…,j−1} (empty when j = i+1), and its element sum is T_n − W*, where T_n = n(n+1)/2 and W* is the element sum of W.
-/

theorem cycle_wrap_set_compl_eq_Icc_and_sum (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n) :
    Finset.Icc 1 n \ (Finset.Icc j n ∪ Finset.Icc 1 i) = Finset.Icc (i + 1) (j - 1) ∧
    ∑ x ∈ Finset.Icc 1 n \ (Finset.Icc j n ∪ Finset.Icc 1 i), x =
      n * (n + 1) / 2 - ∑ x ∈ Finset.Icc j n ∪ Finset.Icc 1 i, x := by
  have hsub : Finset.Icc j n ∪ Finset.Icc 1 i ⊆ Finset.Icc 1 n := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_Icc] at hx ⊢
    omega
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_Icc]
    omega
  · have hg : ∀ m : ℕ, (∑ x ∈ Finset.Icc 1 m, x) * 2 = m * (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]; ring
    have htot : ∑ x ∈ Finset.Icc 1 n, x = n * (n + 1) / 2 :=
      (Nat.div_eq_of_eq_mul_left (by norm_num) (hg n).symm).symm
    rw [← htot, ← Finset.sum_sdiff hsub]
    omega
