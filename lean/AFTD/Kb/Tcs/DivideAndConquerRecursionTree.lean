import AFTD.Prelude

/-!
# divide_and_conquer_recursion_tree

Topic: algorithms   Node: 5f52837127f7

For any branching factor a and cost function g, the divide-and-conquer recurrence T(k+1) = a*T(k) + g(k+1) has exact solution T(k) = a^k * T(0) + sum_{j=1}^k a^(k-j) * g(j).
-/

/-- The general recursion tree summation formula for divide-and-conquer recurrences T(k+1) = a*T(k) + g(k+1). -/
theorem divide_and_conquer_recursion_tree
    (T : ℕ → ℝ) (g : ℕ → ℝ) (a : ℝ)
    (hrec : ∀ k : ℕ, T (k + 1) = a * T k + g (k + 1)) :
    ∀ k : ℕ, T k = a ^ k * T 0 + Finset.sum (Finset.Icc 1 k) (fun j => a ^ (k - j) * g j) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hrec k, ih]
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hsum : a * (∑ j ∈ Finset.Icc 1 k, a ^ (k - j) * g j) =
        ∑ j ∈ Finset.Icc 1 k, a ^ (k + 1 - j) * g j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ k := (Finset.mem_Icc.mp hj).2
      have : a * (a ^ (k - j) * g j) = (a * a ^ (k - j)) * g j := by ring
      rw [this, ← pow_succ']
      congr 2
      omega
    simp only [Nat.sub_self, pow_zero, one_mul]
    have : a * (a ^ k * T 0) = a ^ (k + 1) * T 0 := by
      rw [← mul_assoc, ← pow_succ']
    linarith
