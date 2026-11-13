import AFTD.Prelude

/-!
# polynomial_log_concave_reflect

Topic: graphs   Node: bf948a3ff33e

Provenance: helper lemma. Algebraic helper for the leaf-rich graph case of OP-1399.

Reflecting a natural polynomial through degree N at least its degree preserves log-concavity and interval support.
-/

theorem polynomial_log_concave_reflect (p : Polynomial ℕ) (N : ℕ) (hdeg : p.natDegree ≤ N) (hlc : ∀ k : ℕ, p.coeff k * p.coeff (k + 2) ≤ p.coeff (k + 1) * p.coeff (k + 1)) (hint : ∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < p.coeff i → 0 < p.coeff k → 0 < p.coeff j) : (∀ k : ℕ, (p.reflect N).coeff k * (p.reflect N).coeff (k + 2) ≤ (p.reflect N).coeff (k + 1) * (p.reflect N).coeff (k + 1)) ∧ (∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < (p.reflect N).coeff i → 0 < (p.reflect N).coeff k → 0 < (p.reflect N).coeff j) := by
  have hzero : ∀ {m : ℕ}, N < m → (p.reflect N).coeff m = 0 := by
    intro m hm
    rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hm]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hm)
  constructor
  · intro k
    by_cases hk : k + 2 ≤ N
    · have hk0 : k ≤ N := by omega
      have hk1 : k + 1 ≤ N := by omega
      rw [Polynomial.coeff_reflect, Polynomial.coeff_reflect, Polynomial.coeff_reflect]
      rw [Polynomial.revAt_le hk0, Polynomial.revAt_le hk1, Polynomial.revAt_le hk]
      have h1 : N - (k + 1) = (N - (k + 2)) + 1 := by omega
      have h2 : N - k = (N - (k + 2)) + 2 := by omega
      rw [h1, h2, mul_comm (p.coeff _)]
      exact hlc (N - (k + 2))
    · have hlt : N < k + 2 := Nat.not_le.mp hk
      rw [hzero hlt, mul_zero]
      exact Nat.zero_le _
  · intro i j k hij hjk hi hk
    have hk_le : k ≤ N := by
      by_contra h
      have hlt : N < k := Nat.not_le.mp h
      have hz : (p.reflect N).coeff k = 0 := hzero hlt
      omega
    have hj_le : j ≤ N := by omega
    have hi_le : i ≤ N := by omega
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le hj_le]
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le hi_le] at hi
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le hk_le] at hk
    have h1 : N - k ≤ N - j := by omega
    have h2 : N - j ≤ N - i := by omega
    exact hint (N - k) (N - j) (N - i) h1 h2 hk hi
