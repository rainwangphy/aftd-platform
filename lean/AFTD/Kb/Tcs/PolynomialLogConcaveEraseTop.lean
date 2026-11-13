import AFTD.Prelude

/-!
# polynomial_log_concave_erase_top

Topic: graphs   Node: dc8c61d1e6aa

Provenance: helper lemma. Algebraic helper for the leaf-rich graph case of OP-1399.

Erasing the highest-degree coefficient of a natural polynomial preserves log-concavity and interval support.
-/

lemma polynomial_log_concave_erase_top_coeff_ge (p : Polynomial ℕ) {k : ℕ} (h : p.natDegree ≤ k) :
    (p.erase p.natDegree).coeff k = 0 := by
  rw [Polynomial.coeff_erase]
  split_ifs with hk
  · rfl
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_ne h (Ne.symm hk)

theorem polynomial_log_concave_erase_top (p : Polynomial ℕ) (hlc : ∀ k : ℕ, p.coeff k * p.coeff (k + 2) ≤ p.coeff (k + 1) * p.coeff (k + 1)) (hint : ∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < p.coeff i → 0 < p.coeff k → 0 < p.coeff j) : (∀ k : ℕ, (p.erase p.natDegree).coeff k * (p.erase p.natDegree).coeff (k + 2) ≤ (p.erase p.natDegree).coeff (k + 1) * (p.erase p.natDegree).coeff (k + 1)) ∧ (∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < (p.erase p.natDegree).coeff i → 0 < (p.erase p.natDegree).coeff k → 0 < (p.erase p.natDegree).coeff j) := by
  constructor
  · intro k
    by_cases hk2 : k + 2 < p.natDegree
    · have hk1 : k + 1 < p.natDegree := Nat.lt_of_succ_lt hk2
      have hk0 : k < p.natDegree := Nat.lt_of_succ_lt hk1
      simp only [Polynomial.coeff_erase, if_neg (ne_of_lt hk2), if_neg (ne_of_lt hk1), if_neg (ne_of_lt hk0)]
      exact hlc k
    · have hge : p.natDegree ≤ k + 2 := not_lt.mp hk2
      rw [polynomial_log_concave_erase_top_coeff_ge p hge, mul_zero]
      exact Nat.zero_le _
  · intro i j k hij hjk hi hk
    have hk_lt : k < p.natDegree := by
      by_contra h
      have hge : p.natDegree ≤ k := not_lt.mp h
      have hz := polynomial_log_concave_erase_top_coeff_ge p hge
      rw [hz] at hk
      exact Nat.lt_irrefl 0 hk
    have hj_lt : j < p.natDegree := lt_of_le_of_lt hjk hk_lt
    have hi_lt : i < p.natDegree := lt_of_le_of_lt (hij.trans hjk) hk_lt
    rw [Polynomial.coeff_erase, if_neg (ne_of_lt hi_lt)] at hi
    rw [Polynomial.coeff_erase, if_neg (ne_of_lt hk_lt)] at hk
    rw [Polynomial.coeff_erase, if_neg (ne_of_lt hj_lt)]
    exact hint i j k hij hjk hi hk
