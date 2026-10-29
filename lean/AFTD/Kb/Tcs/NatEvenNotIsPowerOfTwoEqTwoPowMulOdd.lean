import AFTD.Prelude

/-!
# nat_even_not_isPowerOfTwo_eq_two_pow_mul_odd

Topic: combinatorics   Node: 6ec346405b31

Provenance: helper lemma. step towards harborth_bound_equality_rank_three

Every even integer n ≥ 6 that is not a power of 2 factors uniquely as 2^a * m with a ≥ 1, m ≥ 3, and m odd.
-/

/-- Every even integer n ≥ 6 that is not a power of 2 can be factored as 2^a * m with a ≥ 1, m ≥ 3, and m odd. -/
theorem nat_even_not_isPowerOfTwo_eq_two_pow_mul_odd (n : ℕ) (hn : 6 ≤ n) (heven : Even n) (hpow : ¬ n.isPowerOfTwo) :
    ∃ (a : ℕ) (m : ℕ), 1 ≤ a ∧ 3 ≤ m ∧ Odd m ∧ n = 2 ^ a * m := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨a, m, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  refine ⟨a, m, ?_, ?_, hodd, rfl⟩
  · by_contra ha
    have ha0 : a = 0 := by omega
    subst ha0
    simp only [pow_zero, one_mul] at heven
    rcases hodd with ⟨k, rfl⟩
    rcases heven with ⟨j, hj⟩
    omega
  · by_contra hm
    have hm1 : m = 1 := by
      rcases hodd with ⟨k, rfl⟩
      omega
    subst hm1
    exact hpow ⟨a, by ring⟩
