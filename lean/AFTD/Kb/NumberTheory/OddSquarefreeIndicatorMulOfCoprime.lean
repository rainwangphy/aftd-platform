import AFTD.Prelude
import AFTD.Kb.NumberTheory.OddSquarefreeIndicator

/-!
# odd_squarefree_indicator_mul_of_coprime

Topic: elementary_number_theory   Node: afd16209f6cb

Provenance: helper lemma. arXiv:2611.05898, An Asymptotic for E. P. Stein Numbers, Proposition 4.2

For any positive integers $m$ and $n$ that are coprime, the odd square-free indicator satisfies $\mu^*(m n) = \mu^*(m) \mu^*(n)$.
-/

lemma odd_squarefree_indicator_mul_of_coprime_prime_sq_dvd_mul_iff
    {m n p : ℕ} (hp : Nat.Prime p) (hcop : m.Coprime n) :
    p ^ 2 ∣ m * n ↔ p ^ 2 ∣ m ∨ p ^ 2 ∣ n := by
  constructor
  · intro h
    have hp_dvd_sq : p ∣ p ^ 2 := dvd_pow_self p (by decide)
    have hp_dvd_mn : p ∣ m * n := dvd_trans hp_dvd_sq h
    rcases hp.dvd_mul.mp hp_dvd_mn with hpm | hpn
    · left
      have hpn_not : ¬ p ∣ n := by
        intro hpn
        have : p ∣ m.gcd n := Nat.dvd_gcd hpm hpn
        rw [hcop.gcd_eq_one] at this
        exact hp.not_dvd_one this
      have hcop_pn : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpn_not
      have hcop_p2n : (p ^ 2).Coprime n := hcop_pn.pow_left 2
      exact hcop_p2n.dvd_of_dvd_mul_right h
    · right
      have hpm_not : ¬ p ∣ m := by
        intro hpm
        have : p ∣ m.gcd n := Nat.dvd_gcd hpm hpn
        rw [hcop.gcd_eq_one] at this
        exact hp.not_dvd_one this
      have hcop_pm : p.Coprime m := hp.coprime_iff_not_dvd.mpr hpm_not
      have hcop_p2m : (p ^ 2).Coprime m := hcop_pm.pow_left 2
      exact hcop_p2m.dvd_of_dvd_mul_left h
  · rintro (hm | hn)
    · exact dvd_mul_of_dvd_left hm n
    · exact dvd_mul_of_dvd_right hn m

/-- The odd square-free indicator is multiplicative on positive coprime integers. -/
theorem odd_squarefree_indicator_mul_of_coprime (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) :
    odd_squarefree_indicator (m * n) = odd_squarefree_indicator m * odd_squarefree_indicator n := by
  have hiff : (∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ m * n)) ↔
      (∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ m)) ∧
      (∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ n)) := by
    constructor
    · intro h
      constructor
      · intro p hp hp2 hp_sq
        exact h p hp hp2 ((odd_squarefree_indicator_mul_of_coprime_prime_sq_dvd_mul_iff hp hcop).mpr (Or.inl hp_sq))
      · intro p hp hp2 hp_sq
        exact h p hp hp2 ((odd_squarefree_indicator_mul_of_coprime_prime_sq_dvd_mul_iff hp hcop).mpr (Or.inr hp_sq))
    · rintro ⟨hm_cond, hn_cond⟩ p hp hp2 hp_sq
      rw [odd_squarefree_indicator_mul_of_coprime_prime_sq_dvd_mul_iff hp hcop] at hp_sq
      rcases hp_sq with hpm | hpn
      · exact hm_cond p hp hp2 hpm
      · exact hn_cond p hp hp2 hpn
  unfold odd_squarefree_indicator
  by_cases hm_cond : ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ m)
  · by_cases hn_cond : ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ n)
    · have hmn : ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ m * n) := hiff.mpr ⟨hm_cond, hn_cond⟩
      rw [if_pos hmn, if_pos hm_cond, if_pos hn_cond, mul_one]
    · have hmn : ¬ ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ m * n) := fun h => hn_cond (hiff.mp h).2
      rw [if_neg hmn, if_neg hn_cond, mul_zero]
  · have hmn : ¬ ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ¬ (p ^ 2 ∣ m * n) := fun h => hm_cond (hiff.mp h).1
    rw [if_neg hmn, if_neg hm_cond, zero_mul]
