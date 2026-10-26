import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianTwoPrimeDivisorEncoding
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_two_prime_factor_pair_encoding

Topic: combinatorics   Node: 3ba7576012e1

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

A positive factor pair of q^s times p^t has complementary q exponents summing to s and p exponents summing to t.
-/

theorem mondrian_two_prime_factor_pair_encoding (p q t s x y : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hx : 0 < x) (hy : 0 < y) (hxy : x * y = q ^ s * p ^ t) :
    ∃ b c, b + c = s ∧ x = q ^ b * p ^ (x.factorization p) ∧
      y = q ^ c * p ^ (y.factorization p) ∧ x.factorization p + y.factorization p = t := by
  obtain ⟨b, hb, hxb⟩ := mondrian_two_prime_divisor_encoding p q t s x hp hq hpq ⟨y, hxy.symm⟩
  obtain ⟨c, hc, hyc⟩ := mondrian_two_prime_divisor_encoding p q t s y hp hq hpq ⟨x, by nlinarith [hxy]⟩
  have hnot : ¬ p ∣ q := by
    intro hh
    rcases (Nat.dvd_prime hq).mp hh with hh | hh
    · exact hp.ne_one hh
    · exact hpq hh
  have hnot' : ¬ q ∣ p := by
    intro hh
    rcases (Nat.dvd_prime hp).mp hh with hh | hh
    · exact hq.ne_one hh
    · exact hpq hh.symm
  have hvp := congrArg (fun z : ℕ => z.factorization p) hxy
  have hvq := congrArg (fun z : ℕ => z.factorization q) hxy
  have hv : x.factorization p + y.factorization p = t := by
    simpa [Nat.factorization_mul (by omega : x ≠ 0) (by omega : y ≠ 0),
      Nat.factorization_mul (pow_ne_zero s hq.ne_zero) (pow_ne_zero t hp.ne_zero),
      Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnot,
      hp.factorization_self] using hvp
  have hxq : x.factorization q = b := by
    rw [hxb, Nat.factorization_mul (pow_ne_zero b hq.ne_zero)
      (pow_ne_zero (x.factorization p) hp.ne_zero)]
    simp [Nat.factorization_pow, hq.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hnot']
  have hyq : y.factorization q = c := by
    rw [hyc, Nat.factorization_mul (pow_ne_zero c hq.ne_zero)
      (pow_ne_zero (y.factorization p) hp.ne_zero)]
    simp [Nat.factorization_pow, hq.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hnot']
  have hbc : b + c = s := by
    simpa [Nat.factorization_mul (by omega : x ≠ 0) (by omega : y ≠ 0),
      Nat.factorization_mul (pow_ne_zero s hq.ne_zero) (pow_ne_zero t hp.ne_zero),
      Nat.factorization_pow, hq.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hnot', hxq, hyq] using hvq
  exact ⟨b, c, hbc, hxb, hyc, hv⟩
