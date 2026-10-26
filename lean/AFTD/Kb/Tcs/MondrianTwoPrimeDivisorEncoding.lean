import AFTD.Prelude

/-!
# mondrian_two_prime_divisor_encoding

Topic: combinatorics   Node: eeef542e17e7

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

Every divisor x of q^s times p^t, for distinct primes p and q, is q^b times p to the p-adic exponent of x, with b at most s.
-/

theorem mondrian_two_prime_divisor_encoding (p q t s x : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hx : x ∣ q ^ s * p ^ t) :
    ∃ b ≤ s, x = q ^ b * p ^ (x.factorization p) := by
  have hnot : ¬ p ∣ q := by
    intro hh
    rcases (Nat.dvd_prime hq).mp hh with hh | hh
    · exact hp.ne_one hh
    · exact hpq hh
  have hc := Nat.ordCompl_dvd_ordCompl_of_dvd hx p
  have he : (q ^ s * p ^ t) / p ^ ((q ^ s * p ^ t).factorization p) = q ^ s := by
    rw [Nat.mul_comm, Nat.ordCompl_pow_mul_of_not_dvd t hp (fun hh => hnot (hp.dvd_of_dvd_pow hh))]
  rw [he] at hc
  obtain ⟨b, hb, hxb⟩ := (Nat.dvd_prime_pow hq).mp hc
  refine ⟨b, hb, ?_⟩
  have hr := Nat.ordProj_mul_ordCompl_eq_self x p
  change p ^ (x.factorization p) * (x / p ^ (x.factorization p)) = x at hr
  rw [hxb] at hr
  simpa only [Nat.mul_comm] using hr.symm
