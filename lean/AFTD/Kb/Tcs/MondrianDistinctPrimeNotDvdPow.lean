import AFTD.Prelude

/-!
# mondrian_distinct_prime_not_dvd_pow

Topic: combinatorics   Node: 73029fa09789

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

A prime q distinct from p does not divide any power of p.
-/

theorem mondrian_distinct_prime_not_dvd_pow (p q a : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) : ¬ q ∣ p ^ a := by
  intro hh
  have := (Nat.dvd_prime hp).mp (hq.dvd_of_dvd_pow hh)
  rcases this with h | h
  · exact hq.ne_one h
  · exact hpq h.symm
