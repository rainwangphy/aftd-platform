import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianTwoPrimeFactorPairEncoding

/-!
# mondrian_prime_free_factor_pair_encoding

Topic: combinatorics   Node: e70fede98d1f

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

In a positive factor pair of q^s times p^t whose first side is indivisible by q, that side is a pure p-power and the other side contains q^s.
-/

theorem mondrian_prime_free_factor_pair_encoding (p q t s x y : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = q ^ s * p ^ t) (hfree : ¬ q ∣ x) :
    x = p ^ x.factorization p ∧ y = q ^ s * p ^ y.factorization p ∧
      x.factorization p + y.factorization p = t := by
  obtain ⟨b, c, hbc, hxb, hyc, hv⟩ := mondrian_two_prime_factor_pair_encoding p q t s x y hp hq hpq hx hy hxy
  have hb : b = 0 := by
    by_contra hh
    apply hfree
    rw [hxb]
    exact dvd_mul_of_dvd_left (dvd_pow_self q hh) _
  have hc : c = s := by omega
  simpa [hb, hc] using And.intro hxb (And.intro hyc hv)
