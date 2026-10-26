import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPrimeLogGap
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_prime_square_cofactor_side_bound

Topic: combinatorics   Node: 77c6e42413a1

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

A side q^2 times p^a fitting in a q times p^e square satisfies a plus floor(log_p(q)) plus one at most e, for distinct primes.
-/

theorem mondrian_prime_square_cofactor_side_bound (p q e a : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) (h : q ^ 2 * p ^ a ≤ q * p ^ e) :
    a + Nat.log p q + 1 ≤ e := by
  have hc : q * p ^ a ≤ p ^ e := by nlinarith [hq.pos]
  have hh : p ^ (Nat.log p q + a) < p ^ e := by
    rw [pow_add]
    exact (Nat.mul_lt_mul_of_pos_right (mondrian_prime_log_gap p q hp hq hpq).1
      (pow_pos hp.pos a)).trans_le hc
  have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hh
  omega
