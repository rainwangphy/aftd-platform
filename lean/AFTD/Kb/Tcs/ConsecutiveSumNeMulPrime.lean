import AFTD.Prelude
import AFTD.Kb.Tcs.ConsecutiveSumNeMulPrimeOfTwoMulLt

/-!
# consecutive_sum_ne_mul_prime

Topic: combinatorics   Node: 4209b740a6aa

Provenance: formalization of a published result. Source: arXiv:2610.08889 (Consecutive Cycle Sums), Lemma 2 (2an − T_{2a−1} < ap written as 2an < ap + a(2a − 1)); proved here from the stronger consecutive_sum_ne_mul_prime_of_two_mul_lt, which drops that hypothesis.

Let a ≥ 1 and p a prime with p > 2n and 2an − T_{2a−1} < ap, where T_m = m(m+1)/2. Then a·p is not a sum of consecutive integers from {1, …, n} (it is not a standard arc sum of the n-cycle).
-/

theorem consecutive_sum_ne_mul_prime (n a p i j : ℕ) (hp : p.Prime) (hpn : 2 * n < p)
    (ha : 0 < a) (hap : 2 * a * n < a * p + a * (2 * a - 1)) (hi : 1 ≤ i) (hij : i ≤ j)
    (hjn : j ≤ n) :
    ∑ x ∈ Finset.Icc i j, x ≠ a * p :=
  consecutive_sum_ne_mul_prime_of_two_mul_lt n a p i j hp hpn ha hi hij hjn
