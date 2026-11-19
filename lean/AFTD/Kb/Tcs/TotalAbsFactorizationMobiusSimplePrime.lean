import AFTD.Prelude
import AFTD.Kb.Tcs.TotalAbsFactorizationMobius
import AFTD.Kb.Tcs.OrderedFactorizationCount
import AFTD.Kb.Tcs.TotalAbsFactorizationMobiusEqSumDivisors
import AFTD.Kb.Tcs.OrderedFactorizationCountEqSumProperDivisors

/-!
# total_abs_factorization_mobius_simple_prime

Topic: combinatorics   Node: c94e085b3bbf

Provenance: formalization of a published result. Source: arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), Corollary 7

Corollary 7 of arXiv:2611.18194. Let n = mq where q is a prime not dividing m and m > 1. Let a(n) = totalAbsFactorizationMobius n = Σ_x |μ(x, n)|, the sum over all factorizations x of n (multisets of integers greater than 1 with product n) of the absolute value of the Möbius function μ(x, n) = factorizationMobiusToTop n x of the poset of factorizations of n ordered by refinement. Let H(m) = orderedFactorizationCount m be the number of ordered factorizations of m (finite sequences of integers greater than 1 with product m; H(1) = 1). Then a(n) = 2 H(m).
-/

theorem total_abs_factorization_mobius_simple_prime
    (m q : ℕ) (hq : q.Prime) (hqm : ¬ q ∣ m) (hm : 1 < m) :
    totalAbsFactorizationMobius (m * q) = 2 * orderedFactorizationCount m := by
  have h1 := total_abs_factorization_mobius_eq_sum_divisors m q hq hqm (by omega)
  have h2 := orderedFactorizationCount_eq_sum_properDivisors m hm
  rw [h1, Nat.sum_div_divisors]
  rw [← Nat.cons_self_properDivisors (by omega : m ≠ 0), Finset.sum_cons]
  rw [← h2]
  ring
