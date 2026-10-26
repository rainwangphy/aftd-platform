import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_twice_exponent_lt_prime_power

Topic: combinatorics   Node: 106162a9cf8b

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

For p at least two and r at least three, p^r is greater than twice r.
-/

theorem mondrian_twice_exponent_lt_prime_power (p r : ℕ) (hp : 2 ≤ p) (hr : 3 ≤ r) : 2 * r < p ^ r := by
  have hh : ∀ r ≥ 3, 2 * r < 2 ^ r := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ r hr ih => rw [pow_succ]; nlinarith
  exact (hh r hr).trans_le (Nat.pow_le_pow_left hp r)
